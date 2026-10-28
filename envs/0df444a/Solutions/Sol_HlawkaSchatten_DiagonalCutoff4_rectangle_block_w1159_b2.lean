-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:25.779815+00:00
-- url     : https://prove2.me/submissions/78b9a59d-d7bf-4726-91f0-d18bc486179b

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
theorem support_rectangle_w1159_s6_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158753859/10000000000 : ℝ)*x 0 + (1078608469/2000000000 : ℝ)*x 1 + (1316428219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158753859/10000000000 : ℝ)^261 ≤ (6559543847977/50000000000000 : ℝ)^197 := by
    have hnat : (2158753859 : ℕ)^261*50000000000000^197 ≤ 6559543847977^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158753859 10000000000 6559543847977 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078608469/2000000000 : ℝ)^261 ≤ (22063980281629/50000000000000 : ℝ)^197 := by
    have hnat : (1078608469 : ℕ)^261*50000000000000^197 ≤ 22063980281629^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078608469 2000000000 22063980281629 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316428219/2500000000 : ℝ)^261 ≤ (42752951725877/100000000000000 : ℝ)^197 := by
    have hnat : (1316428219 : ℕ)^261*100000000000000^197 ≤ 42752951725877^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316428219 2500000000 42752951725877 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158753859/10000000000 : ℝ), (1078608469/2000000000 : ℝ), (1316428219/2500000000 : ℝ)] ![(6559543847977/50000000000000 : ℝ), (22063980281629/50000000000000 : ℝ), (42752951725877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158753859/10000000000 : ℝ)|^261 ≤ (6559543847977/50000000000000 : ℝ)^197
        have hw : |(-2158753859/10000000000 : ℝ)|=(2158753859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078608469/2000000000 : ℝ)|^261 ≤ (22063980281629/50000000000000 : ℝ)^197
        have hw : |(1078608469/2000000000 : ℝ)|=(1078608469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316428219/2500000000 : ℝ)|^261 ≤ (42752951725877/100000000000000 : ℝ)^197
        have hw : |(1316428219/2500000000 : ℝ)|=(1316428219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (334048301/625000000 : ℝ)*x 0 + (-1111669071/5000000000 : ℝ)*x 1 + (5265713003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334048301/625000000 : ℝ)^261 ≤ (43605451020431/100000000000000 : ℝ)^197 := by
    have hnat : (334048301 : ℕ)^261*100000000000000^197 ≤ 43605451020431^197*625000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334048301 625000000 43605451020431 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111669071/5000000000 : ℝ)^261 ≤ (13641595865071/100000000000000 : ℝ)^197 := by
    have hnat : (1111669071 : ℕ)^261*100000000000000^197 ≤ 13641595865071^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111669071 5000000000 13641595865071 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265713003/10000000000 : ℝ)^261 ≤ (42752953091991/100000000000000 : ℝ)^197 := by
    have hnat : (5265713003 : ℕ)^261*100000000000000^197 ≤ 42752953091991^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265713003 10000000000 42752953091991 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334048301/625000000 : ℝ), (-1111669071/5000000000 : ℝ), (5265713003/10000000000 : ℝ)] ![(43605451020431/100000000000000 : ℝ), (13641595865071/100000000000000 : ℝ), (42752953091991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334048301/625000000 : ℝ)|^261 ≤ (43605451020431/100000000000000 : ℝ)^197
        have hw : |(334048301/625000000 : ℝ)|=(334048301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111669071/5000000000 : ℝ)|^261 ≤ (13641595865071/100000000000000 : ℝ)^197
        have hw : |(-1111669071/5000000000 : ℝ)|=(1111669071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265713003/10000000000 : ℝ)|^261 ≤ (42752953091991/100000000000000 : ℝ)^197
        have hw : |(5265713003/10000000000 : ℝ)|=(5265713003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (668096643/1250000000 : ℝ)*x 0 + (32910703/62500000 : ℝ)*x 1 + (-2223338399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668096643/1250000000 : ℝ)^261 ≤ (8721090913157/20000000000000 : ℝ)^197 := by
    have hnat : (668096643 : ℕ)^261*20000000000000^197 ≤ 8721090913157^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668096643 1250000000 8721090913157 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32910703/62500000 : ℝ)^261 ≤ (42752947466183/100000000000000 : ℝ)^197 := by
    have hnat : (32910703 : ℕ)^261*100000000000000^197 ≤ 42752947466183^197*62500000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32910703 62500000 42752947466183 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223338399/10000000000 : ℝ)^261 ≤ (13641597954209/100000000000000 : ℝ)^197 := by
    have hnat : (2223338399 : ℕ)^261*100000000000000^197 ≤ 13641597954209^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223338399 10000000000 13641597954209 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668096643/1250000000 : ℝ), (32910703/62500000 : ℝ), (-2223338399/10000000000 : ℝ)] ![(8721090913157/20000000000000 : ℝ), (42752947466183/100000000000000 : ℝ), (13641597954209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668096643/1250000000 : ℝ)|^261 ≤ (8721090913157/20000000000000 : ℝ)^197
        have hw : |(668096643/1250000000 : ℝ)|=(668096643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32910703/62500000 : ℝ)|^261 ≤ (42752947466183/100000000000000 : ℝ)^197
        have hw : |(32910703/62500000 : ℝ)|=(32910703/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223338399/10000000000 : ℝ)|^261 ≤ (13641597954209/100000000000000 : ℝ)^197
        have hw : |(-2223338399/10000000000 : ℝ)|=(2223338399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4362268457/10000000000 : ℝ)*x 0 + (847403991/2000000000 : ℝ)*x 1 + (4491185179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362268457/10000000000 : ℝ)^261 ≤ (33316903965643/100000000000000 : ℝ)^197 := by
    have hnat : (4362268457 : ℕ)^261*100000000000000^197 ≤ 33316903965643^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362268457 10000000000 33316903965643 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847403991/2000000000 : ℝ)^261 ≤ (16027748040967/50000000000000 : ℝ)^197 := by
    have hnat : (847403991 : ℕ)^261*50000000000000^197 ≤ 16027748040967^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847403991 2000000000 16027748040967 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491185179/10000000000 : ℝ)^261 ≤ (6925519988797/20000000000000 : ℝ)^197 := by
    have hnat : (4491185179 : ℕ)^261*20000000000000^197 ≤ 6925519988797^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491185179 10000000000 6925519988797 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362268457/10000000000 : ℝ), (847403991/2000000000 : ℝ), (4491185179/10000000000 : ℝ)] ![(33316903965643/100000000000000 : ℝ), (16027748040967/50000000000000 : ℝ), (6925519988797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362268457/10000000000 : ℝ)|^261 ≤ (33316903965643/100000000000000 : ℝ)^197
        have hw : |(4362268457/10000000000 : ℝ)|=(4362268457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847403991/2000000000 : ℝ)|^261 ≤ (16027748040967/50000000000000 : ℝ)^197
        have hw : |(847403991/2000000000 : ℝ)|=(847403991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491185179/10000000000 : ℝ)|^261 ≤ (6925519988797/20000000000000 : ℝ)^197
        have hw : |(4491185179/10000000000 : ℝ)|=(4491185179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-431751821/2000000000 : ℝ)*x 0 + (5266034159/10000000000 : ℝ)*x 1 + (5392719643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431751821/2000000000 : ℝ)^261 ≤ (1639891241743/12500000000000 : ℝ)^197 := by
    have hnat : (431751821 : ℕ)^261*12500000000000^197 ≤ 1639891241743^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431751821 2000000000 1639891241743 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266034159/10000000000 : ℝ)^261 ≤ (21378203869017/50000000000000 : ℝ)^197 := by
    have hnat : (5266034159 : ℕ)^261*50000000000000^197 ≤ 21378203869017^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266034159 10000000000 21378203869017 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392719643/10000000000 : ℝ)^261 ≤ (44124462306007/100000000000000 : ℝ)^197 := by
    have hnat : (5392719643 : ℕ)^261*100000000000000^197 ≤ 44124462306007^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392719643 10000000000 44124462306007 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431751821/2000000000 : ℝ), (5266034159/10000000000 : ℝ), (5392719643/10000000000 : ℝ)] ![(1639891241743/12500000000000 : ℝ), (21378203869017/50000000000000 : ℝ), (44124462306007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431751821/2000000000 : ℝ)|^261 ≤ (1639891241743/12500000000000 : ℝ)^197
        have hw : |(-431751821/2000000000 : ℝ)|=(431751821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266034159/10000000000 : ℝ)|^261 ≤ (21378203869017/50000000000000 : ℝ)^197
        have hw : |(5266034159/10000000000 : ℝ)|=(5266034159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392719643/10000000000 : ℝ)|^261 ≤ (44124462306007/100000000000000 : ℝ)^197
        have hw : |(5392719643/10000000000 : ℝ)|=(5392719643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312473243/10000000000 : ℝ)*x 0 + (-524082791/2500000000 : ℝ)*x 1 + (539271963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312473243/10000000000 : ℝ)^261 ≤ (21628333939877/50000000000000 : ℝ)^197 := by
    have hnat : (5312473243 : ℕ)^261*50000000000000^197 ≤ 21628333939877^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312473243 10000000000 21628333939877 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524082791/2500000000 : ℝ)^261 ≤ (1261886993967/10000000000000 : ℝ)^197 := by
    have hnat : (524082791 : ℕ)^261*10000000000000^197 ≤ 1261886993967^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524082791 2500000000 1261886993967 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539271963/1000000000 : ℝ)^261 ≤ (22062231082541/50000000000000 : ℝ)^197 := by
    have hnat : (539271963 : ℕ)^261*50000000000000^197 ≤ 22062231082541^197*1000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539271963 1000000000 22062231082541 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312473243/10000000000 : ℝ), (-524082791/2500000000 : ℝ), (539271963/1000000000 : ℝ)] ![(21628333939877/50000000000000 : ℝ), (1261886993967/10000000000000 : ℝ), (22062231082541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312473243/10000000000 : ℝ)|^261 ≤ (21628333939877/50000000000000 : ℝ)^197
        have hw : |(5312473243/10000000000 : ℝ)|=(5312473243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524082791/2500000000 : ℝ)|^261 ≤ (1261886993967/10000000000000 : ℝ)^197
        have hw : |(-524082791/2500000000 : ℝ)|=(524082791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539271963/1000000000 : ℝ)|^261 ≤ (22062231082541/50000000000000 : ℝ)^197
        have hw : |(539271963/1000000000 : ℝ)|=(539271963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (166014789/312500000 : ℝ)*x 0 + (1348179903/2500000000 : ℝ)*x 1 + (-1048165591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166014789/312500000 : ℝ)^261 ≤ (43256667933693/100000000000000 : ℝ)^197 := by
    have hnat : (166014789 : ℕ)^261*100000000000000^197 ≤ 43256667933693^197*312500000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166014789 312500000 43256667933693 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348179903/2500000000 : ℝ)^261 ≤ (22062230984977/50000000000000 : ℝ)^197 := by
    have hnat : (1348179903 : ℕ)^261*50000000000000^197 ≤ 22062230984977^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348179903 2500000000 22062230984977 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048165591/5000000000 : ℝ)^261 ≤ (6309435041611/50000000000000 : ℝ)^197 := by
    have hnat : (1048165591 : ℕ)^261*50000000000000^197 ≤ 6309435041611^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048165591 5000000000 6309435041611 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166014789/312500000 : ℝ), (1348179903/2500000000 : ℝ), (-1048165591/5000000000 : ℝ)] ![(43256667933693/100000000000000 : ℝ), (22062230984977/50000000000000 : ℝ), (6309435041611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166014789/312500000 : ℝ)|^261 ≤ (43256667933693/100000000000000 : ℝ)^197
        have hw : |(166014789/312500000 : ℝ)|=(166014789/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348179903/2500000000 : ℝ)|^261 ≤ (22062230984977/50000000000000 : ℝ)^197
        have hw : |(1348179903/2500000000 : ℝ)|=(1348179903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048165591/5000000000 : ℝ)|^261 ≤ (6309435041611/50000000000000 : ℝ)^197
        have hw : |(-1048165591/5000000000 : ℝ)|=(1048165591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s6_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4362277873/10000000000 : ℝ)*x 0 + (898108601/2000000000 : ℝ)*x 1 + (211883243/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362277873/10000000000 : ℝ)^261 ≤ (4164624905469/12500000000000 : ℝ)^197 := by
    have hnat : (4362277873 : ℕ)^261*12500000000000^197 ≤ 4164624905469^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362277873 10000000000 4164624905469 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898108601/2000000000 : ℝ)^261 ≤ (17310520164561/50000000000000 : ℝ)^197 := by
    have hnat : (898108601 : ℕ)^261*50000000000000^197 ≤ 17310520164561^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898108601 2000000000 17310520164561 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211883243/500000000 : ℝ)^261 ≤ (32061960400567/100000000000000 : ℝ)^197 := by
    have hnat : (211883243 : ℕ)^261*100000000000000^197 ≤ 32061960400567^197*500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211883243 500000000 32061960400567 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362277873/10000000000 : ℝ), (898108601/2000000000 : ℝ), (211883243/500000000 : ℝ)] ![(4164624905469/12500000000000 : ℝ), (17310520164561/50000000000000 : ℝ), (32061960400567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362277873/10000000000 : ℝ)|^261 ≤ (4164624905469/12500000000000 : ℝ)^197
        have hw : |(4362277873/10000000000 : ℝ)|=(4362277873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898108601/2000000000 : ℝ)|^261 ≤ (17310520164561/50000000000000 : ℝ)^197
        have hw : |(898108601/2000000000 : ℝ)|=(898108601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211883243/500000000 : ℝ)|^261 ≤ (32061960400567/100000000000000 : ℝ)^197
        have hw : |(211883243/500000000 : ℝ)|=(211883243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11369/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (567/5000 : ℝ) ^ (8351/2048 : ℝ) ≤ (2793093495885829/20000000000000000000 : ℝ) := by
    have hpowers : (567/5000 : ℝ)^8351 ≤ (2793093495885829/20000000000000000000 : ℝ)^2048 := by
      have hnat : (567 : ℕ)^8351*20000000000000000000^2048 ≤ 2793093495885829^2048*5000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        567 5000 2793093495885829 20000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (567/5000 : ℝ)) (X := (2793093495885829/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (881/6250 : ℝ) ^ (8351/2048 : ℝ) ≤ (2119347532892131/6250000000000000000 : ℝ) := by
    have hpowers : (881/6250 : ℝ)^8351 ≤ (2119347532892131/6250000000000000000 : ℝ)^2048 := by
      have hnat : (881 : ℕ)^8351*6250000000000000000^2048 ≤ 2119347532892131^2048*6250^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        881 6250 2119347532892131 6250000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (881/6250 : ℝ)) (X := (2119347532892131/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002793093495885829/10000000000000000000 : ℝ) ≤ (2500171226578561/2500000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (10002793093495885829/10000000000000000000 : ℝ)^2048 ≤ (2500171226578561/2500000000000000 : ℝ)^8351 := by
      have hnat : (10002793093495885829 : ℕ)^2048*2500000000000000^8351 ≤ 2500171226578561^8351*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002793093495885829 10000000000000000000 2500171226578561 2500000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500171226578561/2500000000000000 : ℝ)) (X := (10002793093495885829/10000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047875028005703241/100000000000000000000 : ℝ) ≤ (10001173875558589/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (100047875028005703241/100000000000000000000 : ℝ)^2048 ≤ (10001173875558589/10000000000000000 : ℝ)^8351 := by
      have hnat : (100047875028005703241 : ℕ)^2048*10000000000000000^8351 ≤ 10001173875558589^8351*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047875028005703241 100000000000000000000 10001173875558589 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001173875558589/10000000000000000 : ℝ)) (X := (100047875028005703241/100000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127119347532892131/3125000000000000000 : ℝ) ≤ (5000831422401467/5000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (3127119347532892131/3125000000000000000 : ℝ)^2048 ≤ (5000831422401467/5000000000000000 : ℝ)^8351 := by
      have hnat : (3127119347532892131 : ℕ)^2048*5000000000000000^8351 ≤ 5000831422401467^8351*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127119347532892131 3125000000000000000 5000831422401467 5000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000831422401467/5000000000000000 : ℝ)) (X := (3127119347532892131/3125000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2793093495885829/20000000000000000000 : ℝ) ≤ ((3443849722417538983/3445000000000000000 : ℝ)+2*(97793848869/55120000000000 : ℝ)*(567/5000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (3443849722417538983/3445000000000000000 : ℝ)+2*(97793848869/55120000000000 : ℝ)*(567/5000 : ℝ)=(2500171226578561/2500000000000000 : ℝ) by norm_num, show 1+2*(2793093495885829/20000000000000000000 : ℝ)=(10002793093495885829/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2119347532892131/6250000000000000000 : ℝ)+(2793093495885829/20000000000000000000 : ℝ) ≤ ((3443849722417538983/3445000000000000000 : ℝ)+(97793848869/55120000000000 : ℝ)*((881/6250 : ℝ)+(567/5000 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (3443849722417538983/3445000000000000000 : ℝ)+(97793848869/55120000000000 : ℝ)*((881/6250 : ℝ)+(567/5000 : ℝ))=(10001173875558589/10000000000000000 : ℝ) by norm_num, show 1+(2119347532892131/6250000000000000000 : ℝ)+(2793093495885829/20000000000000000000 : ℝ)=(100047875028005703241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2119347532892131/6250000000000000000 : ℝ) ≤ ((3443849722417538983/3445000000000000000 : ℝ)+2*(97793848869/55120000000000 : ℝ)*(881/6250 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (3443849722417538983/3445000000000000000 : ℝ)+2*(97793848869/55120000000000 : ℝ)*(881/6250 : ℝ)=(5000831422401467/5000000000000000 : ℝ) by norm_num, show 1+2*(2119347532892131/6250000000000000000 : ℝ)=(3127119347532892131/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3443849722417538983/3445000000000000000 : ℝ)*(X 1 0+X 2 0)+(97793848869/55120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (3443849722417538983/3445000000000000000 : ℝ)) (alpha := (97793848869/55120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3443849722417538983/3445000000000000000 : ℝ)*(X 0 1+X 2 1)+(97793848869/55120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (3443849722417538983/3445000000000000000 : ℝ)) (alpha := (97793848869/55120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3443849722417538983/3445000000000000000 : ℝ)*(X 0 2+X 1 2)+(97793848869/55120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (3443849722417538983/3445000000000000000 : ℝ)) (alpha := (97793848869/55120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158753859/10000000000 : ℝ)*X 0 0+(1078608469/2000000000 : ℝ)*X 0 1+(1316428219/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334048301/625000000 : ℝ)*X 1 0+(-1111669071/5000000000 : ℝ)*X 1 1+(5265713003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668096643/1250000000 : ℝ)*X 2 0+(32910703/62500000 : ℝ)*X 2 1+(-2223338399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362268457/10000000000 : ℝ)*X 0 0+(847403991/2000000000 : ℝ)*X 0 1+(4491185179/10000000000 : ℝ)*X 0 2+(4362268457/10000000000 : ℝ)*X 1 0+(847403991/2000000000 : ℝ)*X 1 1+(4491185179/10000000000 : ℝ)*X 1 2+(4362268457/10000000000 : ℝ)*X 2 0+(847403991/2000000000 : ℝ)*X 2 1+(4491185179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431751821/2000000000 : ℝ)*X 0 0+(5266034159/10000000000 : ℝ)*X 0 1+(5392719643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312473243/10000000000 : ℝ)*X 1 0+(-524082791/2500000000 : ℝ)*X 1 1+(539271963/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166014789/312500000 : ℝ)*X 2 0+(1348179903/2500000000 : ℝ)*X 2 1+(-1048165591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362277873/10000000000 : ℝ)*X 0 0+(898108601/2000000000 : ℝ)*X 0 1+(211883243/500000000 : ℝ)*X 0 2+(4362277873/10000000000 : ℝ)*X 1 0+(898108601/2000000000 : ℝ)*X 1 1+(211883243/500000000 : ℝ)*X 1 2+(4362277873/10000000000 : ℝ)*X 2 0+(898108601/2000000000 : ℝ)*X 2 1+(211883243/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (896567328919521617364891327/172250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24046109/50000000000000 : ℝ)*(base23) + (307103057/100000000000000 : ℝ)*(lower2) + (24935297/25000000000000 : ℝ)*(upper3) + (68427093/50000000000000 : ℝ)*(lower4) + (12416247/100000000000000 : ℝ)*(upper5) + (5894053947873523/100000000000000 : ℝ)*(major0) + (5894053947873523/100000000000000 : ℝ)*(major1) + (5894053947873523/100000000000000 : ℝ)*(major2) + (7853636910119087/100000000000000 : ℝ)*(sp0) + (7853636910119087/100000000000000 : ℝ)*(sp1) + (3926808888224293/50000000000000 : ℝ)*(sp2) + (393445692557923/10000000000000 : ℝ)*(sp3) + (19085578283/100000000000000 : ℝ)*(sp6) + (13886547539/100000000000000 : ℝ)*(sp7) + (245904425757923/6250000000000 : ℝ)*(f.failure) + (7853636910119087/100000000000000 : ℝ)*(f.sum) + (143943273228943/2756000000000000000000000000 : ℝ)*base65 + (3922703400996015391/344500000000000000000000000000000 : ℝ)*base68 + (3914262483894984609/344500000000000000000000000000000 : ℝ)*base69 + (212129484056515391/344500000000000000000000000000000 : ℝ)*base72 + (459515927709/2756000000000000000000000000 : ℝ)*base74 + (1301187249014484609/344500000000000000000000000000000 : ℝ)*base75 + (2856686688488515391/344500000000000000000000000000000 : ℝ)*base78 + (2989177459810515391/344500000000000000000000000000000 : ℝ)*base80 + (11012597548647/2756000000000000000000000000 : ℝ)*base81 + (4468039/625000000000000000000 : ℝ)*base90 + (4468039/625000000000000000000 : ℝ)*base92 + (4468039/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108721431453727043941890531/13250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1544830397/100000000000000 : ℝ)*(base19) + (1653062793/100000000000000 : ℝ)*(base23) + (40115247/25000000000000 : ℝ)*(upper3) + (50169211/100000000000000 : ℝ)*(lower4) + (174264927/100000000000000 : ℝ)*(upper5) + (5924018428290253/100000000000000 : ℝ)*(major0) + (5924018428290253/100000000000000 : ℝ)*(major1) + (5924018428290253/100000000000000 : ℝ)*(major2) + (21299048233/50000000000000 : ℝ)*(sp1) + (5455598557/12500000000000 : ℝ)*(sp2) + (3946781757669109/50000000000000 : ℝ)*(sp4) + (1578703874482271/20000000000000 : ℝ)*(sp5) + (986689777185871/12500000000000 : ℝ)*(sp6) + (123577283366539/3125000000000 : ℝ)*(sp7) + (123577283366539/3125000000000 : ℝ)*(f.failure) + (3946781757669109/50000000000000 : ℝ)*(f.sum) + (12794862457673/2756000000000000000000000000 : ℝ)*base65 + (920032700793495199/344500000000000000000000000000000 : ℝ)*base67 + (2699670591629495199/344500000000000000000000000000000 : ℝ)*base69 + (2307343459919995199/344500000000000000000000000000000 : ℝ)*base71 + (7681617379231/2756000000000000000000000000 : ℝ)*base74 + (266725849963504801/344500000000000000000000000000000 : ℝ)*base76 + (389855628891504801/344500000000000000000000000000000 : ℝ)*base78 + (1960092451380495199/344500000000000000000000000000000 : ℝ)*base79 + (8807722680897/2756000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1105273/312500000000000000000 : ℝ)*base89 + (1105273/312500000000000000000 : ℝ)*base91 + (1105273/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1159_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1159_s7_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-53969469/250000000 : ℝ)*x 0 + (5392746171/10000000000 : ℝ)*x 1 + (1053198543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53969469/250000000 : ℝ)^261 ≤ (3279822046451/25000000000000 : ℝ)^197 := by
    have hnat : (53969469 : ℕ)^261*25000000000000^197 ≤ 3279822046451^197*250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53969469 250000000 3279822046451 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392746171/10000000000 : ℝ)^261 ≤ (44124749880737/100000000000000 : ℝ)^197 := by
    have hnat : (5392746171 : ℕ)^261*100000000000000^197 ≤ 44124749880737^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392746171 10000000000 44124749880737 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053198543/2000000000 : ℝ)^261 ≤ (10688990481207/25000000000000 : ℝ)^197 := by
    have hnat : (1053198543 : ℕ)^261*25000000000000^197 ≤ 10688990481207^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053198543 2000000000 10688990481207 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53969469/250000000 : ℝ), (5392746171/10000000000 : ℝ), (1053198543/2000000000 : ℝ)] ![(3279822046451/25000000000000 : ℝ), (44124749880737/100000000000000 : ℝ), (10688990481207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53969469/250000000 : ℝ)|^261 ≤ (3279822046451/25000000000000 : ℝ)^197
        have hw : |(-53969469/250000000 : ℝ)|=(53969469/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392746171/10000000000 : ℝ)|^261 ≤ (44124749880737/100000000000000 : ℝ)^197
        have hw : |(5392746171/10000000000 : ℝ)|=(5392746171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053198543/2000000000 : ℝ)|^261 ≤ (10688990481207/25000000000000 : ℝ)^197
        have hw : |(1053198543/2000000000 : ℝ)|=(1053198543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2672349401/5000000000 : ℝ)*x 0 + (-2223066253/10000000000 : ℝ)*x 1 + (2632996419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672349401/5000000000 : ℝ)^261 ≤ (10901162751089/25000000000000 : ℝ)^197 := by
    have hnat : (2672349401 : ℕ)^261*25000000000000^197 ≤ 10901162751089^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672349401 5000000000 10901162751089 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223066253/10000000000 : ℝ)^261 ≤ (6819692869743/50000000000000 : ℝ)^197 := by
    have hnat : (2223066253 : ℕ)^261*50000000000000^197 ≤ 6819692869743^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223066253 10000000000 6819692869743 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632996419/5000000000 : ℝ)^261 ≤ (21377981623969/50000000000000 : ℝ)^197 := by
    have hnat : (2632996419 : ℕ)^261*50000000000000^197 ≤ 21377981623969^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632996419 5000000000 21377981623969 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672349401/5000000000 : ℝ), (-2223066253/10000000000 : ℝ), (2632996419/5000000000 : ℝ)] ![(10901162751089/25000000000000 : ℝ), (6819692869743/50000000000000 : ℝ), (21377981623969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672349401/5000000000 : ℝ)|^261 ≤ (10901162751089/25000000000000 : ℝ)^197
        have hw : |(2672349401/5000000000 : ℝ)|=(2672349401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2223066253/10000000000 : ℝ)|^261 ≤ (6819692869743/50000000000000 : ℝ)^197
        have hw : |(-2223066253/10000000000 : ℝ)|=(2223066253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632996419/5000000000 : ℝ)|^261 ≤ (21377981623969/50000000000000 : ℝ)^197
        have hw : |(2632996419/5000000000 : ℝ)|=(2632996419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (334043681/625000000 : ℝ)*x 0 + (658249101/1250000000 : ℝ)*x 1 + (-1111533083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334043681/625000000 : ℝ)^261 ≤ (43604652020399/100000000000000 : ℝ)^197 := by
    have hnat : (334043681 : ℕ)^261*100000000000000^197 ≤ 43604652020399^197*625000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334043681 625000000 43604652020399 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658249101/1250000000 : ℝ)^261 ≤ (10688990731307/25000000000000 : ℝ)^197 := by
    have hnat : (658249101 : ℕ)^261*25000000000000^197 ≤ 10688990731307^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658249101 1250000000 10688990731307 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111533083/5000000000 : ℝ)^261 ≤ (1704923129037/12500000000000 : ℝ)^197 := by
    have hnat : (1111533083 : ℕ)^261*12500000000000^197 ≤ 1704923129037^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111533083 5000000000 1704923129037 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334043681/625000000 : ℝ), (658249101/1250000000 : ℝ), (-1111533083/5000000000 : ℝ)] ![(43604652020399/100000000000000 : ℝ), (10688990731307/25000000000000 : ℝ), (1704923129037/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334043681/625000000 : ℝ)|^261 ≤ (43604652020399/100000000000000 : ℝ)^197
        have hw : |(334043681/625000000 : ℝ)|=(334043681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658249101/1250000000 : ℝ)|^261 ≤ (10688990731307/25000000000000 : ℝ)^197
        have hw : |(658249101/1250000000 : ℝ)|=(658249101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111533083/5000000000 : ℝ)|^261 ≤ (1704923129037/12500000000000 : ℝ)^197
        have hw : |(-1111533083/5000000000 : ℝ)|=(1111533083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4362282827/10000000000 : ℝ)*x 0 + (847518819/2000000000 : ℝ)*x 1 + (4490607543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362282827/10000000000 : ℝ)^261 ≤ (6663409874409/20000000000000 : ℝ)^197 := by
    have hnat : (4362282827 : ℕ)^261*20000000000000^197 ≤ 6663409874409^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362282827 10000000000 6663409874409 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847518819/2000000000 : ℝ)^261 ≤ (32061251059539/100000000000000 : ℝ)^197 := by
    have hnat : (847518819 : ℕ)^261*100000000000000^197 ≤ 32061251059539^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847518819 2000000000 32061251059539 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490607543/10000000000 : ℝ)^261 ≤ (8655424887917/25000000000000 : ℝ)^197 := by
    have hnat : (4490607543 : ℕ)^261*25000000000000^197 ≤ 8655424887917^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490607543 10000000000 8655424887917 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362282827/10000000000 : ℝ), (847518819/2000000000 : ℝ), (4490607543/10000000000 : ℝ)] ![(6663409874409/20000000000000 : ℝ), (32061251059539/100000000000000 : ℝ), (8655424887917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362282827/10000000000 : ℝ)|^261 ≤ (6663409874409/20000000000000 : ℝ)^197
        have hw : |(4362282827/10000000000 : ℝ)|=(4362282827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847518819/2000000000 : ℝ)|^261 ≤ (32061251059539/100000000000000 : ℝ)^197
        have hw : |(847518819/2000000000 : ℝ)|=(847518819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490607543/10000000000 : ℝ)|^261 ≤ (8655424887917/25000000000000 : ℝ)^197
        have hw : |(4490607543/10000000000 : ℝ)|=(4490607543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079391743/5000000000 : ℝ)*x 0 + (5266311593/10000000000 : ℝ)*x 1 + (5392426231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079391743/5000000000 : ℝ)^261 ≤ (13119326237173/100000000000000 : ℝ)^197 := by
    have hnat : (1079391743 : ℕ)^261*100000000000000^197 ≤ 13119326237173^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079391743 5000000000 13119326237173 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266311593/10000000000 : ℝ)^261 ≤ (21379696062791/50000000000000 : ℝ)^197 := by
    have hnat : (5266311593 : ℕ)^261*50000000000000^197 ≤ 21379696062791^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266311593 10000000000 21379696062791 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392426231/10000000000 : ℝ)^261 ≤ (22060640813297/50000000000000 : ℝ)^197 := by
    have hnat : (5392426231 : ℕ)^261*50000000000000^197 ≤ 22060640813297^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392426231 10000000000 22060640813297 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079391743/5000000000 : ℝ), (5266311593/10000000000 : ℝ), (5392426231/10000000000 : ℝ)] ![(13119326237173/100000000000000 : ℝ), (21379696062791/50000000000000 : ℝ), (22060640813297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079391743/5000000000 : ℝ)|^261 ≤ (13119326237173/100000000000000 : ℝ)^197
        have hw : |(-1079391743/5000000000 : ℝ)|=(1079391743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266311593/10000000000 : ℝ)|^261 ≤ (21379696062791/50000000000000 : ℝ)^197
        have hw : |(5266311593/10000000000 : ℝ)|=(5266311593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392426231/10000000000 : ℝ)|^261 ≤ (22060640813297/50000000000000 : ℝ)^197
        have hw : |(5392426231/10000000000 : ℝ)|=(5392426231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312545043/10000000000 : ℝ)*x 0 + (-1048316389/5000000000 : ℝ)*x 1 + (5392426279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312545043/10000000000 : ℝ)^261 ≤ (8651488488279/20000000000000 : ℝ)^197 := by
    have hnat : (5312545043 : ℕ)^261*20000000000000^197 ≤ 8651488488279^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312545043 10000000000 8651488488279 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048316389/5000000000 : ℝ)^261 ≤ (98603713989/781250000000 : ℝ)^197 := by
    have hnat : (1048316389 : ℕ)^261*781250000000^197 ≤ 98603713989^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048316389 5000000000 98603713989 781250000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392426279/10000000000 : ℝ)^261 ≤ (11030320536731/25000000000000 : ℝ)^197 := by
    have hnat : (5392426279 : ℕ)^261*25000000000000^197 ≤ 11030320536731^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392426279 10000000000 11030320536731 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312545043/10000000000 : ℝ), (-1048316389/5000000000 : ℝ), (5392426279/10000000000 : ℝ)] ![(8651488488279/20000000000000 : ℝ), (98603713989/781250000000 : ℝ), (11030320536731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312545043/10000000000 : ℝ)|^261 ≤ (8651488488279/20000000000000 : ℝ)^197
        have hw : |(5312545043/10000000000 : ℝ)|=(5312545043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048316389/5000000000 : ℝ)|^261 ≤ (98603713989/781250000000 : ℝ)^197
        have hw : |(-1048316389/5000000000 : ℝ)|=(1048316389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392426279/10000000000 : ℝ)|^261 ≤ (11030320536731/25000000000000 : ℝ)^197
        have hw : |(5392426279/10000000000 : ℝ)|=(5392426279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (106250901/200000000 : ℝ)*x 0 + (5392426283/10000000000 : ℝ)*x 1 + (-2096632763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106250901/200000000 : ℝ)^261 ≤ (43257442516909/100000000000000 : ℝ)^197 := by
    have hnat : (106250901 : ℕ)^261*100000000000000^197 ≤ 43257442516909^197*200000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106250901 200000000 43257442516909 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392426283/10000000000 : ℝ)^261 ≤ (8824256438057/20000000000000 : ℝ)^197 := by
    have hnat : (5392426283 : ℕ)^261*20000000000000^197 ≤ 8824256438057^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392426283 10000000000 8824256438057 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096632763/10000000000 : ℝ)^261 ≤ (157765940887/1250000000000 : ℝ)^197 := by
    have hnat : (2096632763 : ℕ)^261*1250000000000^197 ≤ 157765940887^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096632763 10000000000 157765940887 1250000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106250901/200000000 : ℝ), (5392426283/10000000000 : ℝ), (-2096632763/10000000000 : ℝ)] ![(43257442516909/100000000000000 : ℝ), (8824256438057/20000000000000 : ℝ), (157765940887/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106250901/200000000 : ℝ)|^261 ≤ (43257442516909/100000000000000 : ℝ)^197
        have hw : |(106250901/200000000 : ℝ)|=(106250901/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392426283/10000000000 : ℝ)|^261 ≤ (8824256438057/20000000000000 : ℝ)^197
        have hw : |(5392426283/10000000000 : ℝ)|=(5392426283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096632763/10000000000 : ℝ)|^261 ≤ (157765940887/1250000000000 : ℝ)^197
        have hw : |(-2096632763/10000000000 : ℝ)|=(2096632763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s7_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2181146211/5000000000 : ℝ)*x 0 + (897994277/2000000000 : ℝ)*x 1 + (1059558159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181146211/5000000000 : ℝ)^261 ≤ (6663429292303/20000000000000 : ℝ)^197 := by
    have hnat : (2181146211 : ℕ)^261*20000000000000^197 ≤ 6663429292303^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181146211 5000000000 6663429292303 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897994277/2000000000 : ℝ)^261 ≤ (2163450103661/6250000000000 : ℝ)^197 := by
    have hnat : (897994277 : ℕ)^261*6250000000000^197 ≤ 2163450103661^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897994277 2000000000 2163450103661 6250000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059558159/2500000000 : ℝ)^261 ≤ (32067651867669/100000000000000 : ℝ)^197 := by
    have hnat : (1059558159 : ℕ)^261*100000000000000^197 ≤ 32067651867669^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059558159 2500000000 32067651867669 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181146211/5000000000 : ℝ), (897994277/2000000000 : ℝ), (1059558159/2500000000 : ℝ)] ![(6663429292303/20000000000000 : ℝ), (2163450103661/6250000000000 : ℝ), (32067651867669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181146211/5000000000 : ℝ)|^261 ≤ (6663429292303/20000000000000 : ℝ)^197
        have hw : |(2181146211/5000000000 : ℝ)|=(2181146211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897994277/2000000000 : ℝ)|^261 ≤ (2163450103661/6250000000000 : ℝ)^197
        have hw : |(897994277/2000000000 : ℝ)|=(897994277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059558159/2500000000 : ℝ)|^261 ≤ (32067651867669/100000000000000 : ℝ)^197
        have hw : |(1059558159/2500000000 : ℝ)|=(1059558159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11369/100000 : ℝ) ^ (8351/2048 : ℝ) ≤ (2822334189385341/20000000000000000000 : ℝ) := by
    have hpowers : (11369/100000 : ℝ)^8351 ≤ (2822334189385341/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11369 : ℕ)^8351*20000000000000000000^2048 ≤ 2822334189385341^2048*100000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11369 100000 2822334189385341 20000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11369/100000 : ℝ)) (X := (2822334189385341/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (8351/2048 : ℝ) ≤ (33616246044985669/100000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^8351 ≤ (33616246044985669/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7033 : ℕ)^8351*100000000000000000000^2048 ≤ 33616246044985669^2048*50000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 33616246044985669 100000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (33616246044985669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002822334189385341/10000000000000000000 : ℝ) ≤ (312521627368291/312500000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (10002822334189385341/10000000000000000000 : ℝ)^2048 ≤ (312521627368291/312500000000000 : ℝ)^8351 := by
      have hnat : (10002822334189385341 : ℕ)^2048*312500000000000^8351 ≤ 312521627368291^8351*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002822334189385341 10000000000000000000 312521627368291 312500000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312521627368291/312500000000000 : ℝ)) (X := (10002822334189385341/10000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023863958495956187/50000000000000000000 : ℝ) ≤ (1000117026910783/1000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50023863958495956187/50000000000000000000 : ℝ)^2048 ≤ (1000117026910783/1000000000000000 : ℝ)^8351 := by
      have hnat : (50023863958495956187 : ℕ)^2048*1000000000000000^8351 ≤ 1000117026910783^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023863958495956187 50000000000000000000 1000117026910783 1000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000117026910783/1000000000000000 : ℝ)) (X := (50023863958495956187/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033616246044985669/50000000000000000000 : ℝ) ≤ (2500412115607587/2500000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50033616246044985669/50000000000000000000 : ℝ)^2048 ≤ (2500412115607587/2500000000000000 : ℝ)^8351 := by
      have hnat : (50033616246044985669 : ℕ)^2048*2500000000000000^8351 ≤ 2500412115607587^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033616246044985669 50000000000000000000 2500412115607587 2500000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500412115607587/2500000000000000 : ℝ)) (X := (50033616246044985669/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2822334189385341/20000000000000000000 : ℝ) ≤ ((1348049668431278609/1348500000000000000 : ℝ)+2*(239096661259/134850000000000 : ℝ)*(11369/100000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (1348049668431278609/1348500000000000000 : ℝ)+2*(239096661259/134850000000000 : ℝ)*(11369/100000 : ℝ)=(312521627368291/312500000000000 : ℝ) by norm_num, show 1+2*(2822334189385341/20000000000000000000 : ℝ)=(10002822334189385341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33616246044985669/100000000000000000000 : ℝ)+(2822334189385341/20000000000000000000 : ℝ) ≤ ((1348049668431278609/1348500000000000000 : ℝ)+(239096661259/134850000000000 : ℝ)*((7033/50000 : ℝ)+(11369/100000 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (1348049668431278609/1348500000000000000 : ℝ)+(239096661259/134850000000000 : ℝ)*((7033/50000 : ℝ)+(11369/100000 : ℝ))=(1000117026910783/1000000000000000 : ℝ) by norm_num, show 1+(33616246044985669/100000000000000000000 : ℝ)+(2822334189385341/20000000000000000000 : ℝ)=(50023863958495956187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33616246044985669/100000000000000000000 : ℝ) ≤ ((1348049668431278609/1348500000000000000 : ℝ)+2*(239096661259/134850000000000 : ℝ)*(7033/50000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (1348049668431278609/1348500000000000000 : ℝ)+2*(239096661259/134850000000000 : ℝ)*(7033/50000 : ℝ)=(2500412115607587/2500000000000000 : ℝ) by norm_num, show 1+2*(33616246044985669/100000000000000000000 : ℝ)=(50033616246044985669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1348049668431278609/1348500000000000000 : ℝ)*(X 1 0+X 2 0)+(239096661259/134850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1348049668431278609/1348500000000000000 : ℝ)) (alpha := (239096661259/134850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1348049668431278609/1348500000000000000 : ℝ)*(X 0 1+X 2 1)+(239096661259/134850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1348049668431278609/1348500000000000000 : ℝ)) (alpha := (239096661259/134850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1348049668431278609/1348500000000000000 : ℝ)*(X 0 2+X 1 2)+(239096661259/134850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1348049668431278609/1348500000000000000 : ℝ)) (alpha := (239096661259/134850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53969469/250000000 : ℝ)*X 0 0+(5392746171/10000000000 : ℝ)*X 0 1+(1053198543/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672349401/5000000000 : ℝ)*X 1 0+(-2223066253/10000000000 : ℝ)*X 1 1+(2632996419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334043681/625000000 : ℝ)*X 2 0+(658249101/1250000000 : ℝ)*X 2 1+(-1111533083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362282827/10000000000 : ℝ)*X 0 0+(847518819/2000000000 : ℝ)*X 0 1+(4490607543/10000000000 : ℝ)*X 0 2+(4362282827/10000000000 : ℝ)*X 1 0+(847518819/2000000000 : ℝ)*X 1 1+(4490607543/10000000000 : ℝ)*X 1 2+(4362282827/10000000000 : ℝ)*X 2 0+(847518819/2000000000 : ℝ)*X 2 1+(4490607543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079391743/5000000000 : ℝ)*X 0 0+(5266311593/10000000000 : ℝ)*X 0 1+(5392426231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312545043/10000000000 : ℝ)*X 1 0+(-1048316389/5000000000 : ℝ)*X 1 1+(5392426279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106250901/200000000 : ℝ)*X 2 0+(5392426283/10000000000 : ℝ)*X 2 1+(-2096632763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181146211/5000000000 : ℝ)*X 0 0+(897994277/2000000000 : ℝ)*X 0 1+(1059558159/2500000000 : ℝ)*X 0 2+(2181146211/5000000000 : ℝ)*X 1 0+(897994277/2000000000 : ℝ)*X 1 1+(1059558159/2500000000 : ℝ)*X 1 2+(2181146211/5000000000 : ℝ)*X 2 0+(897994277/2000000000 : ℝ)*X 2 1+(1059558159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5996104809755970997981/2247500000000000000000000000 : ℝ) := by norm_num
    linear_combination (266257751/50000000000000 : ℝ)*(base19) + (655626809/100000000000000 : ℝ)*(base23) + (1063141/4000000000000 : ℝ)*(upper3) + (8360813/100000000000000 : ℝ)*(upper4) + (89973051/50000000000000 : ℝ)*(upper5) + (740109148113337/12500000000000 : ℝ)*(major0) + (740109148113337/12500000000000 : ℝ)*(major1) + (740109148113337/12500000000000 : ℝ)*(major2) + (986168406581289/12500000000000 : ℝ)*(sp0) + (7889372231881143/100000000000000 : ℝ)*(sp1) + (1577874421753967/20000000000000 : ℝ)*(sp2) + (790473483857629/20000000000000 : ℝ)*(sp3) + (6377936583/25000000000000 : ℝ)*(sp4) + (30485993/500000000000 : ℝ)*(sp7) + (494046689560843/12500000000000 : ℝ)*(f.failure) + (1972343191099161/25000000000000 : ℝ)*(f.sum) + (65232832329673/13485000000000000000000000000 : ℝ)*base65 + (65919136383073161/5618750000000000000000000000000 : ℝ)*base67 + (37083980498723161/5618750000000000000000000000000 : ℝ)*base69 + (78068854738189339/5618750000000000000000000000000 : ℝ)*base72 + (11603126549617/3371250000000000000000000000 : ℝ)*base73 + (61670843962139339/5618750000000000000000000000000 : ℝ)*base76 + (9767956082726839/5618750000000000000000000000000 : ℝ)*base78 + (13605402368398161/5618750000000000000000000000000 : ℝ)*base79 + (20255811736097/13485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7037599/1250000000000000000000 : ℝ)*base90 + (7037599/1250000000000000000000 : ℝ)*base92 + (7037599/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246517366197669290319129699/22475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (830011007/50000000000000 : ℝ)*(base19) + (193333701/10000000000000 : ℝ)*(base23) + (20942501/10000000000000 : ℝ)*(upper3) + (23068861/20000000000000 : ℝ)*(lower4) + (202501199/100000000000000 : ℝ)*(upper5) + (5950831108144989/100000000000000 : ℝ)*(major0) + (5950831108144989/100000000000000 : ℝ)*(major1) + (5950831108144989/100000000000000 : ℝ)*(major2) + (23470964683/50000000000000 : ℝ)*(sp1) + (106446833/195312500000 : ℝ)*(sp2) + (7929290455711353/100000000000000 : ℝ)*(sp4) + (7929241853759973/100000000000000 : ℝ)*(sp5) + (3964617010797923/50000000000000 : ℝ)*(sp6) + (1986185697480731/50000000000000 : ℝ)*(sp7) + (1986185697480731/50000000000000 : ℝ)*(f.failure) + (7929290455711353/100000000000000 : ℝ)*(f.sum) + (88361476631/17558593750000000000000000 : ℝ)*base66 + (65810485199133233/44950000000000000000000000000000 : ℝ)*base68 + (299359081589666767/44950000000000000000000000000000 : ℝ)*base69 + (349402019112333233/44950000000000000000000000000000 : ℝ)*base72 + (43581637973/8779296875000000000000000 : ℝ)*base74 + (616719088681266767/44950000000000000000000000000000 : ℝ)*base75 + (11195001329916767/44950000000000000000000000000000 : ℝ)*base77 + (898571004328716767/44950000000000000000000000000000 : ℝ)*base79 + (683031642411/280937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (80185617/5000000000000000000000 : ℝ)*base89 + (80185617/5000000000000000000000 : ℝ)*base91 + (80185617/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1159_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1159_s8_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158782951/10000000000 : ℝ)*x 0 + (5392686813/10000000000 : ℝ)*x 1 + (1316512349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158782951/10000000000 : ℝ)^261 ≤ (6559660964811/50000000000000 : ℝ)^197 := by
    have hnat : (2158782951 : ℕ)^261*50000000000000^197 ≤ 6559660964811^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158782951 10000000000 6559660964811 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392686813/10000000000 : ℝ)^261 ≤ (44124106415571/100000000000000 : ℝ)^197 := by
    have hnat : (5392686813 : ℕ)^261*100000000000000^197 ≤ 44124106415571^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392686813 10000000000 44124106415571 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316512349/2500000000 : ℝ)^261 ≤ (21378285821383/50000000000000 : ℝ)^197 := by
    have hnat : (1316512349 : ℕ)^261*50000000000000^197 ≤ 21378285821383^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316512349 2500000000 21378285821383 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158782951/10000000000 : ℝ), (5392686813/10000000000 : ℝ), (1316512349/2500000000 : ℝ)] ![(6559660964811/50000000000000 : ℝ), (44124106415571/100000000000000 : ℝ), (21378285821383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158782951/10000000000 : ℝ)|^261 ≤ (6559660964811/50000000000000 : ℝ)^197
        have hw : |(-2158782951/10000000000 : ℝ)|=(2158782951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392686813/10000000000 : ℝ)|^261 ≤ (44124106415571/100000000000000 : ℝ)^197
        have hw : |(5392686813/10000000000 : ℝ)|=(5392686813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316512349/2500000000 : ℝ)|^261 ≤ (21378285821383/50000000000000 : ℝ)^197
        have hw : |(1316512349/2500000000 : ℝ)|=(1316512349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2672342099/5000000000 : ℝ)*x 0 + (-555752707/2500000000 : ℝ)*x 1 + (2633024697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672342099/5000000000 : ℝ)^261 ≤ (43604493150393/100000000000000 : ℝ)^197 := by
    have hnat : (2672342099 : ℕ)^261*100000000000000^197 ≤ 43604493150393^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672342099 5000000000 43604493150393 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555752707/2500000000 : ℝ)^261 ≤ (6819467606343/50000000000000 : ℝ)^197 := by
    have hnat : (555752707 : ℕ)^261*50000000000000^197 ≤ 6819467606343^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555752707 2500000000 6819467606343 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633024697/5000000000 : ℝ)^261 ≤ (10689142905313/25000000000000 : ℝ)^197 := by
    have hnat : (2633024697 : ℕ)^261*25000000000000^197 ≤ 10689142905313^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633024697 5000000000 10689142905313 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672342099/5000000000 : ℝ), (-555752707/2500000000 : ℝ), (2633024697/5000000000 : ℝ)] ![(43604493150393/100000000000000 : ℝ), (6819467606343/50000000000000 : ℝ), (10689142905313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672342099/5000000000 : ℝ)|^261 ≤ (43604493150393/100000000000000 : ℝ)^197
        have hw : |(2672342099/5000000000 : ℝ)|=(2672342099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-555752707/2500000000 : ℝ)|^261 ≤ (6819467606343/50000000000000 : ℝ)^197
        have hw : |(-555752707/2500000000 : ℝ)|=(555752707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633024697/5000000000 : ℝ)|^261 ≤ (10689142905313/25000000000000 : ℝ)^197
        have hw : |(2633024697/5000000000 : ℝ)|=(2633024697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2672342097/5000000000 : ℝ)*x 0 + (2633024697/5000000000 : ℝ)*x 1 + (-1111505417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672342097/5000000000 : ℝ)^261 ≤ (43604493107157/100000000000000 : ℝ)^197 := by
    have hnat : (2672342097 : ℕ)^261*100000000000000^197 ≤ 43604493107157^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672342097 5000000000 43604493107157 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633024697/5000000000 : ℝ)^261 ≤ (10689142905313/25000000000000 : ℝ)^197 := by
    have hnat : (2633024697 : ℕ)^261*25000000000000^197 ≤ 10689142905313^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633024697 5000000000 10689142905313 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111505417/5000000000 : ℝ)^261 ≤ (13638935261457/100000000000000 : ℝ)^197 := by
    have hnat : (1111505417 : ℕ)^261*100000000000000^197 ≤ 13638935261457^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111505417 5000000000 13638935261457 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672342097/5000000000 : ℝ), (2633024697/5000000000 : ℝ), (-1111505417/5000000000 : ℝ)] ![(43604493107157/100000000000000 : ℝ), (10689142905313/25000000000000 : ℝ), (13638935261457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672342097/5000000000 : ℝ)|^261 ≤ (43604493107157/100000000000000 : ℝ)^197
        have hw : |(2672342097/5000000000 : ℝ)|=(2672342097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633024697/5000000000 : ℝ)|^261 ≤ (10689142905313/25000000000000 : ℝ)^197
        have hw : |(2633024697/5000000000 : ℝ)|=(2633024697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111505417/5000000000 : ℝ)|^261 ≤ (13638935261457/100000000000000 : ℝ)^197
        have hw : |(-1111505417/5000000000 : ℝ)|=(1111505417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (545285709/1250000000 : ℝ)*x 0 + (2118854683/5000000000 : ℝ)*x 1 + (4490491603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545285709/1250000000 : ℝ)^261 ≤ (333170781599/1000000000000 : ℝ)^197 := by
    have hnat : (545285709 : ℕ)^261*1000000000000^197 ≤ 333170781599^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545285709 1250000000 333170781599 1000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118854683/5000000000 : ℝ)^261 ≤ (4007800815759/12500000000000 : ℝ)^197 := by
    have hnat : (2118854683 : ℕ)^261*12500000000000^197 ≤ 4007800815759^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118854683 5000000000 4007800815759 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490491603/10000000000 : ℝ)^261 ≤ (34620515286277/100000000000000 : ℝ)^197 := by
    have hnat : (4490491603 : ℕ)^261*100000000000000^197 ≤ 34620515286277^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490491603 10000000000 34620515286277 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545285709/1250000000 : ℝ), (2118854683/5000000000 : ℝ), (4490491603/10000000000 : ℝ)] ![(333170781599/1000000000000 : ℝ), (4007800815759/12500000000000 : ℝ), (34620515286277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545285709/1250000000 : ℝ)|^261 ≤ (333170781599/1000000000000 : ℝ)^197
        have hw : |(545285709/1250000000 : ℝ)|=(545285709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118854683/5000000000 : ℝ)|^261 ≤ (4007800815759/12500000000000 : ℝ)^197
        have hw : |(2118854683/5000000000 : ℝ)|=(2118854683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490491603/10000000000 : ℝ)|^261 ≤ (34620515286277/100000000000000 : ℝ)^197
        have hw : |(4490491603/10000000000 : ℝ)|=(4490491603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-53969693/250000000 : ℝ)*x 0 + (2633183699/5000000000 : ℝ)*x 1 + (5392367707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53969693/250000000 : ℝ)^261 ≤ (1311936032723/10000000000000 : ℝ)^197 := by
    have hnat : (53969693 : ℕ)^261*10000000000000^197 ≤ 1311936032723^197*250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53969693 250000000 1311936032723 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633183699/5000000000 : ℝ)^261 ≤ (21379996216087/50000000000000 : ℝ)^197 := by
    have hnat : (2633183699 : ℕ)^261*50000000000000^197 ≤ 21379996216087^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633183699 5000000000 21379996216087 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392367707/10000000000 : ℝ)^261 ≤ (44120647214543/100000000000000 : ℝ)^197 := by
    have hnat : (5392367707 : ℕ)^261*100000000000000^197 ≤ 44120647214543^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392367707 10000000000 44120647214543 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53969693/250000000 : ℝ), (2633183699/5000000000 : ℝ), (5392367707/10000000000 : ℝ)] ![(1311936032723/10000000000000 : ℝ), (21379996216087/50000000000000 : ℝ), (44120647214543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53969693/250000000 : ℝ)|^261 ≤ (1311936032723/10000000000000 : ℝ)^197
        have hw : |(-53969693/250000000 : ℝ)|=(53969693/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633183699/5000000000 : ℝ)|^261 ≤ (21379996216087/50000000000000 : ℝ)^197
        have hw : |(2633183699/5000000000 : ℝ)|=(2633183699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392367707/10000000000 : ℝ)|^261 ≤ (44120647214543/100000000000000 : ℝ)^197
        have hw : |(5392367707/10000000000 : ℝ)|=(5392367707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1062512011/2000000000 : ℝ)*x 0 + (-2096692189/10000000000 : ℝ)*x 1 + (5392367629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062512011/2000000000 : ℝ)^261 ≤ (43257604387777/100000000000000 : ℝ)^197 := by
    have hnat : (1062512011 : ℕ)^261*100000000000000^197 ≤ 43257604387777^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062512011 2000000000 43257604387777 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096692189/10000000000 : ℝ)^261 ≤ (2524349844437/20000000000000 : ℝ)^197 := by
    have hnat : (2096692189 : ℕ)^261*20000000000000^197 ≤ 2524349844437^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096692189 10000000000 2524349844437 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392367629/10000000000 : ℝ)^261 ≤ (44120646369009/100000000000000 : ℝ)^197 := by
    have hnat : (5392367629 : ℕ)^261*100000000000000^197 ≤ 44120646369009^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392367629 10000000000 44120646369009 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062512011/2000000000 : ℝ), (-2096692189/10000000000 : ℝ), (5392367629/10000000000 : ℝ)] ![(43257604387777/100000000000000 : ℝ), (2524349844437/20000000000000 : ℝ), (44120646369009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062512011/2000000000 : ℝ)|^261 ≤ (43257604387777/100000000000000 : ℝ)^197
        have hw : |(1062512011/2000000000 : ℝ)|=(1062512011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096692189/10000000000 : ℝ)|^261 ≤ (2524349844437/20000000000000 : ℝ)^197
        have hw : |(-2096692189/10000000000 : ℝ)|=(2096692189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392367629/10000000000 : ℝ)|^261 ≤ (44120646369009/100000000000000 : ℝ)^197
        have hw : |(5392367629/10000000000 : ℝ)|=(5392367629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656279611/5000000000 : ℝ)*x 0 + (269618383/500000000 : ℝ)*x 1 + (-1048346637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656279611/5000000000 : ℝ)^261 ≤ (43257595401539/100000000000000 : ℝ)^197 := by
    have hnat : (2656279611 : ℕ)^261*100000000000000^197 ≤ 43257595401539^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656279611 5000000000 43257595401539 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269618383/500000000 : ℝ)^261 ≤ (22060323352527/50000000000000 : ℝ)^197 := by
    have hnat : (269618383 : ℕ)^261*50000000000000^197 ≤ 22060323352527^197*500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269618383 500000000 22060323352527 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048346637/5000000000 : ℝ)^261 ≤ (3155439468907/25000000000000 : ℝ)^197 := by
    have hnat : (1048346637 : ℕ)^261*25000000000000^197 ≤ 3155439468907^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048346637 5000000000 3155439468907 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656279611/5000000000 : ℝ), (269618383/500000000 : ℝ), (-1048346637/5000000000 : ℝ)] ![(43257595401539/100000000000000 : ℝ), (22060323352527/50000000000000 : ℝ), (3155439468907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656279611/5000000000 : ℝ)|^261 ≤ (43257595401539/100000000000000 : ℝ)^197
        have hw : |(2656279611/5000000000 : ℝ)|=(2656279611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269618383/500000000 : ℝ)|^261 ≤ (22060323352527/50000000000000 : ℝ)^197
        have hw : |(269618383/500000000 : ℝ)|=(269618383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048346637/5000000000 : ℝ)|^261 ≤ (3155439468907/25000000000000 : ℝ)^197
        have hw : |(-1048346637/5000000000 : ℝ)|=(1048346637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s8_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (13632171/31250000 : ℝ)*x 0 + (2244928273/5000000000 : ℝ)*x 1 + (66224177/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13632171/31250000 : ℝ)^261 ≤ (8329292428607/25000000000000 : ℝ)^197 := by
    have hnat : (13632171 : ℕ)^261*25000000000000^197 ≤ 8329292428607^197*31250000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13632171 31250000 8329292428607 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244928273/5000000000 : ℝ)^261 ≤ (4326753586657/12500000000000 : ℝ)^197 := by
    have hnat : (2244928273 : ℕ)^261*12500000000000^197 ≤ 4326753586657^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244928273 5000000000 4326753586657 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66224177/156250000 : ℝ)^261 ≤ (32068801586607/100000000000000 : ℝ)^197 := by
    have hnat : (66224177 : ℕ)^261*100000000000000^197 ≤ 32068801586607^197*156250000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66224177 156250000 32068801586607 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13632171/31250000 : ℝ), (2244928273/5000000000 : ℝ), (66224177/156250000 : ℝ)] ![(8329292428607/25000000000000 : ℝ), (4326753586657/12500000000000 : ℝ), (32068801586607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13632171/31250000 : ℝ)|^261 ≤ (8329292428607/25000000000000 : ℝ)^197
        have hw : |(13632171/31250000 : ℝ)|=(13632171/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244928273/5000000000 : ℝ)|^261 ≤ (4326753586657/12500000000000 : ℝ)^197
        have hw : |(2244928273/5000000000 : ℝ)|=(2244928273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66224177/156250000 : ℝ)|^261 ≤ (32068801586607/100000000000000 : ℝ)^197
        have hw : |(66224177/156250000 : ℝ)|=(66224177/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    (711/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/800 : ℝ) ^ (8351/2048 : ℝ) ≤ (282841272035647/2000000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^8351 ≤ (282841272035647/2000000000000000000 : ℝ)^2048 := by
      have hnat : (91 : ℕ)^8351*2000000000000000000^2048 ≤ 282841272035647^2048*800^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 282841272035647 2000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (282841272035647/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (703/5000 : ℝ) ^ (8351/2048 : ℝ) ≤ (16778906850875171/50000000000000000000 : ℝ) := by
    have hpowers : (703/5000 : ℝ)^8351 ≤ (16778906850875171/50000000000000000000 : ℝ)^2048 := by
      have hnat : (703 : ℕ)^8351*50000000000000000000^2048 ≤ 16778906850875171^2048*5000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 5000 16778906850875171 50000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/5000 : ℝ)) (X := (16778906850875171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000282841272035647/1000000000000000000 : ℝ) ≤ (10000693566166991/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (1000282841272035647/1000000000000000000 : ℝ)^2048 ≤ (10000693566166991/10000000000000000 : ℝ)^8351 := by
      have hnat : (1000282841272035647 : ℕ)^2048*10000000000000000^8351 ≤ 10000693566166991^8351*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000282841272035647 1000000000000000000 10000693566166991 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693566166991/10000000000000000 : ℝ)) (X := (1000282841272035647/1000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011924969325883173/25000000000000000000 : ℝ) ≤ (312536549428431/312500000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (25011924969325883173/25000000000000000000 : ℝ)^2048 ≤ (312536549428431/312500000000000 : ℝ)^8351 := by
      have hnat : (25011924969325883173 : ℕ)^2048*312500000000000^8351 ≤ 312536549428431^8351*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011924969325883173 25000000000000000000 312536549428431 312500000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312536549428431/312500000000000 : ℝ)) (X := (25011924969325883173/25000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016778906850875171/25000000000000000000 : ℝ) ≤ (10001645597252593/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (25016778906850875171/25000000000000000000 : ℝ)^2048 ≤ (10001645597252593/10000000000000000 : ℝ)^8351 := by
      have hnat : (25016778906850875171 : ℕ)^2048*10000000000000000^8351 ≤ 10001645597252593^8351*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016778906850875171 25000000000000000000 10001645597252593 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001645597252593/10000000000000000 : ℝ)) (X := (25016778906850875171/25000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(282841272035647/2000000000000000000 : ℝ) ≤ ((5368206574311929617/5370000000000000000 : ℝ)+2*(476015542801/268500000000000 : ℝ)*(91/800 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (5368206574311929617/5370000000000000000 : ℝ)+2*(476015542801/268500000000000 : ℝ)*(91/800 : ℝ)=(10000693566166991/10000000000000000 : ℝ) by norm_num, show 1+2*(282841272035647/2000000000000000000 : ℝ)=(1000282841272035647/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16778906850875171/50000000000000000000 : ℝ)+(282841272035647/2000000000000000000 : ℝ) ≤ ((5368206574311929617/5370000000000000000 : ℝ)+(476015542801/268500000000000 : ℝ)*((703/5000 : ℝ)+(91/800 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (5368206574311929617/5370000000000000000 : ℝ)+(476015542801/268500000000000 : ℝ)*((703/5000 : ℝ)+(91/800 : ℝ))=(312536549428431/312500000000000 : ℝ) by norm_num, show 1+(16778906850875171/50000000000000000000 : ℝ)+(282841272035647/2000000000000000000 : ℝ)=(25011924969325883173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16778906850875171/50000000000000000000 : ℝ) ≤ ((5368206574311929617/5370000000000000000 : ℝ)+2*(476015542801/268500000000000 : ℝ)*(703/5000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (5368206574311929617/5370000000000000000 : ℝ)+2*(476015542801/268500000000000 : ℝ)*(703/5000 : ℝ)=(10001645597252593/10000000000000000 : ℝ) by norm_num, show 1+2*(16778906850875171/50000000000000000000 : ℝ)=(25016778906850875171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5368206574311929617/5370000000000000000 : ℝ)*(X 1 0+X 2 0)+(476015542801/268500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (91/800 : ℝ)) (hi := (703/5000 : ℝ)) (c := (5368206574311929617/5370000000000000000 : ℝ)) (alpha := (476015542801/268500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5368206574311929617/5370000000000000000 : ℝ)*(X 0 1+X 2 1)+(476015542801/268500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (91/800 : ℝ)) (hi := (703/5000 : ℝ)) (c := (5368206574311929617/5370000000000000000 : ℝ)) (alpha := (476015542801/268500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5368206574311929617/5370000000000000000 : ℝ)*(X 0 2+X 1 2)+(476015542801/268500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (91/800 : ℝ)) (hi := (703/5000 : ℝ)) (c := (5368206574311929617/5370000000000000000 : ℝ)) (alpha := (476015542801/268500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158782951/10000000000 : ℝ)*X 0 0+(5392686813/10000000000 : ℝ)*X 0 1+(1316512349/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672342099/5000000000 : ℝ)*X 1 0+(-555752707/2500000000 : ℝ)*X 1 1+(2633024697/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672342097/5000000000 : ℝ)*X 2 0+(2633024697/5000000000 : ℝ)*X 2 1+(-1111505417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545285709/1250000000 : ℝ)*X 0 0+(2118854683/5000000000 : ℝ)*X 0 1+(4490491603/10000000000 : ℝ)*X 0 2+(545285709/1250000000 : ℝ)*X 1 0+(2118854683/5000000000 : ℝ)*X 1 1+(4490491603/10000000000 : ℝ)*X 1 2+(545285709/1250000000 : ℝ)*X 2 0+(2118854683/5000000000 : ℝ)*X 2 1+(4490491603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53969693/250000000 : ℝ)*X 0 0+(2633183699/5000000000 : ℝ)*X 0 1+(5392367707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062512011/2000000000 : ℝ)*X 1 0+(-2096692189/10000000000 : ℝ)*X 1 1+(5392367629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656279611/5000000000 : ℝ)*X 2 0+(269618383/500000000 : ℝ)*X 2 1+(-1048346637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((13632171/31250000 : ℝ)*X 0 0+(2244928273/5000000000 : ℝ)*X 0 1+(66224177/156250000 : ℝ)*X 0 2+(13632171/31250000 : ℝ)*X 1 0+(2244928273/5000000000 : ℝ)*X 1 1+(66224177/156250000 : ℝ)*X 1 2+(13632171/31250000 : ℝ)*X 2 0+(2244928273/5000000000 : ℝ)*X 2 1+(66224177/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214135652385873458179378959/44750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (941565169/100000000000000 : ℝ)*(base19) + (870165583/100000000000000 : ℝ)*(base23) + (1750109/5000000000000 : ℝ)*(lower2) + (123573579/100000000000000 : ℝ)*(upper3) + (32447199/50000000000000 : ℝ)*(upper5) + (2963153432525691/50000000000000 : ℝ)*(major0) + (2963153432525691/50000000000000 : ℝ)*(major1) + (2963153432525691/50000000000000 : ℝ)*(major2) + (7896587518941567/100000000000000 : ℝ)*(sp0) + (197415298901807/2500000000000 : ℝ)*(sp1) + (3948306013735933/50000000000000 : ℝ)*(sp2) + (3955986632717377/100000000000000 : ℝ)*(sp3) + (12689347941/50000000000000 : ℝ)*(sp4) + (2808048557/20000000000000 : ℝ)*(sp7) + (1978000336480081/50000000000000 : ℝ)*(f.failure) + (7896612897637449/100000000000000 : ℝ)*(f.sum) + (2297686117331/4475000000000000000000000000 : ℝ)*base66 + (1451342948438203449/89500000000000000000000000000000 : ℝ)*base67 + (1824776747477203449/89500000000000000000000000000000 : ℝ)*base69 + (823369385980703449/89500000000000000000000000000000 : ℝ)*base71 + (7547201336603/2237500000000000000000000000 : ℝ)*base74 + (2953920184324203449/89500000000000000000000000000000 : ℝ)*base75 + (1635308502502703449/89500000000000000000000000000000 : ℝ)*base77 + (690482129806703449/89500000000000000000000000000000 : ℝ)*base79 + (4371371045331/4475000000000000000000000000 : ℝ)*base82 + (29606067/5000000000000000000000 : ℝ)*base89 + (29606067/5000000000000000000000 : ℝ)*base91 + (29606067/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (456253958554860565574009447/89500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26503399/100000000000000 : ℝ)*(base8) + (166636263/100000000000000 : ℝ)*(upper1) + (47300079/10000000000000 : ℝ)*(upper2) + (9438687/3125000000000 : ℝ)*(lower4) + (729909/1562500000000 : ℝ)*(lower5) + (5956251182984003/100000000000000 : ℝ)*(major0) + (5956251182984003/100000000000000 : ℝ)*(major1) + (5956251182984003/100000000000000 : ℝ)*(major2) + (26042192661/100000000000000 : ℝ)*(sp0) + (35464685769/100000000000000 : ℝ)*(sp1) + (3968243328944863/50000000000000 : ℝ)*(sp4) + (3968238630950009/50000000000000 : ℝ)*(sp5) + (3968256363292893/50000000000000 : ℝ)*(sp6) + (198799473472761/5000000000000 : ℝ)*(sp7) + (198799473472761/5000000000000 : ℝ)*(f.failure) + (3968256363292893/50000000000000 : ℝ)*(f.sum) + (41582428355539/6712500000000000000000000000 : ℝ)*base65 + (3559178931221325617/179000000000000000000000000000000 : ℝ)*base67 + (2372353309298325617/179000000000000000000000000000000 : ℝ)*base69 + (972934092032325617/179000000000000000000000000000000 : ℝ)*base71 + (45958101300353/13425000000000000000000000000 : ℝ)*base73 + (3067512290968325617/179000000000000000000000000000000 : ℝ)*base75 + (1626631488072325617/179000000000000000000000000000000 : ℝ)*base77 + (3992994664220325617/179000000000000000000000000000000 : ℝ)*base79 + (26344180273897/13425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2705173/500000000000000000000 : ℝ)*base90 + (2705173/500000000000000000000 : ℝ)*base92 + (2705173/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1159_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1159_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1159_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1159_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1159_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

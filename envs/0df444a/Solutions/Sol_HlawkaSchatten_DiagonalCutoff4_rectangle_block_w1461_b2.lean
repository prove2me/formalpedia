-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1461_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:32.118127+00:00
-- url     : https://prove2.me/submissions/46aec3ed-79eb-4baa-a2aa-0f88a45cfa6b

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
theorem support_rectangle_w1461_s6_0 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-972729243/5000000000 : ℝ)*x 0 + (1351643219/2500000000 : ℝ)*x 1 + (5247574893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972729243/5000000000 : ℝ)^4421 ≤ (11876897501911/100000000000000 : ℝ)^3397 := by
    have hnat : (972729243 : ℕ)^4421*100000000000000^3397 ≤ 11876897501911^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972729243 5000000000 11876897501911 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351643219/2500000000 : ℝ)^4421 ≤ (44917278340389/100000000000000 : ℝ)^3397 := by
    have hnat : (1351643219 : ℕ)^4421*100000000000000^3397 ≤ 44917278340389^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351643219 2500000000 44917278340389 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247574893/10000000000 : ℝ)^4421 ≤ (43205824153253/100000000000000 : ℝ)^3397 := by
    have hnat : (5247574893 : ℕ)^4421*100000000000000^3397 ≤ 43205824153253^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247574893 10000000000 43205824153253 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-972729243/5000000000 : ℝ), (1351643219/2500000000 : ℝ), (5247574893/10000000000 : ℝ)] ![(11876897501911/100000000000000 : ℝ), (44917278340389/100000000000000 : ℝ), (43205824153253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-972729243/5000000000 : ℝ)|^4421 ≤ (11876897501911/100000000000000 : ℝ)^3397
        have hw : |(-972729243/5000000000 : ℝ)|=(972729243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351643219/2500000000 : ℝ)|^4421 ≤ (44917278340389/100000000000000 : ℝ)^3397
        have hw : |(1351643219/2500000000 : ℝ)|=(1351643219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247574893/10000000000 : ℝ)|^4421 ≤ (43205824153253/100000000000000 : ℝ)^3397
        have hw : |(5247574893/10000000000 : ℝ)|=(5247574893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_1 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336658773/2500000000 : ℝ)*x 0 + (-2026385691/10000000000 : ℝ)*x 1 + (5247574847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336658773/2500000000 : ℝ)^4421 ≤ (22135150654253/50000000000000 : ℝ)^3397 := by
    have hnat : (1336658773 : ℕ)^4421*50000000000000^3397 ≤ 22135150654253^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336658773 2500000000 22135150654253 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026385691/10000000000 : ℝ)^4421 ≤ (313096875481/2500000000000 : ℝ)^3397 := by
    have hnat : (2026385691 : ℕ)^4421*2500000000000^3397 ≤ 313096875481^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026385691 10000000000 313096875481 2500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247574847/10000000000 : ℝ)^4421 ≤ (5400727957543/12500000000000 : ℝ)^3397 := by
    have hnat : (5247574847 : ℕ)^4421*12500000000000^3397 ≤ 5400727957543^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247574847 10000000000 5400727957543 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336658773/2500000000 : ℝ), (-2026385691/10000000000 : ℝ), (5247574847/10000000000 : ℝ)] ![(22135150654253/50000000000000 : ℝ), (313096875481/2500000000000 : ℝ), (5400727957543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336658773/2500000000 : ℝ)|^4421 ≤ (22135150654253/50000000000000 : ℝ)^3397
        have hw : |(1336658773/2500000000 : ℝ)|=(1336658773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2026385691/10000000000 : ℝ)|^4421 ≤ (313096875481/2500000000000 : ℝ)^3397
        have hw : |(-2026385691/10000000000 : ℝ)|=(2026385691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247574847/10000000000 : ℝ)|^4421 ≤ (5400727957543/12500000000000 : ℝ)^3397
        have hw : |(5247574847/10000000000 : ℝ)|=(5247574847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_2 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346635061/10000000000 : ℝ)*x 0 + (5247574849/10000000000 : ℝ)*x 1 + (-2026385729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346635061/10000000000 : ℝ)^4421 ≤ (44270300974451/100000000000000 : ℝ)^3397 := by
    have hnat : (5346635061 : ℕ)^4421*100000000000000^3397 ≤ 44270300974451^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346635061 10000000000 44270300974451 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247574849/10000000000 : ℝ)^4421 ≤ (1728232947271/4000000000000 : ℝ)^3397 := by
    have hnat : (5247574849 : ℕ)^4421*4000000000000^3397 ≤ 1728232947271^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247574849 10000000000 1728232947271 4000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026385729/10000000000 : ℝ)^4421 ≤ (12523875324891/100000000000000 : ℝ)^3397 := by
    have hnat : (2026385729 : ℕ)^4421*100000000000000^3397 ≤ 12523875324891^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026385729 10000000000 12523875324891 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346635061/10000000000 : ℝ), (5247574849/10000000000 : ℝ), (-2026385729/10000000000 : ℝ)] ![(44270300974451/100000000000000 : ℝ), (1728232947271/4000000000000 : ℝ), (12523875324891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346635061/10000000000 : ℝ)|^4421 ≤ (44270300974451/100000000000000 : ℝ)^3397
        have hw : |(5346635061/10000000000 : ℝ)|=(5346635061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247574849/10000000000 : ℝ)|^4421 ≤ (1728232947271/4000000000000 : ℝ)^3397
        have hw : |(5247574849/10000000000 : ℝ)|=(5247574849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2026385729/10000000000 : ℝ)|^4421 ≤ (12523875324891/100000000000000 : ℝ)^3397
        have hw : |(-2026385729/10000000000 : ℝ)|=(2026385729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_3 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214821793/500000000 : ℝ)*x 0 + (2062780143/5000000000 : ℝ)*x 1 + (1118390781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214821793/500000000 : ℝ)^4421 ≤ (6661033312819/20000000000000 : ℝ)^3397 := by
    have hnat : (214821793 : ℕ)^4421*20000000000000^3397 ≤ 6661033312819^3397*500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214821793 500000000 6661033312819 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062780143/5000000000 : ℝ)^4421 ≤ (15795856406151/50000000000000 : ℝ)^3397 := by
    have hnat : (2062780143 : ℕ)^4421*50000000000000^3397 ≤ 15795856406151^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062780143 5000000000 15795856406151 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118390781/2500000000 : ℝ)^4421 ≤ (17551560305879/50000000000000 : ℝ)^3397 := by
    have hnat : (1118390781 : ℕ)^4421*50000000000000^3397 ≤ 17551560305879^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118390781 2500000000 17551560305879 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214821793/500000000 : ℝ), (2062780143/5000000000 : ℝ), (1118390781/2500000000 : ℝ)] ![(6661033312819/20000000000000 : ℝ), (15795856406151/50000000000000 : ℝ), (17551560305879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214821793/500000000 : ℝ)|^4421 ≤ (6661033312819/20000000000000 : ℝ)^3397
        have hw : |(214821793/500000000 : ℝ)|=(214821793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062780143/5000000000 : ℝ)|^4421 ≤ (15795856406151/50000000000000 : ℝ)^3397
        have hw : |(2062780143/5000000000 : ℝ)|=(2062780143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1118390781/2500000000 : ℝ)|^4421 ≤ (17551560305879/50000000000000 : ℝ)^3397
        have hw : |(1118390781/2500000000 : ℝ)|=(1118390781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_4 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1945469519/10000000000 : ℝ)*x 0 + (2624074999/5000000000 : ℝ)*x 1 + (1081198959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1945469519/10000000000 : ℝ)^4421 ≤ (2375397032323/20000000000000 : ℝ)^3397 := by
    have hnat : (1945469519 : ℕ)^4421*20000000000000^3397 ≤ 2375397032323^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945469519 10000000000 2375397032323 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624074999/5000000000 : ℝ)^4421 ≤ (10802996684601/25000000000000 : ℝ)^3397 := by
    have hnat : (2624074999 : ℕ)^4421*25000000000000^3397 ≤ 10802996684601^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624074999 5000000000 10802996684601 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081198959/2000000000 : ℝ)^4421 ≤ (44911028081067/100000000000000 : ℝ)^3397 := by
    have hnat : (1081198959 : ℕ)^4421*100000000000000^3397 ≤ 44911028081067^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081198959 2000000000 44911028081067 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1945469519/10000000000 : ℝ), (2624074999/5000000000 : ℝ), (1081198959/2000000000 : ℝ)] ![(2375397032323/20000000000000 : ℝ), (10802996684601/25000000000000 : ℝ), (44911028081067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1945469519/10000000000 : ℝ)|^4421 ≤ (2375397032323/20000000000000 : ℝ)^3397
        have hw : |(-1945469519/10000000000 : ℝ)|=(1945469519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624074999/5000000000 : ℝ)|^4421 ≤ (10802996684601/25000000000000 : ℝ)^3397
        have hw : |(2624074999/5000000000 : ℝ)|=(2624074999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081198959/2000000000 : ℝ)|^4421 ≤ (44911028081067/100000000000000 : ℝ)^3397
        have hw : |(1081198959/2000000000 : ℝ)|=(1081198959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_5 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326293501/2500000000 : ℝ)*x 0 + (-466991433/2500000000 : ℝ)*x 1 + (5405994771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326293501/2500000000 : ℝ)^4421 ≤ (21912020232761/50000000000000 : ℝ)^3397 := by
    have hnat : (1326293501 : ℕ)^4421*50000000000000^3397 ≤ 21912020232761^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326293501 2500000000 21912020232761 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466991433/2500000000 : ℝ)^4421 ≤ (563246584957/5000000000000 : ℝ)^3397 := by
    have hnat : (466991433 : ℕ)^4421*5000000000000^3397 ≤ 563246584957^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466991433 2500000000 563246584957 5000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405994771/10000000000 : ℝ)^4421 ≤ (44911027821581/100000000000000 : ℝ)^3397 := by
    have hnat : (5405994771 : ℕ)^4421*100000000000000^3397 ≤ 44911027821581^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405994771 10000000000 44911027821581 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326293501/2500000000 : ℝ), (-466991433/2500000000 : ℝ), (5405994771/10000000000 : ℝ)] ![(21912020232761/50000000000000 : ℝ), (563246584957/5000000000000 : ℝ), (44911027821581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326293501/2500000000 : ℝ)|^4421 ≤ (21912020232761/50000000000000 : ℝ)^3397
        have hw : |(1326293501/2500000000 : ℝ)|=(1326293501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466991433/2500000000 : ℝ)|^4421 ≤ (563246584957/5000000000000 : ℝ)^3397
        have hw : |(-466991433/2500000000 : ℝ)|=(466991433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405994771/10000000000 : ℝ)|^4421 ≤ (44911027821581/100000000000000 : ℝ)^3397
        have hw : |(5405994771/10000000000 : ℝ)|=(5405994771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_6 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305173969/10000000000 : ℝ)*x 0 + (5405994767/10000000000 : ℝ)*x 1 + (-933982893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305173969/10000000000 : ℝ)^4421 ≤ (43824040089247/100000000000000 : ℝ)^3397 := by
    have hnat : (5305173969 : ℕ)^4421*100000000000000^3397 ≤ 43824040089247^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305173969 10000000000 43824040089247 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405994767/10000000000 : ℝ)^4421 ≤ (22455513889167/50000000000000 : ℝ)^3397 := by
    have hnat : (5405994767 : ℕ)^4421*50000000000000^3397 ≤ 22455513889167^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405994767 10000000000 22455513889167 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933982893/5000000000 : ℝ)^4421 ≤ (11264932122957/100000000000000 : ℝ)^3397 := by
    have hnat : (933982893 : ℕ)^4421*100000000000000^3397 ≤ 11264932122957^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933982893 5000000000 11264932122957 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305173969/10000000000 : ℝ), (5405994767/10000000000 : ℝ), (-933982893/5000000000 : ℝ)] ![(43824040089247/100000000000000 : ℝ), (22455513889167/50000000000000 : ℝ), (11264932122957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305173969/10000000000 : ℝ)|^4421 ≤ (43824040089247/100000000000000 : ℝ)^3397
        have hw : |(5305173969/10000000000 : ℝ)|=(5305173969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405994767/10000000000 : ℝ)|^4421 ≤ (22455513889167/50000000000000 : ℝ)^3397
        have hw : |(5405994767/10000000000 : ℝ)|=(5405994767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-933982893/5000000000 : ℝ)|^4421 ≤ (11264932122957/100000000000000 : ℝ)^3397
        have hw : |(-933982893/5000000000 : ℝ)|=(933982893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s6_7 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148230001/5000000000 : ℝ)*x 0 + (178892171/400000000 : ℝ)*x 1 + (1031706423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148230001/5000000000 : ℝ)^4421 ≤ (520397033153/1562500000000 : ℝ)^3397 := by
    have hnat : (2148230001 : ℕ)^4421*1562500000000^3397 ≤ 520397033153^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148230001 5000000000 520397033153 1562500000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178892171/400000000 : ℝ)^4421 ≤ (17545132802007/50000000000000 : ℝ)^3397 := by
    have hnat : (178892171 : ℕ)^4421*50000000000000^3397 ≤ 17545132802007^3397*400000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178892171 400000000 17545132802007 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031706423/2500000000 : ℝ)^4421 ≤ (7901081066631/25000000000000 : ℝ)^3397 := by
    have hnat : (1031706423 : ℕ)^4421*25000000000000^3397 ≤ 7901081066631^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031706423 2500000000 7901081066631 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148230001/5000000000 : ℝ), (178892171/400000000 : ℝ), (1031706423/2500000000 : ℝ)] ![(520397033153/1562500000000 : ℝ), (17545132802007/50000000000000 : ℝ), (7901081066631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148230001/5000000000 : ℝ)|^4421 ≤ (520397033153/1562500000000 : ℝ)^3397
        have hw : |(2148230001/5000000000 : ℝ)|=(2148230001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(178892171/400000000 : ℝ)|^4421 ≤ (17545132802007/50000000000000 : ℝ)^3397
        have hw : |(178892171/400000000 : ℝ)|=(178892171/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031706423/2500000000 : ℝ)|^4421 ≤ (7901081066631/25000000000000 : ℝ)^3397
        have hw : |(1031706423/2500000000 : ℝ)|=(1031706423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1461_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2851/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11401/100000 : ℝ) ^ (1105/256 : ℝ) ≤ (8499289780015451/100000000000000000000 : ℝ) := by
    have hpowers : (11401/100000 : ℝ)^1105 ≤ (8499289780015451/100000000000000000000 : ℝ)^256 := by
      have hnat : (11401 : ℕ)^1105*100000000000000000000^256 ≤ 8499289780015451^256*100000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11401 100000 8499289780015451 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11401/100000 : ℝ)) (X := (8499289780015451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (1105/256 : ℝ) ≤ (26029758395033251/100000000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^1105 ≤ (26029758395033251/100000000000000000000 : ℝ)^256 := by
      have hnat : (1847 : ℕ)^1105*100000000000000000000^256 ≤ 26029758395033251^256*12500^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 26029758395033251 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (26029758395033251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008499289780015451/50000000000000000000 : ℝ) ≤ (10000393787531607/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50008499289780015451/50000000000000000000 : ℝ)^256 ≤ (10000393787531607/10000000000000000 : ℝ)^1105 := by
      have hnat : (50008499289780015451 : ℕ)^256*10000000000000000^1105 ≤ 10000393787531607^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008499289780015451 50000000000000000000 10000393787531607 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000393787531607/10000000000000000 : ℝ)) (X := (50008499289780015451/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017264524087524351/50000000000000000000 : ℝ) ≤ (31252499509061/31250000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50017264524087524351/50000000000000000000 : ℝ)^256 ≤ (31252499509061/31250000000000 : ℝ)^1105 := by
      have hnat : (50017264524087524351 : ℕ)^256*31250000000000^1105 ≤ 31252499509061^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017264524087524351 50000000000000000000 31252499509061 31250000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252499509061/31250000000000 : ℝ)) (X := (50017264524087524351/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026029758395033251/50000000000000000000 : ℝ) ≤ (10001205898267433/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50026029758395033251/50000000000000000000 : ℝ)^256 ≤ (10001205898267433/10000000000000000 : ℝ)^1105 := by
      have hnat : (50026029758395033251 : ℕ)^256*10000000000000000^1105 ≤ 10001205898267433^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026029758395033251 50000000000000000000 10001205898267433 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001205898267433/10000000000000000 : ℝ)) (X := (50026029758395033251/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8499289780015451/100000000000000000000 : ℝ) ≤ ((33742070158420021399/33750000000000000000 : ℝ)+2*(406055367913/337500000000000 : ℝ)*(11401/100000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (33742070158420021399/33750000000000000000 : ℝ)+2*(406055367913/337500000000000 : ℝ)*(11401/100000 : ℝ)=(10000393787531607/10000000000000000 : ℝ) by norm_num, show 1+2*(8499289780015451/100000000000000000000 : ℝ)=(50008499289780015451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26029758395033251/100000000000000000000 : ℝ)+(8499289780015451/100000000000000000000 : ℝ) ≤ ((33742070158420021399/33750000000000000000 : ℝ)+(406055367913/337500000000000 : ℝ)*((1847/12500 : ℝ)+(11401/100000 : ℝ)))^(1105/256 : ℝ) := by
    rw [show (33742070158420021399/33750000000000000000 : ℝ)+(406055367913/337500000000000 : ℝ)*((1847/12500 : ℝ)+(11401/100000 : ℝ))=(31252499509061/31250000000000 : ℝ) by norm_num, show 1+(26029758395033251/100000000000000000000 : ℝ)+(8499289780015451/100000000000000000000 : ℝ)=(50017264524087524351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26029758395033251/100000000000000000000 : ℝ) ≤ ((33742070158420021399/33750000000000000000 : ℝ)+2*(406055367913/337500000000000 : ℝ)*(1847/12500 : ℝ))^(1105/256 : ℝ) := by
    rw [show (33742070158420021399/33750000000000000000 : ℝ)+2*(406055367913/337500000000000 : ℝ)*(1847/12500 : ℝ)=(10001205898267433/10000000000000000 : ℝ) by norm_num, show 1+2*(26029758395033251/100000000000000000000 : ℝ)=(50026029758395033251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33742070158420021399/33750000000000000000 : ℝ)*(X 1 0+X 2 0)+(406055367913/337500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (33742070158420021399/33750000000000000000 : ℝ)) (alpha := (406055367913/337500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33742070158420021399/33750000000000000000 : ℝ)*(X 0 1+X 2 1)+(406055367913/337500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (33742070158420021399/33750000000000000000 : ℝ)) (alpha := (406055367913/337500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33742070158420021399/33750000000000000000 : ℝ)*(X 0 2+X 1 2)+(406055367913/337500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (33742070158420021399/33750000000000000000 : ℝ)) (alpha := (406055367913/337500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-972729243/5000000000 : ℝ)*X 0 0+(1351643219/2500000000 : ℝ)*X 0 1+(5247574893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336658773/2500000000 : ℝ)*X 1 0+(-2026385691/10000000000 : ℝ)*X 1 1+(5247574847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346635061/10000000000 : ℝ)*X 2 0+(5247574849/10000000000 : ℝ)*X 2 1+(-2026385729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214821793/500000000 : ℝ)*X 0 0+(2062780143/5000000000 : ℝ)*X 0 1+(1118390781/2500000000 : ℝ)*X 0 2+(214821793/500000000 : ℝ)*X 1 0+(2062780143/5000000000 : ℝ)*X 1 1+(1118390781/2500000000 : ℝ)*X 1 2+(214821793/500000000 : ℝ)*X 2 0+(2062780143/5000000000 : ℝ)*X 2 1+(1118390781/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1945469519/10000000000 : ℝ)*X 0 0+(2624074999/5000000000 : ℝ)*X 0 1+(1081198959/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326293501/2500000000 : ℝ)*X 1 0+(-466991433/2500000000 : ℝ)*X 1 1+(5405994771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305173969/10000000000 : ℝ)*X 2 0+(5405994767/10000000000 : ℝ)*X 2 1+(-933982893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148230001/5000000000 : ℝ)*X 0 0+(178892171/400000000 : ℝ)*X 0 1+(1031706423/2500000000 : ℝ)*X 0 2+(2148230001/5000000000 : ℝ)*X 1 0+(178892171/400000000 : ℝ)*X 1 1+(1031706423/2500000000 : ℝ)*X 1 2+(2148230001/5000000000 : ℝ)*X 2 0+(178892171/400000000 : ℝ)*X 2 1+(1031706423/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44680662446746766197122077/7812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1028423343/100000000000000 : ℝ)*(base19) + (446556003/50000000000000 : ℝ)*(base23) + (13212203/25000000000000 : ℝ)*(lower2) + (8857111/5000000000000 : ℝ)*(upper3) + (25008241/50000000000000 : ℝ)*(upper5) + (572686688083893/12500000000000 : ℝ)*(major0) + (572686688083893/12500000000000 : ℝ)*(major1) + (572686688083893/12500000000000 : ℝ)*(major2) + (3144704852282379/50000000000000 : ℝ)*(sp0) + (1572356629915981/25000000000000 : ℝ)*(sp1) + (6289426654975261/100000000000000 : ℝ)*(sp2) + (574709679760331/20000000000000 : ℝ)*(sp3) + (17843522509/100000000000000 : ℝ)*(sp4) + (10871815867/100000000000000 : ℝ)*(sp7) + (1436779635308761/50000000000000 : ℝ)*(f.failure) + (3144713774043633/50000000000000 : ℝ)*(f.sum) + (11523216971051/5625000000000000000000000000 : ℝ)*base66 + (122231883742083769/140625000000000000000000000000000 : ℝ)*base67 + (535420057304583769/140625000000000000000000000000000 : ℝ)*base69 + (80915232601458769/140625000000000000000000000000000 : ℝ)*base71 + (32761098551449/5625000000000000000000000000 : ℝ)*base73 + (699683422554791231/140625000000000000000000000000000 : ℝ)*base76 + (580780166710833769/140625000000000000000000000000000 : ℝ)*base77 + (782155841117291231/140625000000000000000000000000000 : ℝ)*base80 + (25138764303949/5625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33386873/5000000000000000000000 : ℝ)*base89 + (33386873/5000000000000000000000 : ℝ)*base91 + (33386873/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5005507795038758289709894771/562500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (376488969/25000000000000 : ℝ)*(base19) + (1597556261/100000000000000 : ℝ)*(base23) + (514489083/100000000000000 : ℝ)*(lower1) + (158262911/100000000000000 : ℝ)*(upper3) + (35892333/50000000000000 : ℝ)*(lower4) + (9205233/5000000000000 : ℝ)*(upper5) + (4614911554154171/100000000000000 : ℝ)*(major0) + (4614911554154171/100000000000000 : ℝ)*(major1) + (4614911554154171/100000000000000 : ℝ)*(major2) + (30616369/12500000000000 : ℝ)*(sp1) + (791912925116303/12500000000000 : ℝ)*(sp4) + (1583825412510899/25000000000000 : ℝ)*(sp5) + (6335301803374163/100000000000000 : ℝ)*(sp6) + (289451941075523/10000000000000 : ℝ)*(sp7) + (289451941075523/10000000000000 : ℝ)*(f.failure) + (791912925116303/12500000000000 : ℝ)*(f.sum) + (94816279197623/16875000000000000000000000000 : ℝ)*base65 + (12034311486927405229/3375000000000000000000000000000000 : ℝ)*base67 + (12198455158677405229/3375000000000000000000000000000000 : ℝ)*base69 + (28389868524177405229/3375000000000000000000000000000000 : ℝ)*base71 + (38195571448627/16875000000000000000000000000 : ℝ)*base74 + (3204564848822594771/3375000000000000000000000000000000 : ℝ)*base76 + (11667051279947594771/3375000000000000000000000000000000 : ℝ)*base78 + (11334789179052405229/3375000000000000000000000000000000 : ℝ)*base79 + (78513893443627/16875000000000000000000000000 : ℝ)*base82 + (2603939/1000000000000000000000 : ℝ)*base89 + (2603939/1000000000000000000000 : ℝ)*base91 + (2603939/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1461_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1461_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1461_s7_0 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336657467/2500000000 : ℝ)*x 0 + (5247594099/10000000000 : ℝ)*x 1 + (-2026367041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336657467/2500000000 : ℝ)^4421 ≤ (44270245014779/100000000000000 : ℝ)^3397 := by
    have hnat : (1336657467 : ℕ)^4421*100000000000000^3397 ≤ 44270245014779^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336657467 2500000000 44270245014779 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247594099/10000000000 : ℝ)^4421 ≤ (43206029953447/100000000000000 : ℝ)^3397 := by
    have hnat : (5247594099 : ℕ)^4421*100000000000000^3397 ≤ 43206029953447^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247594099 10000000000 43206029953447 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026367041/10000000000 : ℝ)^4421 ≤ (391366406543/3125000000000 : ℝ)^3397 := by
    have hnat : (2026367041 : ℕ)^4421*3125000000000^3397 ≤ 391366406543^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026367041 10000000000 391366406543 3125000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336657467/2500000000 : ℝ), (5247594099/10000000000 : ℝ), (-2026367041/10000000000 : ℝ)] ![(44270245014779/100000000000000 : ℝ), (43206029953447/100000000000000 : ℝ), (391366406543/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336657467/2500000000 : ℝ)|^4421 ≤ (44270245014779/100000000000000 : ℝ)^3397
        have hw : |(1336657467/2500000000 : ℝ)|=(1336657467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247594099/10000000000 : ℝ)|^4421 ≤ (43206029953447/100000000000000 : ℝ)^3397
        have hw : |(5247594099/10000000000 : ℝ)|=(5247594099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2026367041/10000000000 : ℝ)|^4421 ≤ (391366406543/3125000000000 : ℝ)^3397
        have hw : |(-2026367041/10000000000 : ℝ)|=(2026367041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s7_1 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-486367873/2500000000 : ℝ)*x 0 + (2624084509/5000000000 : ℝ)*x 1 + (1081194899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486367873/2500000000 : ℝ)^4421 ≤ (5938500418783/50000000000000 : ℝ)^3397 := by
    have hnat : (486367873 : ℕ)^4421*50000000000000^3397 ≤ 5938500418783^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486367873 2500000000 5938500418783 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624084509/5000000000 : ℝ)^4421 ≤ (5401523819033/12500000000000 : ℝ)^3397 := by
    have hnat : (2624084509 : ℕ)^4421*12500000000000^3397 ≤ 5401523819033^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624084509 5000000000 5401523819033 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081194899/2000000000 : ℝ)^4421 ≤ (44910808599459/100000000000000 : ℝ)^3397 := by
    have hnat : (1081194899 : ℕ)^4421*100000000000000^3397 ≤ 44910808599459^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081194899 2000000000 44910808599459 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486367873/2500000000 : ℝ), (2624084509/5000000000 : ℝ), (1081194899/2000000000 : ℝ)] ![(5938500418783/50000000000000 : ℝ), (5401523819033/12500000000000 : ℝ), (44910808599459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486367873/2500000000 : ℝ)|^4421 ≤ (5938500418783/50000000000000 : ℝ)^3397
        have hw : |(-486367873/2500000000 : ℝ)|=(486367873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624084509/5000000000 : ℝ)|^4421 ≤ (5401523819033/12500000000000 : ℝ)^3397
        have hw : |(2624084509/5000000000 : ℝ)|=(2624084509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081194899/2000000000 : ℝ)|^4421 ≤ (44910808599459/100000000000000 : ℝ)^3397
        have hw : |(1081194899/2000000000 : ℝ)|=(1081194899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s7_2 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305179129/10000000000 : ℝ)*x 0 + (-933993291/5000000000 : ℝ)*x 1 + (270298727/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305179129/10000000000 : ℝ)^4421 ≤ (10956023890749/25000000000000 : ℝ)^3397 := by
    have hnat : (5305179129 : ℕ)^4421*25000000000000^3397 ≤ 10956023890749^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305179129 10000000000 10956023890749 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933993291/5000000000 : ℝ)^4421 ≤ (11265095339873/100000000000000 : ℝ)^3397 := by
    have hnat : (933993291 : ℕ)^4421*100000000000000^3397 ≤ 11265095339873^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933993291 5000000000 11265095339873 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270298727/500000000 : ℝ)^4421 ≤ (22455404542997/50000000000000 : ℝ)^3397 := by
    have hnat : (270298727 : ℕ)^4421*50000000000000^3397 ≤ 22455404542997^3397*500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270298727 500000000 22455404542997 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305179129/10000000000 : ℝ), (-933993291/5000000000 : ℝ), (270298727/500000000 : ℝ)] ![(10956023890749/25000000000000 : ℝ), (11265095339873/100000000000000 : ℝ), (22455404542997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305179129/10000000000 : ℝ)|^4421 ≤ (10956023890749/25000000000000 : ℝ)^3397
        have hw : |(5305179129/10000000000 : ℝ)|=(5305179129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-933993291/5000000000 : ℝ)|^4421 ≤ (11265095339873/100000000000000 : ℝ)^3397
        have hw : |(-933993291/5000000000 : ℝ)|=(933993291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270298727/500000000 : ℝ)|^4421 ≤ (22455404542997/50000000000000 : ℝ)^3397
        have hw : |(270298727/500000000 : ℝ)|=(270298727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s7_3 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331573687/625000000 : ℝ)*x 0 + (108119493/200000000 : ℝ)*x 1 + (-1867986617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331573687/625000000 : ℝ)^4421 ≤ (21912047045073/50000000000000 : ℝ)^3397 := by
    have hnat : (331573687 : ℕ)^4421*50000000000000^3397 ≤ 21912047045073^3397*625000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331573687 625000000 21912047045073 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108119493/200000000 : ℝ)^4421 ≤ (44910810275303/100000000000000 : ℝ)^3397 := by
    have hnat : (108119493 : ℕ)^4421*100000000000000^3397 ≤ 44910810275303^3397*200000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108119493 200000000 44910810275303 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867986617/10000000000 : ℝ)^4421 ≤ (1126509561457/10000000000000 : ℝ)^3397 := by
    have hnat : (1867986617 : ℕ)^4421*10000000000000^3397 ≤ 1126509561457^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867986617 10000000000 1126509561457 10000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331573687/625000000 : ℝ), (108119493/200000000 : ℝ), (-1867986617/10000000000 : ℝ)] ![(21912047045073/50000000000000 : ℝ), (44910810275303/100000000000000 : ℝ), (1126509561457/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331573687/625000000 : ℝ)|^4421 ≤ (21912047045073/50000000000000 : ℝ)^3397
        have hw : |(331573687/625000000 : ℝ)|=(331573687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108119493/200000000 : ℝ)|^4421 ≤ (44910810275303/100000000000000 : ℝ)^3397
        have hw : |(108119493/200000000 : ℝ)|=(108119493/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867986617/10000000000 : ℝ)|^4421 ≤ (1126509561457/10000000000000 : ℝ)^3397
        have hw : |(-1867986617/10000000000 : ℝ)|=(1867986617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s7_4 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34371691/80000000 : ℝ)*x 0 + (894452251/2000000000 : ℝ)*x 1 + (515858547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34371691/80000000 : ℝ)^4421 ≤ (33305423973379/100000000000000 : ℝ)^3397 := by
    have hnat : (34371691 : ℕ)^4421*100000000000000^3397 ≤ 33305423973379^3397*80000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34371691 80000000 33305423973379 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894452251/2000000000 : ℝ)^4421 ≤ (35089826315289/100000000000000 : ℝ)^3397 := by
    have hnat : (894452251 : ℕ)^4421*100000000000000^3397 ≤ 35089826315289^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894452251 2000000000 35089826315289 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515858547/1250000000 : ℝ)^4421 ≤ (6320949937939/20000000000000 : ℝ)^3397 := by
    have hnat : (515858547 : ℕ)^4421*20000000000000^3397 ≤ 6320949937939^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515858547 1250000000 6320949937939 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34371691/80000000 : ℝ), (894452251/2000000000 : ℝ), (515858547/1250000000 : ℝ)] ![(33305423973379/100000000000000 : ℝ), (35089826315289/100000000000000 : ℝ), (6320949937939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34371691/80000000 : ℝ)|^4421 ≤ (33305423973379/100000000000000 : ℝ)^3397
        have hw : |(34371691/80000000 : ℝ)|=(34371691/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894452251/2000000000 : ℝ)|^4421 ≤ (35089826315289/100000000000000 : ℝ)^3397
        have hw : |(894452251/2000000000 : ℝ)|=(894452251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515858547/1250000000 : ℝ)|^4421 ≤ (6320949937939/20000000000000 : ℝ)^3397
        have hw : |(515858547/1250000000 : ℝ)|=(515858547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1461_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2851/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2851/25000 : ℝ) ^ (1105/256 : ℝ) ≤ (8508947458689241/100000000000000000000 : ℝ) := by
    have hpowers : (2851/25000 : ℝ)^1105 ≤ (8508947458689241/100000000000000000000 : ℝ)^256 := by
      have hnat : (2851 : ℕ)^1105*100000000000000000000^256 ≤ 8508947458689241^256*25000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2851 25000 8508947458689241 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2851/25000 : ℝ)) (X := (8508947458689241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (1105/256 : ℝ) ≤ (208055635338839/800000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^1105 ≤ (208055635338839/800000000000000000 : ℝ)^256 := by
      have hnat : (14773 : ℕ)^1105*800000000000000000^256 ≤ 208055635338839^256*100000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 208055635338839 800000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (208055635338839/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008508947458689241/50000000000000000000 : ℝ) ≤ (10000394234960151/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50008508947458689241/50000000000000000000 : ℝ)^256 ≤ (10000394234960151/10000000000000000 : ℝ)^1105 := by
      have hnat : (50008508947458689241 : ℕ)^256*10000000000000000^1105 ≤ 10000394234960151^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008508947458689241 50000000000000000000 10000394234960151 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000394234960151/10000000000000000 : ℝ)) (X := (50008508947458689241/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008628975469011029/25000000000000000000 : ℝ) ≤ (10000799538414439/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (25008628975469011029/25000000000000000000 : ℝ)^256 ≤ (10000799538414439/10000000000000000 : ℝ)^1105 := by
      have hnat : (25008628975469011029 : ℕ)^256*10000000000000000^1105 ≤ 10000799538414439^1105*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008628975469011029 25000000000000000000 10000799538414439 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000799538414439/10000000000000000 : ℝ)) (X := (25008628975469011029/25000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (400208055635338839/400000000000000000 : ℝ) ≤ (10001204841868727/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (400208055635338839/400000000000000000 : ℝ)^256 ≤ (10001204841868727/10000000000000000 : ℝ)^1105 := by
      have hnat : (400208055635338839 : ℕ)^256*10000000000000000^1105 ≤ 10001204841868727^1105*400000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400208055635338839 400000000000000000 10001204841868727 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001204841868727/10000000000000000 : ℝ)) (X := (400208055635338839/400000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8508947458689241/100000000000000000000 : ℝ) ≤ ((6736416803279069603/6738000000000000000 : ℝ)+2*(25331465893/21056250000000 : ℝ)*(2851/25000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (6736416803279069603/6738000000000000000 : ℝ)+2*(25331465893/21056250000000 : ℝ)*(2851/25000 : ℝ)=(10000394234960151/10000000000000000 : ℝ) by norm_num, show 1+2*(8508947458689241/100000000000000000000 : ℝ)=(50008508947458689241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(208055635338839/800000000000000000 : ℝ)+(8508947458689241/100000000000000000000 : ℝ) ≤ ((6736416803279069603/6738000000000000000 : ℝ)+(25331465893/21056250000000 : ℝ)*((14773/100000 : ℝ)+(2851/25000 : ℝ)))^(1105/256 : ℝ) := by
    rw [show (6736416803279069603/6738000000000000000 : ℝ)+(25331465893/21056250000000 : ℝ)*((14773/100000 : ℝ)+(2851/25000 : ℝ))=(10000799538414439/10000000000000000 : ℝ) by norm_num, show 1+(208055635338839/800000000000000000 : ℝ)+(8508947458689241/100000000000000000000 : ℝ)=(25008628975469011029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(208055635338839/800000000000000000 : ℝ) ≤ ((6736416803279069603/6738000000000000000 : ℝ)+2*(25331465893/21056250000000 : ℝ)*(14773/100000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (6736416803279069603/6738000000000000000 : ℝ)+2*(25331465893/21056250000000 : ℝ)*(14773/100000 : ℝ)=(10001204841868727/10000000000000000 : ℝ) by norm_num, show 1+2*(208055635338839/800000000000000000 : ℝ)=(400208055635338839/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6736416803279069603/6738000000000000000 : ℝ)*(X 1 0+X 2 0)+(25331465893/21056250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (6736416803279069603/6738000000000000000 : ℝ)) (alpha := (25331465893/21056250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6736416803279069603/6738000000000000000 : ℝ)*(X 0 1+X 2 1)+(25331465893/21056250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (6736416803279069603/6738000000000000000 : ℝ)) (alpha := (25331465893/21056250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6736416803279069603/6738000000000000000 : ℝ)*(X 0 2+X 1 2)+(25331465893/21056250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (6736416803279069603/6738000000000000000 : ℝ)) (alpha := (25331465893/21056250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336657467/2500000000 : ℝ)*X 2 0+(5247594099/10000000000 : ℝ)*X 2 1+(-2026367041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-486367873/2500000000 : ℝ)*X 0 0+(2624084509/5000000000 : ℝ)*X 0 1+(1081194899/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305179129/10000000000 : ℝ)*X 1 0+(-933993291/5000000000 : ℝ)*X 1 1+(270298727/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((331573687/625000000 : ℝ)*X 2 0+(108119493/200000000 : ℝ)*X 2 1+(-1867986617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((34371691/80000000 : ℝ)*X 0 0+(894452251/2000000000 : ℝ)*X 0 1+(515858547/1250000000 : ℝ)*X 0 2+(34371691/80000000 : ℝ)*X 1 0+(894452251/2000000000 : ℝ)*X 1 1+(515858547/1250000000 : ℝ)*X 1 2+(34371691/80000000 : ℝ)*X 2 0+(894452251/2000000000 : ℝ)*X 2 1+(515858547/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (365124738873079552208826009/112300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550817947/100000000000000 : ℝ)*(base19) + (399350219/100000000000000 : ℝ)*(base23) + (178041123/100000000000000 : ℝ)*(lower1) + (103522089/100000000000000 : ℝ)*(upper3) + (86489/1562500000000 : ℝ)*(lower4) + (17708859/50000000000000 : ℝ)*(upper5) + (4616074659152403/100000000000000 : ℝ)*(major0) + (4616074659152403/100000000000000 : ℝ)*(major1) + (4616074659152403/100000000000000 : ℝ)*(major2) + (111443577/50000000000000 : ℝ)*(sp0) + (6336900287900629/100000000000000 : ℝ)*(sp1) + (3168449868541341/50000000000000 : ℝ)*(sp2) + (1267379933132651/20000000000000 : ℝ)*(sp3) + (2895248922026383/100000000000000 : ℝ)*(sp4) + (2895248922026383/100000000000000 : ℝ)*(f.failure) + (6336900287900629/100000000000000 : ℝ)*(f.sum) + (24911279716867/5615000000000000000000000000 : ℝ)*base66 + (1020203078287462003/224600000000000000000000000000000 : ℝ)*base67 + (324324028962137997/224600000000000000000000000000000 : ℝ)*base70 + (8362214326266137997/224600000000000000000000000000000 : ℝ)*base72 + (2092085831027/5615000000000000000000000000 : ℝ)*base74 + (14990357903517137997/224600000000000000000000000000000 : ℝ)*base76 + (961309819154537997/224600000000000000000000000000000 : ℝ)*base78 + (2219729312707062003/224600000000000000000000000000000 : ℝ)*base79 + (9760472341097/5615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (51079919/10000000000000000000000 : ℝ)*base89 + (51079919/10000000000000000000000 : ℝ)*base91 + (51079919/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1461_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1461_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1461_box_0 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-893539009/5000000000 : ℝ)*x 0 + (1346219893/2500000000 : ℝ)*x 1 + (5384878931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893539009/5000000000 : ℝ)^4421 ≤ (1063427340231/10000000000000 : ℝ)^3397 := by
    have hnat : (893539009 : ℕ)^4421*10000000000000^3397 ≤ 1063427340231^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893539009 5000000000 1063427340231 10000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346219893/2500000000 : ℝ)^4421 ≤ (8936573350577/20000000000000 : ℝ)^3397 := by
    have hnat : (1346219893 : ℕ)^4421*20000000000000^3397 ≤ 8936573350577^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346219893 2500000000 8936573350577 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384878931/10000000000 : ℝ)^4421 ≤ (1396339369707/3125000000000 : ℝ)^3397 := by
    have hnat : (5384878931 : ℕ)^4421*3125000000000^3397 ≤ 1396339369707^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384878931 10000000000 1396339369707 3125000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-893539009/5000000000 : ℝ), (1346219893/2500000000 : ℝ), (5384878931/10000000000 : ℝ)] ![(1063427340231/10000000000000 : ℝ), (8936573350577/20000000000000 : ℝ), (1396339369707/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-893539009/5000000000 : ℝ)|^4421 ≤ (1063427340231/10000000000000 : ℝ)^3397
        have hw : |(-893539009/5000000000 : ℝ)|=(893539009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346219893/2500000000 : ℝ)|^4421 ≤ (8936573350577/20000000000000 : ℝ)^3397
        have hw : |(1346219893/2500000000 : ℝ)|=(1346219893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384878931/10000000000 : ℝ)|^4421 ≤ (1396339369707/3125000000000 : ℝ)^3397
        have hw : |(5384878931/10000000000 : ℝ)|=(5384878931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_1 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286257643/10000000000 : ℝ)*x 0 + (-961347601/5000000000 : ℝ)*x 1 + (1346219661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286257643/10000000000 : ℝ)^4421 ≤ (43620785253967/100000000000000 : ℝ)^3397 := by
    have hnat : (5286257643 : ℕ)^4421*100000000000000^3397 ≤ 43620785253967^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286257643 10000000000 43620785253967 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961347601/5000000000 : ℝ)^4421 ≤ (5848178998089/50000000000000 : ℝ)^3397 := by
    have hnat : (961347601 : ℕ)^4421*50000000000000^3397 ≤ 5848178998089^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961347601 5000000000 5848178998089 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346219661/2500000000 : ℝ)^4421 ≤ (8936571346253/20000000000000 : ℝ)^3397 := by
    have hnat : (1346219661 : ℕ)^4421*20000000000000^3397 ≤ 8936571346253^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346219661 2500000000 8936571346253 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286257643/10000000000 : ℝ), (-961347601/5000000000 : ℝ), (1346219661/2500000000 : ℝ)] ![(43620785253967/100000000000000 : ℝ), (5848178998089/50000000000000 : ℝ), (8936571346253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286257643/10000000000 : ℝ)|^4421 ≤ (43620785253967/100000000000000 : ℝ)^3397
        have hw : |(5286257643/10000000000 : ℝ)|=(5286257643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-961347601/5000000000 : ℝ)|^4421 ≤ (5848178998089/50000000000000 : ℝ)^3397
        have hw : |(-961347601/5000000000 : ℝ)|=(961347601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346219661/2500000000 : ℝ)|^4421 ≤ (8936571346253/20000000000000 : ℝ)^3397
        have hw : |(1346219661/2500000000 : ℝ)|=(1346219661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_2 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643128747/5000000000 : ℝ)*x 0 + (5384879351/10000000000 : ℝ)*x 1 + (-48067361/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643128747/5000000000 : ℝ)^4421 ≤ (5452597956729/12500000000000 : ℝ)^3397 := by
    have hnat : (2643128747 : ℕ)^4421*12500000000000^3397 ≤ 5452597956729^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643128747 5000000000 5452597956729 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384879351/10000000000 : ℝ)^4421 ≤ (44682864366271/100000000000000 : ℝ)^3397 := by
    have hnat : (5384879351 : ℕ)^4421*100000000000000^3397 ≤ 44682864366271^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384879351 10000000000 44682864366271 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48067361/250000000 : ℝ)^4421 ≤ (11696351963361/100000000000000 : ℝ)^3397 := by
    have hnat : (48067361 : ℕ)^4421*100000000000000^3397 ≤ 11696351963361^3397*250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48067361 250000000 11696351963361 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643128747/5000000000 : ℝ), (5384879351/10000000000 : ℝ), (-48067361/250000000 : ℝ)] ![(5452597956729/12500000000000 : ℝ), (44682864366271/100000000000000 : ℝ), (11696351963361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643128747/5000000000 : ℝ)|^4421 ≤ (5452597956729/12500000000000 : ℝ)^3397
        have hw : |(2643128747/5000000000 : ℝ)|=(2643128747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384879351/10000000000 : ℝ)|^4421 ≤ (44682864366271/100000000000000 : ℝ)^3397
        have hw : |(5384879351/10000000000 : ℝ)|=(5384879351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48067361/250000000 : ℝ)|^4421 ≤ (11696351963361/100000000000000 : ℝ)^3397
        have hw : |(-48067361/250000000 : ℝ)|=(48067361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_3 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1110527811/2500000000 : ℝ)*x 0 + (845449593/2000000000 : ℝ)*x 1 + (4227248457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110527811/2500000000 : ℝ)^4421 ≤ (869556756337/2500000000000 : ℝ)^3397 := by
    have hnat : (1110527811 : ℕ)^4421*2500000000000^3397 ≤ 869556756337^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110527811 2500000000 869556756337 2500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845449593/2000000000 : ℝ)^4421 ≤ (2038053899717/6250000000000 : ℝ)^3397 := by
    have hnat : (845449593 : ℕ)^4421*6250000000000^3397 ≤ 2038053899717^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845449593 2000000000 2038053899717 6250000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227248457/10000000000 : ℝ)^4421 ≤ (16304433667401/50000000000000 : ℝ)^3397 := by
    have hnat : (4227248457 : ℕ)^4421*50000000000000^3397 ≤ 16304433667401^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227248457 10000000000 16304433667401 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1110527811/2500000000 : ℝ), (845449593/2000000000 : ℝ), (4227248457/10000000000 : ℝ)] ![(869556756337/2500000000000 : ℝ), (2038053899717/6250000000000 : ℝ), (16304433667401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1110527811/2500000000 : ℝ)|^4421 ≤ (869556756337/2500000000000 : ℝ)^3397
        have hw : |(1110527811/2500000000 : ℝ)|=(1110527811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845449593/2000000000 : ℝ)|^4421 ≤ (2038053899717/6250000000000 : ℝ)^3397
        have hw : |(845449593/2000000000 : ℝ)|=(845449593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227248457/10000000000 : ℝ)|^4421 ≤ (16304433667401/50000000000000 : ℝ)^3397
        have hw : |(4227248457/10000000000 : ℝ)|=(4227248457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_4 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106576283/10000000000 : ℝ)*x 0 + (1053391931/2000000000 : ℝ)*x 1 + (2633479559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106576283/10000000000 : ℝ)^4421 ≤ (411646724053/3125000000000 : ℝ)^3397 := by
    have hnat : (2106576283 : ℕ)^4421*3125000000000^3397 ≤ 411646724053^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106576283 10000000000 411646724053 3125000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053391931/2000000000 : ℝ)^4421 ≤ (542670691149/1250000000000 : ℝ)^3397 := by
    have hnat : (1053391931 : ℕ)^4421*1250000000000^3397 ≤ 542670691149^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053391931 2000000000 542670691149 1250000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633479559/5000000000 : ℝ)^4421 ≤ (10853412382837/25000000000000 : ℝ)^3397 := by
    have hnat : (2633479559 : ℕ)^4421*25000000000000^3397 ≤ 10853412382837^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633479559 5000000000 10853412382837 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106576283/10000000000 : ℝ), (1053391931/2000000000 : ℝ), (2633479559/5000000000 : ℝ)] ![(411646724053/3125000000000 : ℝ), (542670691149/1250000000000 : ℝ), (10853412382837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106576283/10000000000 : ℝ)|^4421 ≤ (411646724053/3125000000000 : ℝ)^3397
        have hw : |(-2106576283/10000000000 : ℝ)|=(2106576283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053391931/2000000000 : ℝ)|^4421 ≤ (542670691149/1250000000000 : ℝ)^3397
        have hw : |(1053391931/2000000000 : ℝ)|=(1053391931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633479559/5000000000 : ℝ)|^4421 ≤ (10853412382837/25000000000000 : ℝ)^3397
        have hw : |(2633479559/5000000000 : ℝ)|=(2633479559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_5 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368676691/10000000000 : ℝ)*x 0 + (-1970767649/10000000000 : ℝ)*x 1 + (2633479759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368676691/10000000000 : ℝ)^4421 ≤ (11126992162123/25000000000000 : ℝ)^3397 := by
    have hnat : (5368676691 : ℕ)^4421*25000000000000^3397 ≤ 11126992162123^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368676691 10000000000 11126992162123 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1970767649/10000000000 : ℝ)^4421 ≤ (6039188754141/50000000000000 : ℝ)^3397 := by
    have hnat : (1970767649 : ℕ)^4421*50000000000000^3397 ≤ 6039188754141^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970767649 10000000000 6039188754141 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633479759/5000000000 : ℝ)^4421 ≤ (43413653822277/100000000000000 : ℝ)^3397 := by
    have hnat : (2633479759 : ℕ)^4421*100000000000000^3397 ≤ 43413653822277^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633479759 5000000000 43413653822277 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368676691/10000000000 : ℝ), (-1970767649/10000000000 : ℝ), (2633479759/5000000000 : ℝ)] ![(11126992162123/25000000000000 : ℝ), (6039188754141/50000000000000 : ℝ), (43413653822277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368676691/10000000000 : ℝ)|^4421 ≤ (11126992162123/25000000000000 : ℝ)^3397
        have hw : |(5368676691/10000000000 : ℝ)|=(5368676691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1970767649/10000000000 : ℝ)|^4421 ≤ (6039188754141/50000000000000 : ℝ)^3397
        have hw : |(-1970767649/10000000000 : ℝ)|=(1970767649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633479759/5000000000 : ℝ)|^4421 ≤ (43413653822277/100000000000000 : ℝ)^3397
        have hw : |(2633479759/5000000000 : ℝ)|=(2633479759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_6 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368676371/10000000000 : ℝ)*x 0 + (5266959459/10000000000 : ℝ)*x 1 + (-985384081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368676371/10000000000 : ℝ)^4421 ≤ (22253982597949/50000000000000 : ℝ)^3397 := by
    have hnat : (5368676371 : ℕ)^4421*50000000000000^3397 ≤ 22253982597949^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368676371 10000000000 22253982597949 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266959459/10000000000 : ℝ)^4421 ≤ (8682730637873/20000000000000 : ℝ)^3397 := by
    have hnat : (5266959459 : ℕ)^4421*20000000000000^3397 ≤ 8682730637873^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266959459 10000000000 8682730637873 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985384081/5000000000 : ℝ)^4421 ≤ (3019595400023/25000000000000 : ℝ)^3397 := by
    have hnat : (985384081 : ℕ)^4421*25000000000000^3397 ≤ 3019595400023^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985384081 5000000000 3019595400023 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368676371/10000000000 : ℝ), (5266959459/10000000000 : ℝ), (-985384081/5000000000 : ℝ)] ![(22253982597949/50000000000000 : ℝ), (8682730637873/20000000000000 : ℝ), (3019595400023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368676371/10000000000 : ℝ)|^4421 ≤ (22253982597949/50000000000000 : ℝ)^3397
        have hw : |(5368676371/10000000000 : ℝ)|=(5368676371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266959459/10000000000 : ℝ)|^4421 ≤ (8682730637873/20000000000000 : ℝ)^3397
        have hw : |(5266959459/10000000000 : ℝ)|=(5266959459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985384081/5000000000 : ℝ)|^4421 ≤ (3019595400023/25000000000000 : ℝ)^3397
        have hw : |(-985384081/5000000000 : ℝ)|=(985384081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_7 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4149672623/10000000000 : ℝ)*x 0 + (874683509/2000000000 : ℝ)*x 1 + (4373417503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4149672623/10000000000 : ℝ)^4421 ≤ (6366444923081/20000000000000 : ℝ)^3397 := by
    have hnat : (4149672623 : ℕ)^4421*20000000000000^3397 ≤ 6366444923081^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149672623 10000000000 6366444923081 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874683509/2000000000 : ℝ)^4421 ≤ (272671103163/800000000000 : ℝ)^3397 := by
    have hnat : (874683509 : ℕ)^4421*800000000000^3397 ≤ 272671103163^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874683509 2000000000 272671103163 800000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4373417503/10000000000 : ℝ)^4421 ≤ (17041943734691/50000000000000 : ℝ)^3397 := by
    have hnat : (4373417503 : ℕ)^4421*50000000000000^3397 ≤ 17041943734691^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373417503 10000000000 17041943734691 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4149672623/10000000000 : ℝ), (874683509/2000000000 : ℝ), (4373417503/10000000000 : ℝ)] ![(6366444923081/20000000000000 : ℝ), (272671103163/800000000000 : ℝ), (17041943734691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4149672623/10000000000 : ℝ)|^4421 ≤ (6366444923081/20000000000000 : ℝ)^3397
        have hw : |(4149672623/10000000000 : ℝ)|=(4149672623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874683509/2000000000 : ℝ)|^4421 ≤ (272671103163/800000000000 : ℝ)^3397
        have hw : |(874683509/2000000000 : ℝ)|=(874683509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4373417503/10000000000 : ℝ)|^4421 ≤ (17041943734691/50000000000000 : ℝ)^3397
        have hw : |(4373417503/10000000000 : ℝ)|=(4373417503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_8 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039213347/10000000000 : ℝ)*x 0 + (5185255421/10000000000 : ℝ)*x 1 + (1079766471/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039213347/10000000000 : ℝ)^4421 ≤ (12627151741843/100000000000000 : ℝ)^3397 := by
    have hnat : (2039213347 : ℕ)^4421*100000000000000^3397 ≤ 12627151741843^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039213347 10000000000 12627151741843 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185255421/10000000000 : ℝ)^4421 ≤ (21269622169919/50000000000000 : ℝ)^3397 := by
    have hnat : (5185255421 : ℕ)^4421*50000000000000^3397 ≤ 21269622169919^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185255421 10000000000 21269622169919 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079766471/2000000000 : ℝ)^4421 ≤ (44833603907537/100000000000000 : ℝ)^3397 := by
    have hnat : (1079766471 : ℕ)^4421*100000000000000^3397 ≤ 44833603907537^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079766471 2000000000 44833603907537 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039213347/10000000000 : ℝ), (5185255421/10000000000 : ℝ), (1079766471/2000000000 : ℝ)] ![(12627151741843/100000000000000 : ℝ), (21269622169919/50000000000000 : ℝ), (44833603907537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039213347/10000000000 : ℝ)|^4421 ≤ (12627151741843/100000000000000 : ℝ)^3397
        have hw : |(-2039213347/10000000000 : ℝ)|=(2039213347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185255421/10000000000 : ℝ)|^4421 ≤ (21269622169919/50000000000000 : ℝ)^3397
        have hw : |(5185255421/10000000000 : ℝ)|=(5185255421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079766471/2000000000 : ℝ)|^4421 ≤ (44833603907537/100000000000000 : ℝ)^3397
        have hw : |(1079766471/2000000000 : ℝ)|=(1079766471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_9 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055300191/2000000000 : ℝ)*x 0 + (-1916882099/10000000000 : ℝ)*x 1 + (5398832733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055300191/2000000000 : ℝ)^4421 ≤ (43516035826683/100000000000000 : ℝ)^3397 := by
    have hnat : (1055300191 : ℕ)^4421*100000000000000^3397 ≤ 43516035826683^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055300191 2000000000 43516035826683 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916882099/10000000000 : ℝ)^4421 ≤ (5825178083199/50000000000000 : ℝ)^3397 := by
    have hnat : (1916882099 : ℕ)^4421*50000000000000^3397 ≤ 5825178083199^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916882099 10000000000 5825178083199 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398832733/10000000000 : ℝ)^4421 ≤ (8966721598561/20000000000000 : ℝ)^3397 := by
    have hnat : (5398832733 : ℕ)^4421*20000000000000^3397 ≤ 8966721598561^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398832733 10000000000 8966721598561 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055300191/2000000000 : ℝ), (-1916882099/10000000000 : ℝ), (5398832733/10000000000 : ℝ)] ![(43516035826683/100000000000000 : ℝ), (5825178083199/50000000000000 : ℝ), (8966721598561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055300191/2000000000 : ℝ)|^4421 ≤ (43516035826683/100000000000000 : ℝ)^3397
        have hw : |(1055300191/2000000000 : ℝ)|=(1055300191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916882099/10000000000 : ℝ)|^4421 ≤ (5825178083199/50000000000000 : ℝ)^3397
        have hw : |(-1916882099/10000000000 : ℝ)|=(1916882099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398832733/10000000000 : ℝ)|^4421 ≤ (8966721598561/20000000000000 : ℝ)^3397
        have hw : |(5398832733/10000000000 : ℝ)|=(5398832733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_10 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319125243/2500000000 : ℝ)*x 0 + (5398832799/10000000000 : ℝ)*x 1 + (-383376397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319125243/2500000000 : ℝ)^4421 ≤ (43516036009147/100000000000000 : ℝ)^3397 := by
    have hnat : (1319125243 : ℕ)^4421*100000000000000^3397 ≤ 43516036009147^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319125243 2500000000 43516036009147 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398832799/10000000000 : ℝ)^4421 ≤ (22416804353053/50000000000000 : ℝ)^3397 := by
    have hnat : (5398832799 : ℕ)^4421*50000000000000^3397 ≤ 22416804353053^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398832799 10000000000 22416804353053 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383376397/2000000000 : ℝ)^4421 ≤ (5825177632337/50000000000000 : ℝ)^3397 := by
    have hnat : (383376397 : ℕ)^4421*50000000000000^3397 ≤ 5825177632337^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383376397 2000000000 5825177632337 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319125243/2500000000 : ℝ), (5398832799/10000000000 : ℝ), (-383376397/2000000000 : ℝ)] ![(43516036009147/100000000000000 : ℝ), (22416804353053/50000000000000 : ℝ), (5825177632337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319125243/2500000000 : ℝ)|^4421 ≤ (43516036009147/100000000000000 : ℝ)^3397
        have hw : |(1319125243/2500000000 : ℝ)|=(1319125243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398832799/10000000000 : ℝ)|^4421 ≤ (22416804353053/50000000000000 : ℝ)^3397
        have hw : |(5398832799/10000000000 : ℝ)|=(5398832799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383376397/2000000000 : ℝ)|^4421 ≤ (5825177632337/50000000000000 : ℝ)^3397
        have hw : |(-383376397/2000000000 : ℝ)|=(383376397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_11 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238079509/5000000000 : ℝ)*x 0 + (2104968829/5000000000 : ℝ)*x 1 + (2104968539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238079509/5000000000 : ℝ)^4421 ≤ (35129632585173/100000000000000 : ℝ)^3397 := by
    have hnat : (2238079509 : ℕ)^4421*100000000000000^3397 ≤ 35129632585173^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238079509 5000000000 35129632585173 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104968829/5000000000 : ℝ)^4421 ≤ (2027199162921/6250000000000 : ℝ)^3397 := by
    have hnat : (2104968829 : ℕ)^4421*6250000000000^3397 ≤ 2027199162921^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104968829 5000000000 2027199162921 6250000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104968539/5000000000 : ℝ)^4421 ≤ (32435180791147/100000000000000 : ℝ)^3397 := by
    have hnat : (2104968539 : ℕ)^4421*100000000000000^3397 ≤ 32435180791147^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104968539 5000000000 32435180791147 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238079509/5000000000 : ℝ), (2104968829/5000000000 : ℝ), (2104968539/5000000000 : ℝ)] ![(35129632585173/100000000000000 : ℝ), (2027199162921/6250000000000 : ℝ), (32435180791147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238079509/5000000000 : ℝ)|^4421 ≤ (35129632585173/100000000000000 : ℝ)^3397
        have hw : |(2238079509/5000000000 : ℝ)|=(2238079509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2104968829/5000000000 : ℝ)|^4421 ≤ (2027199162921/6250000000000 : ℝ)^3397
        have hw : |(2104968829/5000000000 : ℝ)|=(2104968829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2104968539/5000000000 : ℝ)|^4421 ≤ (32435180791147/100000000000000 : ℝ)^3397
        have hw : |(2104968539/5000000000 : ℝ)|=(2104968539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_12 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-927284483/5000000000 : ℝ)*x 0 + (2732310213/5000000000 : ℝ)*x 1 + (2627909407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927284483/5000000000 : ℝ)^4421 ≤ (2231980304003/20000000000000 : ℝ)^3397 := by
    have hnat : (927284483 : ℕ)^4421*20000000000000^3397 ≤ 2231980304003^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927284483 5000000000 2231980304003 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732310213/5000000000 : ℝ)^4421 ≤ (45545916444999/100000000000000 : ℝ)^3397 := by
    have hnat : (2732310213 : ℕ)^4421*100000000000000^3397 ≤ 45545916444999^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732310213 5000000000 45545916444999 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627909407/5000000000 : ℝ)^4421 ≤ (43294182019833/100000000000000 : ℝ)^3397 := by
    have hnat : (2627909407 : ℕ)^4421*100000000000000^3397 ≤ 43294182019833^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627909407 5000000000 43294182019833 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927284483/5000000000 : ℝ), (2732310213/5000000000 : ℝ), (2627909407/5000000000 : ℝ)] ![(2231980304003/20000000000000 : ℝ), (45545916444999/100000000000000 : ℝ), (43294182019833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927284483/5000000000 : ℝ)|^4421 ≤ (2231980304003/20000000000000 : ℝ)^3397
        have hw : |(-927284483/5000000000 : ℝ)|=(927284483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732310213/5000000000 : ℝ)|^4421 ≤ (45545916444999/100000000000000 : ℝ)^3397
        have hw : |(2732310213/5000000000 : ℝ)|=(2732310213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627909407/5000000000 : ℝ)|^4421 ≤ (43294182019833/100000000000000 : ℝ)^3397
        have hw : |(2627909407/5000000000 : ℝ)|=(2627909407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_13 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672057703/1250000000 : ℝ)*x 0 + (-395042227/2000000000 : ℝ)*x 1 + (2627909627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672057703/1250000000 : ℝ)^4421 ≤ (44591981407029/100000000000000 : ℝ)^3397 := by
    have hnat : (672057703 : ℕ)^4421*100000000000000^3397 ≤ 44591981407029^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672057703 1250000000 44591981407029 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395042227/2000000000 : ℝ)^4421 ≤ (6056915925693/50000000000000 : ℝ)^3397 := by
    have hnat : (395042227 : ℕ)^4421*50000000000000^3397 ≤ 6056915925693^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395042227 2000000000 6056915925693 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627909627/5000000000 : ℝ)^4421 ≤ (10823546684211/25000000000000 : ℝ)^3397 := by
    have hnat : (2627909627 : ℕ)^4421*25000000000000^3397 ≤ 10823546684211^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627909627 5000000000 10823546684211 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672057703/1250000000 : ℝ), (-395042227/2000000000 : ℝ), (2627909627/5000000000 : ℝ)] ![(44591981407029/100000000000000 : ℝ), (6056915925693/50000000000000 : ℝ), (10823546684211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672057703/1250000000 : ℝ)|^4421 ≤ (44591981407029/100000000000000 : ℝ)^3397
        have hw : |(672057703/1250000000 : ℝ)|=(672057703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395042227/2000000000 : ℝ)|^4421 ≤ (6056915925693/50000000000000 : ℝ)^3397
        have hw : |(-395042227/2000000000 : ℝ)|=(395042227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627909627/5000000000 : ℝ)|^4421 ≤ (10823546684211/25000000000000 : ℝ)^3397
        have hw : |(2627909627/5000000000 : ℝ)|=(2627909627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_14 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672057737/1250000000 : ℝ)*x 0 + (5255818879/10000000000 : ℝ)*x 1 + (-197521127/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672057737/1250000000 : ℝ)^4421 ≤ (5573998042877/12500000000000 : ℝ)^3397 := by
    have hnat : (672057737 : ℕ)^4421*12500000000000^3397 ≤ 5573998042877^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672057737 1250000000 5573998042877 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255818879/10000000000 : ℝ)^4421 ≤ (8658836543333/20000000000000 : ℝ)^3397 := by
    have hnat : (5255818879 : ℕ)^4421*20000000000000^3397 ≤ 8658836543333^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255818879 10000000000 8658836543333 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197521127/1000000000 : ℝ)^4421 ≤ (1211383292891/10000000000000 : ℝ)^3397 := by
    have hnat : (197521127 : ℕ)^4421*10000000000000^3397 ≤ 1211383292891^3397*1000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197521127 1000000000 1211383292891 10000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672057737/1250000000 : ℝ), (5255818879/10000000000 : ℝ), (-197521127/1000000000 : ℝ)] ![(5573998042877/12500000000000 : ℝ), (8658836543333/20000000000000 : ℝ), (1211383292891/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672057737/1250000000 : ℝ)|^4421 ≤ (5573998042877/12500000000000 : ℝ)^3397
        have hw : |(672057737/1250000000 : ℝ)|=(672057737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255818879/10000000000 : ℝ)|^4421 ≤ (8658836543333/20000000000000 : ℝ)^3397
        have hw : |(5255818879/10000000000 : ℝ)|=(5255818879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197521127/1000000000 : ℝ)|^4421 ≤ (1211383292891/10000000000000 : ℝ)^3397
        have hw : |(-197521127/1000000000 : ℝ)|=(197521127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_box_15 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2060797551/5000000000 : ℝ)*x 0 + (4387215161/10000000000 : ℝ)*x 1 + (438721509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060797551/5000000000 : ℝ)^4421 ≤ (15776101015547/50000000000000 : ℝ)^3397 := by
    have hnat : (2060797551 : ℕ)^4421*50000000000000^3397 ≤ 15776101015547^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060797551 5000000000 15776101015547 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387215161/10000000000 : ℝ)^4421 ≤ (8555974833431/25000000000000 : ℝ)^3397 := by
    have hnat : (4387215161 : ℕ)^4421*25000000000000^3397 ≤ 8555974833431^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387215161 10000000000 8555974833431 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438721509/1000000000 : ℝ)^4421 ≤ (34223898612909/100000000000000 : ℝ)^3397 := by
    have hnat : (438721509 : ℕ)^4421*100000000000000^3397 ≤ 34223898612909^3397*1000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438721509 1000000000 34223898612909 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2060797551/5000000000 : ℝ), (4387215161/10000000000 : ℝ), (438721509/1000000000 : ℝ)] ![(15776101015547/50000000000000 : ℝ), (8555974833431/25000000000000 : ℝ), (34223898612909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2060797551/5000000000 : ℝ)|^4421 ≤ (15776101015547/50000000000000 : ℝ)^3397
        have hw : |(2060797551/5000000000 : ℝ)|=(2060797551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387215161/10000000000 : ℝ)|^4421 ≤ (8555974833431/25000000000000 : ℝ)^3397
        have hw : |(4387215161/10000000000 : ℝ)|=(4387215161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438721509/1000000000 : ℝ)|^4421 ≤ (34223898612909/100000000000000 : ℝ)^3397
        have hw : |(438721509/1000000000 : ℝ)|=(438721509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1461_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1573/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29589/50000 : ℝ) ∧ (80623/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21201/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2851/25000 : ℝ) ^ (1105/256 : ℝ) ≤ (8508947458689241/100000000000000000000 : ℝ) := by
    have hpowers : (2851/25000 : ℝ)^1105 ≤ (8508947458689241/100000000000000000000 : ℝ)^256 := by
      have hnat : (2851 : ℕ)^1105*100000000000000000000^256 ≤ 8508947458689241^256*25000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2851 25000 8508947458689241 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2851/25000 : ℝ)) (X := (8508947458689241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (1105/256 : ℝ) ≤ (25999356503528949/100000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^1105 ≤ (25999356503528949/100000000000000000000 : ℝ)^256 := by
      have hnat : (3693 : ℕ)^1105*100000000000000000000^256 ≤ 25999356503528949^256*25000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 25999356503528949 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (25999356503528949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008508947458689241/50000000000000000000 : ℝ) ≤ (10000394234960151/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50008508947458689241/50000000000000000000 : ℝ)^256 ≤ (10000394234960151/10000000000000000 : ℝ)^1105 := by
      have hnat : (50008508947458689241 : ℕ)^256*10000000000000000^1105 ≤ 10000394234960151^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008508947458689241 50000000000000000000 10000394234960151 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000394234960151/10000000000000000 : ℝ)) (X := (50008508947458689241/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003450830396221819/10000000000000000000 : ℝ) ≤ (10000799362437033/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (10003450830396221819/10000000000000000000 : ℝ)^256 ≤ (10000799362437033/10000000000000000 : ℝ)^1105 := by
      have hnat : (10003450830396221819 : ℕ)^256*10000000000000000^1105 ≤ 10000799362437033^1105*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003450830396221819 10000000000000000000 10000799362437033 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000799362437033/10000000000000000 : ℝ)) (X := (10003450830396221819/10000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025999356503528949/50000000000000000000 : ℝ) ≤ (2000240897982783/2000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50025999356503528949/50000000000000000000 : ℝ)^256 ≤ (2000240897982783/2000000000000000 : ℝ)^1105 := by
      have hnat : (50025999356503528949 : ℕ)^256*2000000000000000^1105 ≤ 2000240897982783^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025999356503528949 50000000000000000000 2000240897982783 2000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000240897982783/2000000000000000 : ℝ)) (X := (50025999356503528949/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8508947458689241/100000000000000000000 : ℝ) ≤ ((4209010954481632989/4210000000000000000 : ℝ)+2*(202563738441/168400000000000 : ℝ)*(2851/25000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (4209010954481632989/4210000000000000000 : ℝ)+2*(202563738441/168400000000000 : ℝ)*(2851/25000 : ℝ)=(10000394234960151/10000000000000000 : ℝ) by norm_num, show 1+2*(8508947458689241/100000000000000000000 : ℝ)=(50008508947458689241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25999356503528949/100000000000000000000 : ℝ)+(8508947458689241/100000000000000000000 : ℝ) ≤ ((4209010954481632989/4210000000000000000 : ℝ)+(202563738441/168400000000000 : ℝ)*((3693/25000 : ℝ)+(2851/25000 : ℝ)))^(1105/256 : ℝ) := by
    rw [show (4209010954481632989/4210000000000000000 : ℝ)+(202563738441/168400000000000 : ℝ)*((3693/25000 : ℝ)+(2851/25000 : ℝ))=(10000799362437033/10000000000000000 : ℝ) by norm_num, show 1+(25999356503528949/100000000000000000000 : ℝ)+(8508947458689241/100000000000000000000 : ℝ)=(10003450830396221819/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25999356503528949/100000000000000000000 : ℝ) ≤ ((4209010954481632989/4210000000000000000 : ℝ)+2*(202563738441/168400000000000 : ℝ)*(3693/25000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (4209010954481632989/4210000000000000000 : ℝ)+2*(202563738441/168400000000000 : ℝ)*(3693/25000 : ℝ)=(2000240897982783/2000000000000000 : ℝ) by norm_num, show 1+2*(25999356503528949/100000000000000000000 : ℝ)=(50025999356503528949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4209010954481632989/4210000000000000000 : ℝ)*(X 1 0+X 2 0)+(202563738441/168400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (4209010954481632989/4210000000000000000 : ℝ)) (alpha := (202563738441/168400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4209010954481632989/4210000000000000000 : ℝ)*(X 0 1+X 2 1)+(202563738441/168400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (4209010954481632989/4210000000000000000 : ℝ)) (alpha := (202563738441/168400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4209010954481632989/4210000000000000000 : ℝ)*(X 0 2+X 1 2)+(202563738441/168400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (4209010954481632989/4210000000000000000 : ℝ)) (alpha := (202563738441/168400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-893539009/5000000000 : ℝ)*X 0 0+(1346219893/2500000000 : ℝ)*X 0 1+(5384878931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286257643/10000000000 : ℝ)*X 1 0+(-961347601/5000000000 : ℝ)*X 1 1+(1346219661/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2643128747/5000000000 : ℝ)*X 2 0+(5384879351/10000000000 : ℝ)*X 2 1+(-48067361/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1110527811/2500000000 : ℝ)*X 0 0+(845449593/2000000000 : ℝ)*X 0 1+(4227248457/10000000000 : ℝ)*X 0 2+(1110527811/2500000000 : ℝ)*X 1 0+(845449593/2000000000 : ℝ)*X 1 1+(4227248457/10000000000 : ℝ)*X 1 2+(1110527811/2500000000 : ℝ)*X 2 0+(845449593/2000000000 : ℝ)*X 2 1+(4227248457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2106576283/10000000000 : ℝ)*X 0 0+(1053391931/2000000000 : ℝ)*X 0 1+(2633479559/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5368676691/10000000000 : ℝ)*X 1 0+(-1970767649/10000000000 : ℝ)*X 1 1+(2633479759/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5368676371/10000000000 : ℝ)*X 2 0+(5266959459/10000000000 : ℝ)*X 2 1+(-985384081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4149672623/10000000000 : ℝ)*X 0 0+(874683509/2000000000 : ℝ)*X 0 1+(4373417503/10000000000 : ℝ)*X 0 2+(4149672623/10000000000 : ℝ)*X 1 0+(874683509/2000000000 : ℝ)*X 1 1+(4373417503/10000000000 : ℝ)*X 1 2+(4149672623/10000000000 : ℝ)*X 2 0+(874683509/2000000000 : ℝ)*X 2 1+(4373417503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2039213347/10000000000 : ℝ)*X 0 0+(5185255421/10000000000 : ℝ)*X 0 1+(1079766471/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055300191/2000000000 : ℝ)*X 1 0+(-1916882099/10000000000 : ℝ)*X 1 1+(5398832733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319125243/2500000000 : ℝ)*X 2 0+(5398832799/10000000000 : ℝ)*X 2 1+(-383376397/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2238079509/5000000000 : ℝ)*X 0 0+(2104968829/5000000000 : ℝ)*X 0 1+(2104968539/5000000000 : ℝ)*X 0 2+(2238079509/5000000000 : ℝ)*X 1 0+(2104968829/5000000000 : ℝ)*X 1 1+(2104968539/5000000000 : ℝ)*X 1 2+(2238079509/5000000000 : ℝ)*X 2 0+(2104968829/5000000000 : ℝ)*X 2 1+(2104968539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-927284483/5000000000 : ℝ)*X 0 0+(2732310213/5000000000 : ℝ)*X 0 1+(2627909407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672057703/1250000000 : ℝ)*X 1 0+(-395042227/2000000000 : ℝ)*X 1 1+(2627909627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672057737/1250000000 : ℝ)*X 2 0+(5255818879/10000000000 : ℝ)*X 2 1+(-197521127/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2060797551/5000000000 : ℝ)*X 0 0+(4387215161/10000000000 : ℝ)*X 0 1+(438721509/1000000000 : ℝ)*X 0 2+(2060797551/5000000000 : ℝ)*X 1 0+(4387215161/10000000000 : ℝ)*X 1 1+(438721509/1000000000 : ℝ)*X 1 2+(2060797551/5000000000 : ℝ)*X 2 0+(4387215161/10000000000 : ℝ)*X 2 1+(438721509/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1573/2500 : ℝ) ≤ (-66221047726770634690151201282157/105250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2601579/25000000000000 : ℝ)*(upper1) + (3612081/2500000000000 : ℝ)*(upper2) + (201414819/100000000000000 : ℝ)*(upper3) + (46546383/100000000000000 : ℝ)*(lower4) + (20649107/100000000000000 : ℝ)*(upper5) + (1525762648711143/50000000000000 : ℝ)*(major0) + (1525762648711143/50000000000000 : ℝ)*(major1) + (1525762648711143/50000000000000 : ℝ)*(major2) + (479258251/25000000000000 : ℝ)*(sp1) + (4374435307/50000000000000 : ℝ)*(sp2) + (421007554715061/10000000000000 : ℝ)*(sp4) + (2105036815058803/50000000000000 : ℝ)*(sp5) + (1052516699569999/25000000000000 : ℝ)*(sp6) + (956973833859131/50000000000000 : ℝ)*(sp7) + (956973833859131/50000000000000 : ℝ)*(f.failure) + (421007554715061/10000000000000 : ℝ)*(f.sum) + (9479032458903/4210000000000000000000000000 : ℝ)*base65 + (2015486424067728573/210500000000000000000000000000000 : ℝ)*base68 + (1216334841240728573/210500000000000000000000000000000 : ℝ)*base70 + (2316704810009728573/210500000000000000000000000000000 : ℝ)*base72 + (14246549741583/4210000000000000000000000000 : ℝ)*base73 + (10732003866332728573/210500000000000000000000000000000 : ℝ)*base76 + (2119231500206728573/210500000000000000000000000000000 : ℝ)*base78 + (2159328258011728573/210500000000000000000000000000000 : ℝ)*base80 + (105725544865477/4210000000000000000000000000 : ℝ)*base82 + (44928283/5000000000000000000000 : ℝ)*base89 + (44928283/5000000000000000000000 : ℝ)*base91 + (44928283/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29589/50000 : ℝ) ≤ (49829850369440451898683789/84200000000000000000000000 : ℝ) := by norm_num
    linear_combination (8975499/25000000000000 : ℝ)*(upper0) + (190741959/100000000000000 : ℝ)*(lower1) + (10636671/4000000000000 : ℝ)*(upper4) + (39052649761689/1250000000000 : ℝ)*(major0) + (39052649761689/1250000000000 : ℝ)*(major1) + (39052649761689/1250000000000 : ℝ)*(major2) + (1067287387042599/25000000000000 : ℝ)*(sp0) + (533615631301679/12500000000000 : ℝ)*(sp1) + (4269147480196719/100000000000000 : ℝ)*(sp2) + (979765958644513/50000000000000 : ℝ)*(sp3) + (12205995669/100000000000000 : ℝ)*(sp6) + (5576769879/100000000000000 : ℝ)*(sp7) + (1267252749/12500000000000 : ℝ)*(sp8) + (234635778957/100000000000000 : ℝ)*(sp9) + (391907498811781/20000000000000 : ℝ)*(f.failure) + (1067289921548097/25000000000000 : ℝ)*(f.sum) + (480323283007/421000000000000000000000000 : ℝ)*base65 + (42110256711120921/5262500000000000000000000000000 : ℝ)*base67 + (28687858057545921/5262500000000000000000000000000 : ℝ)*base69 + (1300986641916579/5262500000000000000000000000000 : ℝ)*base72 + (591556337149/210500000000000000000000000 : ℝ)*base73 + (14581826518866579/5262500000000000000000000000000 : ℝ)*base76 + (19236789636158421/5262500000000000000000000000000 : ℝ)*base77 + (17265811384079079/5262500000000000000000000000000 : ℝ)*base80 + (504015580581/84200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13810267/2000000000000000000000 : ℝ)*base90 + (13810267/2000000000000000000000 : ℝ)*base92 + (13810267/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80623/100000 : ℝ) ≤ (678867000947122038255501639/842000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4261977/20000000000000 : ℝ)*(upper1) + (14579023/100000000000000 : ℝ)*(upper3) + (103747863/100000000000000 : ℝ)*(upper4) + (9257367/10000000000000 : ℝ)*(lower5) + (343026262100759/10000000000000 : ℝ)*(major0) + (343026262100759/10000000000000 : ℝ)*(major1) + (343026262100759/10000000000000 : ℝ)*(major2) + (16457210219/12500000000000 : ℝ)*(sp1) + (14364909803/6250000000000 : ℝ)*(sp2) + (3651612461/6250000000000 : ℝ)*(sp3) + (4682154499076433/100000000000000 : ℝ)*(sp8) + (4682022841394681/100000000000000 : ℝ)*(sp9) + (936384932103917/20000000000000 : ℝ)*(sp10) + (10757185694773/500000000000 : ℝ)*(sp11) + (268936945594247/12500000000000 : ℝ)*(f.failure) + (4682154499076433/100000000000000 : ℝ)*(f.sum) + (2703519500013/842000000000000000000000000 : ℝ)*base65 + (85063774784986349/42100000000000000000000000000000 : ℝ)*base68 + (415445383685613651/42100000000000000000000000000000 : ℝ)*base69 + (308115387380813651/42100000000000000000000000000000 : ℝ)*base71 + (371504084839/168400000000000000000000000 : ℝ)*base74 + (87641522420986349/42100000000000000000000000000000 : ℝ)*base76 + (77626058005286349/42100000000000000000000000000000 : ℝ)*base78 + (57734340798013651/42100000000000000000000000000000 : ℝ)*base79 + (703562699013/168400000000000000000000000 : ℝ)*base81 + (10618329/1250000000000000000000 : ℝ)*base90 + (10618329/1250000000000000000000 : ℝ)*base92 + (10618329/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21201/25000 : ℝ) ≤ (-89253481957529977100303908371963/105250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13708421/10000000000000 : ℝ)*(upper3) + (15644811/100000000000000 : ℝ)*(upper4) + (61195741/50000000000000 : ℝ)*(upper5) + (1734053757761789/50000000000000 : ℝ)*(major0) + (1734053757761789/50000000000000 : ℝ)*(major1) + (1734053757761789/50000000000000 : ℝ)*(major2) + (7443234023/50000000000000 : ℝ)*(sp0) + (21270976173/20000000000000 : ℝ)*(sp5) + (31696537641/12500000000000 : ℝ)*(sp6) + (1082537701/12500000000000 : ℝ)*(sp7) + (149663594172539/3125000000000 : ℝ)*(sp12) + (478914354510843/10000000000000 : ℝ)*(sp13) + (4788996327688167/100000000000000 : ℝ)*(sp14) + (2175223606768127/100000000000000 : ℝ)*(sp15) + (1087616133534867/50000000000000 : ℝ)*(f.failure) + (2394624949994647/50000000000000 : ℝ)*(f.sum) + (3368175101129/4210000000000000000000000000 : ℝ)*base65 + (2256001986206282321/210500000000000000000000000000000 : ℝ)*base67 + (1714064224263782321/210500000000000000000000000000000 : ℝ)*base69 + (1368775598056717679/210500000000000000000000000000000 : ℝ)*base72 + (1893024654829/4210000000000000000000000000 : ℝ)*base73 + (863173632147782321/210500000000000000000000000000000 : ℝ)*base75 + (277232707449217679/210500000000000000000000000000000 : ℝ)*base78 + (799866850063782321/210500000000000000000000000000000 : ℝ)*base79 + (5037174509069/4210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (72758669/5000000000000000000000 : ℝ)*base90 + (72758669/5000000000000000000000 : ℝ)*base92 + (72758669/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1461_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(29589/50000 : ℝ) else (80623/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21201/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1461_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1461_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(29589/50000 : ℝ) else (80623/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21201/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1461_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1461_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1461_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(29589/50000 : ℝ) else (80623/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21201/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1461_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

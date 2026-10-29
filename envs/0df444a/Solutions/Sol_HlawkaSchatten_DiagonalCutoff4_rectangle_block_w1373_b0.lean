-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1373_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:21.214519+00:00
-- url     : https://prove2.me/submissions/b1c36c9f-b9ca-435f-b45d-c5148fa929c5

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
theorem support_rectangle_w1373_s0_0 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1790960941/10000000000 : ℝ)*x 0 + (1196727041/2000000000 : ℝ)*x 1 + (963650257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1790960941/10000000000 : ℝ)^4333 ≤ (5259165726843/50000000000000 : ℝ)^3309 := by
    have hnat : (1790960941 : ℕ)^4333*50000000000000^3309 ≤ 5259165726843^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790960941 10000000000 5259165726843 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1196727041/2000000000 : ℝ)^4333 ≤ (1020880570959/2000000000000 : ℝ)^3309 := by
    have hnat : (1196727041 : ℕ)^4333*2000000000000^3309 ≤ 1020880570959^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196727041 2000000000 1020880570959 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963650257/2000000000 : ℝ)^4333 ≤ (3843763998277/10000000000000 : ℝ)^3309 := by
    have hnat : (963650257 : ℕ)^4333*10000000000000^3309 ≤ 3843763998277^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963650257 2000000000 3843763998277 10000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1790960941/10000000000 : ℝ), (1196727041/2000000000 : ℝ), (963650257/2000000000 : ℝ)] ![(5259165726843/50000000000000 : ℝ), (1020880570959/2000000000000 : ℝ), (3843763998277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1790960941/10000000000 : ℝ)|^4333 ≤ (5259165726843/50000000000000 : ℝ)^3309
        have hw : |(-1790960941/10000000000 : ℝ)|=(1790960941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1196727041/2000000000 : ℝ)|^4333 ≤ (1020880570959/2000000000000 : ℝ)^3309
        have hw : |(1196727041/2000000000 : ℝ)|=(1196727041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963650257/2000000000 : ℝ)|^4333 ≤ (3843763998277/10000000000000 : ℝ)^3309
        have hw : |(963650257/2000000000 : ℝ)|=(963650257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_1 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5498344391/10000000000 : ℝ)*x 0 + (-2451881377/10000000000 : ℝ)*x 1 + (963650377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498344391/10000000000 : ℝ)^4333 ≤ (45692441110247/100000000000000 : ℝ)^3309 := by
    have hnat : (5498344391 : ℕ)^4333*100000000000000^3309 ≤ 45692441110247^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498344391 10000000000 45692441110247 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451881377/10000000000 : ℝ)^4333 ≤ (15869912625649/100000000000000 : ℝ)^3309 := by
    have hnat : (2451881377 : ℕ)^4333*100000000000000^3309 ≤ 15869912625649^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451881377 10000000000 15869912625649 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963650377/2000000000 : ℝ)^4333 ≤ (19218823125251/50000000000000 : ℝ)^3309 := by
    have hnat : (963650377 : ℕ)^4333*50000000000000^3309 ≤ 19218823125251^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963650377 2000000000 19218823125251 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498344391/10000000000 : ℝ), (-2451881377/10000000000 : ℝ), (963650377/2000000000 : ℝ)] ![(45692441110247/100000000000000 : ℝ), (15869912625649/100000000000000 : ℝ), (19218823125251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498344391/10000000000 : ℝ)|^4333 ≤ (45692441110247/100000000000000 : ℝ)^3309
        have hw : |(5498344391/10000000000 : ℝ)|=(5498344391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2451881377/10000000000 : ℝ)|^4333 ≤ (15869912625649/100000000000000 : ℝ)^3309
        have hw : |(-2451881377/10000000000 : ℝ)|=(2451881377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963650377/2000000000 : ℝ)|^4333 ≤ (19218823125251/50000000000000 : ℝ)^3309
        have hw : |(963650377/2000000000 : ℝ)|=(963650377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_2 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5498344279/10000000000 : ℝ)*x 0 + (4818251203/10000000000 : ℝ)*x 1 + (-61297059/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498344279/10000000000 : ℝ)^4333 ≤ (1827697595659/4000000000000 : ℝ)^3309 := by
    have hnat : (5498344279 : ℕ)^4333*4000000000000^3309 ≤ 1827697595659^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498344279 10000000000 1827697595659 4000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4818251203/10000000000 : ℝ)^4333 ≤ (1921881956309/5000000000000 : ℝ)^3309 := by
    have hnat : (4818251203 : ℕ)^4333*5000000000000^3309 ≤ 1921881956309^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818251203 10000000000 1921881956309 5000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61297059/250000000 : ℝ)^4333 ≤ (7934960478549/50000000000000 : ℝ)^3309 := by
    have hnat : (61297059 : ℕ)^4333*50000000000000^3309 ≤ 7934960478549^3309*250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61297059 250000000 7934960478549 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498344279/10000000000 : ℝ), (4818251203/10000000000 : ℝ), (-61297059/250000000 : ℝ)] ![(1827697595659/4000000000000 : ℝ), (1921881956309/5000000000000 : ℝ), (7934960478549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498344279/10000000000 : ℝ)|^4333 ≤ (1827697595659/4000000000000 : ℝ)^3309
        have hw : |(5498344279/10000000000 : ℝ)|=(5498344279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4818251203/10000000000 : ℝ)|^4333 ≤ (1921881956309/5000000000000 : ℝ)^3309
        have hw : |(4818251203/10000000000 : ℝ)|=(4818251203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61297059/250000000 : ℝ)|^4333 ≤ (7934960478549/50000000000000 : ℝ)^3309
        have hw : |(-61297059/250000000 : ℝ)|=(61297059/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_3 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174142911/10000000000 : ℝ)*x 0 + (621034273/2000000000 : ℝ)*x 1 + (5574652267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174142911/10000000000 : ℝ)^4333 ≤ (15926430083287/50000000000000 : ℝ)^3309 := by
    have hnat : (4174142911 : ℕ)^4333*50000000000000^3309 ≤ 15926430083287^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174142911 10000000000 15926430083287 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621034273/2000000000 : ℝ)^4333 ≤ (10811273650459/50000000000000 : ℝ)^3309 := by
    have hnat : (621034273 : ℕ)^4333*50000000000000^3309 ≤ 10811273650459^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621034273 2000000000 10811273650459 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5574652267/10000000000 : ℝ)^4333 ≤ (46524592519391/100000000000000 : ℝ)^3309 := by
    have hnat : (5574652267 : ℕ)^4333*100000000000000^3309 ≤ 46524592519391^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574652267 10000000000 46524592519391 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174142911/10000000000 : ℝ), (621034273/2000000000 : ℝ), (5574652267/10000000000 : ℝ)] ![(15926430083287/50000000000000 : ℝ), (10811273650459/50000000000000 : ℝ), (46524592519391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174142911/10000000000 : ℝ)|^4333 ≤ (15926430083287/50000000000000 : ℝ)^3309
        have hw : |(4174142911/10000000000 : ℝ)|=(4174142911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621034273/2000000000 : ℝ)|^4333 ≤ (10811273650459/50000000000000 : ℝ)^3309
        have hw : |(621034273/2000000000 : ℝ)|=(621034273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5574652267/10000000000 : ℝ)|^4333 ≤ (46524592519391/100000000000000 : ℝ)^3309
        have hw : |(5574652267/10000000000 : ℝ)|=(5574652267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_4 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1795257549/10000000000 : ℝ)*x 0 + (4848187349/10000000000 : ℝ)*x 1 + (5952629179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795257549/10000000000 : ℝ)^4333 ≤ (10551386630567/100000000000000 : ℝ)^3309 := by
    have hnat : (1795257549 : ℕ)^4333*100000000000000^3309 ≤ 10551386630567^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795257549 10000000000 10551386630567 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4848187349/10000000000 : ℝ)^4333 ≤ (9687664727711/25000000000000 : ℝ)^3309 := by
    have hnat : (4848187349 : ℕ)^4333*25000000000000^3309 ≤ 9687664727711^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4848187349 10000000000 9687664727711 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5952629179/10000000000 : ℝ)^4333 ≤ (25348977223679/50000000000000 : ℝ)^3309 := by
    have hnat : (5952629179 : ℕ)^4333*50000000000000^3309 ≤ 25348977223679^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5952629179 10000000000 25348977223679 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1795257549/10000000000 : ℝ), (4848187349/10000000000 : ℝ), (5952629179/10000000000 : ℝ)] ![(10551386630567/100000000000000 : ℝ), (9687664727711/25000000000000 : ℝ), (25348977223679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1795257549/10000000000 : ℝ)|^4333 ≤ (10551386630567/100000000000000 : ℝ)^3309
        have hw : |(-1795257549/10000000000 : ℝ)|=(1795257549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4848187349/10000000000 : ℝ)|^4333 ≤ (9687664727711/25000000000000 : ℝ)^3309
        have hw : |(4848187349/10000000000 : ℝ)|=(4848187349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5952629179/10000000000 : ℝ)|^4333 ≤ (25348977223679/50000000000000 : ℝ)^3309
        have hw : |(5952629179/10000000000 : ℝ)|=(5952629179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_5 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180554061/10000000000 : ℝ)*x 0 + (-164688341/1250000000 : ℝ)*x 1 + (2976313943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180554061/10000000000 : ℝ)^4333 ≤ (21132814818029/50000000000000 : ℝ)^3309 := by
    have hnat : (5180554061 : ℕ)^4333*50000000000000^3309 ≤ 21132814818029^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180554061 10000000000 21132814818029 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164688341/1250000000 : ℝ)^4333 ≤ (7036430320359/100000000000000 : ℝ)^3309 := by
    have hnat : (164688341 : ℕ)^4333*100000000000000^3309 ≤ 7036430320359^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164688341 1250000000 7036430320359 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2976313943/5000000000 : ℝ)^4333 ≤ (50697940027133/100000000000000 : ℝ)^3309 := by
    have hnat : (2976313943 : ℕ)^4333*100000000000000^3309 ≤ 50697940027133^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2976313943 5000000000 50697940027133 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180554061/10000000000 : ℝ), (-164688341/1250000000 : ℝ), (2976313943/5000000000 : ℝ)] ![(21132814818029/50000000000000 : ℝ), (7036430320359/100000000000000 : ℝ), (50697940027133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180554061/10000000000 : ℝ)|^4333 ≤ (21132814818029/50000000000000 : ℝ)^3309
        have hw : |(5180554061/10000000000 : ℝ)|=(5180554061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164688341/1250000000 : ℝ)|^4333 ≤ (7036430320359/100000000000000 : ℝ)^3309
        have hw : |(-164688341/1250000000 : ℝ)|=(164688341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2976313943/5000000000 : ℝ)|^4333 ≤ (50697940027133/100000000000000 : ℝ)^3309
        have hw : |(2976313943/5000000000 : ℝ)|=(2976313943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_6 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (647569119/1250000000 : ℝ)*x 0 + (5952630371/10000000000 : ℝ)*x 1 + (-65875223/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647569119/1250000000 : ℝ)^4333 ≤ (42265617788343/100000000000000 : ℝ)^3309 := by
    have hnat : (647569119 : ℕ)^4333*100000000000000^3309 ≤ 42265617788343^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647569119 1250000000 42265617788343 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5952630371/10000000000 : ℝ)^4333 ≤ (25348983870589/50000000000000 : ℝ)^3309 := by
    have hnat : (5952630371 : ℕ)^4333*50000000000000^3309 ≤ 25348983870589^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5952630371 10000000000 25348983870589 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65875223/500000000 : ℝ)^4333 ≤ (7036414459219/100000000000000 : ℝ)^3309 := by
    have hnat : (65875223 : ℕ)^4333*100000000000000^3309 ≤ 7036414459219^3309*500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65875223 500000000 7036414459219 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647569119/1250000000 : ℝ), (5952630371/10000000000 : ℝ), (-65875223/500000000 : ℝ)] ![(42265617788343/100000000000000 : ℝ), (25348983870589/50000000000000 : ℝ), (7036414459219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647569119/1250000000 : ℝ)|^4333 ≤ (42265617788343/100000000000000 : ℝ)^3309
        have hw : |(647569119/1250000000 : ℝ)|=(647569119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5952630371/10000000000 : ℝ)|^4333 ≤ (25348983870589/50000000000000 : ℝ)^3309
        have hw : |(5952630371/10000000000 : ℝ)|=(5952630371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65875223/500000000 : ℝ)|^4333 ≤ (7036414459219/100000000000000 : ℝ)^3309
        have hw : |(-65875223/500000000 : ℝ)|=(65875223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s0_7 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209161981/500000000 : ℝ)*x 0 + (2755609933/5000000000 : ℝ)*x 1 + (634175117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209161981/500000000 : ℝ)^4333 ≤ (15971894716967/50000000000000 : ℝ)^3309 := by
    have hnat : (209161981 : ℕ)^4333*50000000000000^3309 ≤ 15971894716967^3309*500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209161981 500000000 15971894716967 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755609933/5000000000 : ℝ)^4333 ≤ (45832601355519/100000000000000 : ℝ)^3309 := by
    have hnat : (2755609933 : ℕ)^4333*100000000000000^3309 ≤ 45832601355519^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755609933 5000000000 45832601355519 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634175117/2000000000 : ℝ)^4333 ≤ (22223609190259/100000000000000 : ℝ)^3309 := by
    have hnat : (634175117 : ℕ)^4333*100000000000000^3309 ≤ 22223609190259^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634175117 2000000000 22223609190259 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209161981/500000000 : ℝ), (2755609933/5000000000 : ℝ), (634175117/2000000000 : ℝ)] ![(15971894716967/50000000000000 : ℝ), (45832601355519/100000000000000 : ℝ), (22223609190259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209161981/500000000 : ℝ)|^4333 ≤ (15971894716967/50000000000000 : ℝ)^3309
        have hw : |(209161981/500000000 : ℝ)|=(209161981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755609933/5000000000 : ℝ)|^4333 ≤ (45832601355519/100000000000000 : ℝ)^3309
        have hw : |(2755609933/5000000000 : ℝ)|=(2755609933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634175117/2000000000 : ℝ)|^4333 ≤ (22223609190259/100000000000000 : ℝ)^3309
        have hw : |(634175117/2000000000 : ℝ)|=(634175117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1373_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (411/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (533/2000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (1083/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1083 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1083*1^256 ≤ 0^256*1^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1083/256 : ℝ) ≤ (2072656004713112003/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1083 ≤ (2072656004713112003/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1083*100000000000000000000^256 ≤ 2072656004713112003^256*5^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2072656004713112003 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2072656004713112003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1083 := by
      have hnat : (1 : ℕ)^256*1^1083 ≤ 1^1083*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102072656004713112003/100000000000000000000 : ℝ) ≤ (2009722094567989/2000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (102072656004713112003/100000000000000000000 : ℝ)^256 ≤ (2009722094567989/2000000000000000 : ℝ)^1083 := by
      have hnat : (102072656004713112003 : ℕ)^256*2000000000000000^1083 ≤ 2009722094567989^1083*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102072656004713112003 100000000000000000000 2009722094567989 2000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009722094567989/2000000000000000 : ℝ)) (X := (102072656004713112003/100000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52072656004713112003/50000000000000000000 : ℝ) ≤ (1009722094567989/1000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (52072656004713112003/50000000000000000000 : ℝ)^256 ≤ (1009722094567989/1000000000000000 : ℝ)^1083 := by
      have hnat : (52072656004713112003 : ℕ)^256*1000000000000000^1083 ≤ 1009722094567989^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52072656004713112003 50000000000000000000 1009722094567989 1000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009722094567989/1000000000000000 : ℝ)) (X := (52072656004713112003/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9722094567989/800000000000000 : ℝ)*(0 : ℝ))^(1083/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(9722094567989/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2072656004713112003/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9722094567989/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1083/256 : ℝ) := by
    rw [show (1 : ℝ)+(9722094567989/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2009722094567989/2000000000000000 : ℝ) by norm_num, show 1+(2072656004713112003/100000000000000000000 : ℝ)+(0 : ℝ)=(102072656004713112003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2072656004713112003/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9722094567989/800000000000000 : ℝ)*(2/5 : ℝ))^(1083/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(9722094567989/800000000000000 : ℝ)*(2/5 : ℝ)=(1009722094567989/1000000000000000 : ℝ) by norm_num, show 1+2*(2072656004713112003/100000000000000000000 : ℝ)=(52072656004713112003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9722094567989/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9722094567989/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9722094567989/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9722094567989/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9722094567989/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9722094567989/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1790960941/10000000000 : ℝ)*X 0 0+(1196727041/2000000000 : ℝ)*X 0 1+(963650257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5498344391/10000000000 : ℝ)*X 1 0+(-2451881377/10000000000 : ℝ)*X 1 1+(963650377/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5498344279/10000000000 : ℝ)*X 2 0+(4818251203/10000000000 : ℝ)*X 2 1+(-61297059/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4174142911/10000000000 : ℝ)*X 0 0+(621034273/2000000000 : ℝ)*X 0 1+(5574652267/10000000000 : ℝ)*X 0 2+(4174142911/10000000000 : ℝ)*X 1 0+(621034273/2000000000 : ℝ)*X 1 1+(5574652267/10000000000 : ℝ)*X 1 2+(4174142911/10000000000 : ℝ)*X 2 0+(621034273/2000000000 : ℝ)*X 2 1+(5574652267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1795257549/10000000000 : ℝ)*X 0 0+(4848187349/10000000000 : ℝ)*X 0 1+(5952629179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180554061/10000000000 : ℝ)*X 1 0+(-164688341/1250000000 : ℝ)*X 1 1+(2976313943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647569119/1250000000 : ℝ)*X 2 0+(5952630371/10000000000 : ℝ)*X 2 1+(-65875223/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((209161981/500000000 : ℝ)*X 0 0+(2755609933/5000000000 : ℝ)*X 0 1+(634175117/2000000000 : ℝ)*X 0 2+(209161981/500000000 : ℝ)*X 1 0+(2755609933/5000000000 : ℝ)*X 1 1+(634175117/2000000000 : ℝ)*X 1 2+(209161981/500000000 : ℝ)*X 2 0+(2755609933/5000000000 : ℝ)*X 2 1+(634175117/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74636973858322893143331/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230160671/100000000000000 : ℝ)*(base1) + (433662429/25000000000000 : ℝ)*(base19) + (429292629/25000000000000 : ℝ)*(base23) + (305306727/100000000000000 : ℝ)*(upper3) + (2247351/5000000000000 : ℝ)*(upper5) + (315761393525569/50000000000000 : ℝ)*(major0) + (315761393525569/50000000000000 : ℝ)*(major1) + (315761393525569/50000000000000 : ℝ)*(major2) + (858092437197067/100000000000000 : ℝ)*(sp0) + (858095180991151/100000000000000 : ℝ)*(sp1) + (858095198470351/100000000000000 : ℝ)*(sp2) + (50618171260959/12500000000000 : ℝ)*(sp3) + (588575559/12500000000000 : ℝ)*(sp4) + (1404711573/50000000000000 : ℝ)*(sp7) + (40494840967149/10000000000000 : ℝ)*(f.failure) + (858096915640867/100000000000000 : ℝ)*(f.sum) + (69576309670741/20000000000000000000000000000 : ℝ)*base65 + (87828713250741/40000000000000000000000000000 : ℝ)*base67 + (29092183730741/40000000000000000000000000000 : ℝ)*base69 + (125727810290741/40000000000000000000000000000 : ℝ)*base71 + (104755964630741/20000000000000000000000000000 : ℝ)*base73 + (140852181650741/40000000000000000000000000000 : ℝ)*base75 + (163708294770741/40000000000000000000000000000 : ℝ)*base77 + (157972161650741/40000000000000000000000000000 : ℝ)*base79 + (97589990930741/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1016359/500000000000000000000 : ℝ)*base90 + (1016359/500000000000000000000 : ℝ)*base92 + (1016359/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187116714444687499442241/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (465051367/50000000000000 : ℝ)*(base19) + (149398011/10000000000000 : ℝ)*(base23) + (288533001/50000000000000 : ℝ)*(base39) + (18686383/25000000000000 : ℝ)*(upper2) + (168198591/50000000000000 : ℝ)*(upper5) + (166589866036663/25000000000000 : ℝ)*(major0) + (166589866036663/25000000000000 : ℝ)*(major1) + (13327177741613/2000000000000 : ℝ)*(major2) + (285812307/12500000000000 : ℝ)*(sp1) + (3099828161/100000000000000 : ℝ)*(sp2) + (226357867452443/25000000000000 : ℝ)*(sp4) + (452714126604291/50000000000000 : ℝ)*(sp5) + (56589215816719/6250000000000 : ℝ)*(sp6) + (427286569556329/100000000000000 : ℝ)*(sp7) + (427286569556329/100000000000000 : ℝ)*(f.failure) + (36217281875031/4000000000000 : ℝ)*(f.sum) + (196200630062161/40000000000000000000000000000 : ℝ)*base66 + (15275412879057/1600000000000000000000000000 : ℝ)*base67 + (130655327120707/20000000000000000000000000000 : ℝ)*base69 + (11443956181457/1600000000000000000000000000 : ℝ)*base71 + (143989283777839/40000000000000000000000000000 : ℝ)*base73 + (61199926640707/20000000000000000000000000000 : ℝ)*base75 + (53736733959293/20000000000000000000000000000 : ℝ)*base78 + (47634148560707/20000000000000000000000000000 : ℝ)*base79 + (19351423530707/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (30787739/5000000000000000000000 : ℝ)*base90 + (30787739/5000000000000000000000 : ℝ)*base92 + (30787739/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1373_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (411/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (533/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1373_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1373_s1_0 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971311091/10000000000 : ℝ)*x 0 + (5628509827/10000000000 : ℝ)*x 1 + (5057843489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971311091/10000000000 : ℝ)^4333 ≤ (2981609590737/25000000000000 : ℝ)^3309 := by
    have hnat : (1971311091 : ℕ)^4333*25000000000000^3309 ≤ 2981609590737^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971311091 10000000000 2981609590737 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5628509827/10000000000 : ℝ)^4333 ≤ (5889255944499/12500000000000 : ℝ)^3309 := by
    have hnat : (5628509827 : ℕ)^4333*12500000000000^3309 ≤ 5889255944499^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628509827 10000000000 5889255944499 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057843489/10000000000 : ℝ)^4333 ≤ (40959514070439/100000000000000 : ℝ)^3309 := by
    have hnat : (5057843489 : ℕ)^4333*100000000000000^3309 ≤ 40959514070439^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057843489 10000000000 40959514070439 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971311091/10000000000 : ℝ), (5628509827/10000000000 : ℝ), (5057843489/10000000000 : ℝ)] ![(2981609590737/25000000000000 : ℝ), (5889255944499/12500000000000 : ℝ), (40959514070439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971311091/10000000000 : ℝ)|^4333 ≤ (2981609590737/25000000000000 : ℝ)^3309
        have hw : |(-1971311091/10000000000 : ℝ)|=(1971311091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5628509827/10000000000 : ℝ)|^4333 ≤ (5889255944499/12500000000000 : ℝ)^3309
        have hw : |(5628509827/10000000000 : ℝ)|=(5628509827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057843489/10000000000 : ℝ)|^4333 ≤ (40959514070439/100000000000000 : ℝ)^3309
        have hw : |(5057843489/10000000000 : ℝ)|=(5057843489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_1 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540250561/1000000000 : ℝ)*x 0 + (-568760389/2500000000 : ℝ)*x 1 + (5057844813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540250561/1000000000 : ℝ)^4333 ≤ (44652358107257/100000000000000 : ℝ)^3309 := by
    have hnat : (540250561 : ℕ)^4333*100000000000000^3309 ≤ 44652358107257^3309*1000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540250561 1000000000 44652358107257 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568760389/2500000000 : ℝ)^4333 ≤ (14388113774113/100000000000000 : ℝ)^3309 := by
    have hnat : (568760389 : ℕ)^4333*100000000000000^3309 ≤ 14388113774113^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568760389 2500000000 14388113774113 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057844813/10000000000 : ℝ)^4333 ≤ (40959528110511/100000000000000 : ℝ)^3309 := by
    have hnat : (5057844813 : ℕ)^4333*100000000000000^3309 ≤ 40959528110511^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057844813 10000000000 40959528110511 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540250561/1000000000 : ℝ), (-568760389/2500000000 : ℝ), (5057844813/10000000000 : ℝ)] ![(44652358107257/100000000000000 : ℝ), (14388113774113/100000000000000 : ℝ), (40959528110511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540250561/1000000000 : ℝ)|^4333 ≤ (44652358107257/100000000000000 : ℝ)^3309
        have hw : |(540250561/1000000000 : ℝ)|=(540250561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-568760389/2500000000 : ℝ)|^4333 ≤ (14388113774113/100000000000000 : ℝ)^3309
        have hw : |(-568760389/2500000000 : ℝ)|=(568760389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057844813/10000000000 : ℝ)|^4333 ≤ (40959528110511/100000000000000 : ℝ)^3309
        have hw : |(5057844813/10000000000 : ℝ)|=(5057844813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_2 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42207079/78125000 : ℝ)*x 0 + (1264460921/2500000000 : ℝ)*x 1 + (-455008469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42207079/78125000 : ℝ)^4333 ≤ (44652363540321/100000000000000 : ℝ)^3309 := by
    have hnat : (42207079 : ℕ)^4333*100000000000000^3309 ≤ 44652363540321^3309*78125000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42207079 78125000 44652363540321 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264460921/2500000000 : ℝ)^4333 ≤ (20479758069137/50000000000000 : ℝ)^3309 := by
    have hnat : (1264460921 : ℕ)^4333*50000000000000^3309 ≤ 20479758069137^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264460921 2500000000 20479758069137 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455008469/2000000000 : ℝ)^4333 ≤ (14388120308179/100000000000000 : ℝ)^3309 := by
    have hnat : (455008469 : ℕ)^4333*100000000000000^3309 ≤ 14388120308179^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455008469 2000000000 14388120308179 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42207079/78125000 : ℝ), (1264460921/2500000000 : ℝ), (-455008469/2000000000 : ℝ)] ![(44652363540321/100000000000000 : ℝ), (20479758069137/50000000000000 : ℝ), (14388120308179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42207079/78125000 : ℝ)|^4333 ≤ (44652363540321/100000000000000 : ℝ)^3309
        have hw : |(42207079/78125000 : ℝ)|=(42207079/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1264460921/2500000000 : ℝ)|^4333 ≤ (20479758069137/50000000000000 : ℝ)^3309
        have hw : |(1264460921/2500000000 : ℝ)|=(1264460921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455008469/2000000000 : ℝ)|^4333 ≤ (14388120308179/100000000000000 : ℝ)^3309
        have hw : |(-455008469/2000000000 : ℝ)|=(455008469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_3 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4286759159/10000000000 : ℝ)*x 0 + (3721121051/10000000000 : ℝ)*x 1 + (2465187093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286759159/10000000000 : ℝ)^4333 ≤ (6596568789397/20000000000000 : ℝ)^3309 := by
    have hnat : (4286759159 : ℕ)^4333*20000000000000^3309 ≤ 6596568789397^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286759159 10000000000 6596568789397 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3721121051/10000000000 : ℝ)^4333 ≤ (6851015149293/25000000000000 : ℝ)^3309 := by
    have hnat : (3721121051 : ℕ)^4333*25000000000000^3309 ≤ 6851015149293^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721121051 10000000000 6851015149293 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2465187093/5000000000 : ℝ)^4333 ≤ (39613095436873/100000000000000 : ℝ)^3309 := by
    have hnat : (2465187093 : ℕ)^4333*100000000000000^3309 ≤ 39613095436873^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465187093 5000000000 39613095436873 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286759159/10000000000 : ℝ), (3721121051/10000000000 : ℝ), (2465187093/5000000000 : ℝ)] ![(6596568789397/20000000000000 : ℝ), (6851015149293/25000000000000 : ℝ), (39613095436873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286759159/10000000000 : ℝ)|^4333 ≤ (6596568789397/20000000000000 : ℝ)^3309
        have hw : |(4286759159/10000000000 : ℝ)|=(4286759159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3721121051/10000000000 : ℝ)|^4333 ≤ (6851015149293/25000000000000 : ℝ)^3309
        have hw : |(3721121051/10000000000 : ℝ)|=(3721121051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2465187093/5000000000 : ℝ)|^4333 ≤ (39613095436873/100000000000000 : ℝ)^3309
        have hw : |(2465187093/5000000000 : ℝ)|=(2465187093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_4 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-985896839/5000000000 : ℝ)*x 0 + (316552203/625000000 : ℝ)*x 1 + (2810696969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985896839/5000000000 : ℝ)^4333 ≤ (238605233473/2000000000000 : ℝ)^3309 := by
    have hnat : (985896839 : ℕ)^4333*2000000000000^3309 ≤ 238605233473^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985896839 5000000000 238605233473 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316552203/625000000 : ℝ)^4333 ≤ (4103367251873/10000000000000 : ℝ)^3309 := by
    have hnat : (316552203 : ℕ)^4333*10000000000000^3309 ≤ 4103367251873^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316552203 625000000 4103367251873 10000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2810696969/5000000000 : ℝ)^4333 ≤ (47036065786563/100000000000000 : ℝ)^3309 := by
    have hnat : (2810696969 : ℕ)^4333*100000000000000^3309 ≤ 47036065786563^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810696969 5000000000 47036065786563 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985896839/5000000000 : ℝ), (316552203/625000000 : ℝ), (2810696969/5000000000 : ℝ)] ![(238605233473/2000000000000 : ℝ), (4103367251873/10000000000000 : ℝ), (47036065786563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985896839/5000000000 : ℝ)|^4333 ≤ (238605233473/2000000000000 : ℝ)^3309
        have hw : |(-985896839/5000000000 : ℝ)|=(985896839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316552203/625000000 : ℝ)|^4333 ≤ (4103367251873/10000000000000 : ℝ)^3309
        have hw : |(316552203/625000000 : ℝ)|=(316552203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2810696969/5000000000 : ℝ)|^4333 ≤ (47036065786563/100000000000000 : ℝ)^3309
        have hw : |(2810696969/5000000000 : ℝ)|=(2810696969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_5 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627024583/5000000000 : ℝ)*x 0 + (-855746113/5000000000 : ℝ)*x 1 + (5621394031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627024583/5000000000 : ℝ)^4333 ≤ (43052513535461/100000000000000 : ℝ)^3309 := by
    have hnat : (2627024583 : ℕ)^4333*100000000000000^3309 ≤ 43052513535461^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627024583 5000000000 43052513535461 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855746113/5000000000 : ℝ)^4333 ≤ (4955709822653/50000000000000 : ℝ)^3309 := by
    have hnat : (855746113 : ℕ)^4333*50000000000000^3309 ≤ 4955709822653^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855746113 5000000000 4955709822653 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5621394031/10000000000 : ℝ)^4333 ≤ (23518033402767/50000000000000 : ℝ)^3309 := by
    have hnat : (5621394031 : ℕ)^4333*50000000000000^3309 ≤ 23518033402767^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621394031 10000000000 23518033402767 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627024583/5000000000 : ℝ), (-855746113/5000000000 : ℝ), (5621394031/10000000000 : ℝ)] ![(43052513535461/100000000000000 : ℝ), (4955709822653/50000000000000 : ℝ), (23518033402767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627024583/5000000000 : ℝ)|^4333 ≤ (43052513535461/100000000000000 : ℝ)^3309
        have hw : |(2627024583/5000000000 : ℝ)|=(2627024583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855746113/5000000000 : ℝ)|^4333 ≤ (4955709822653/50000000000000 : ℝ)^3309
        have hw : |(-855746113/5000000000 : ℝ)|=(855746113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5621394031/10000000000 : ℝ)|^4333 ≤ (23518033402767/50000000000000 : ℝ)^3309
        have hw : |(5621394031/10000000000 : ℝ)|=(5621394031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_6 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262702453/500000000 : ℝ)*x 0 + (702674267/1250000000 : ℝ)*x 1 + (-13371033/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262702453/500000000 : ℝ)^4333 ≤ (4305251239809/10000000000000 : ℝ)^3309 := by
    have hnat : (262702453 : ℕ)^4333*10000000000000^3309 ≤ 4305251239809^3309*500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262702453 500000000 4305251239809 10000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702674267/1250000000 : ℝ)^4333 ≤ (23518033977993/50000000000000 : ℝ)^3309 := by
    have hnat : (702674267 : ℕ)^4333*50000000000000^3309 ≤ 23518033977993^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702674267 1250000000 23518033977993 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13371033/78125000 : ℝ)^4333 ≤ (495570981507/5000000000000 : ℝ)^3309 := by
    have hnat : (13371033 : ℕ)^4333*5000000000000^3309 ≤ 495570981507^3309*78125000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13371033 78125000 495570981507 5000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262702453/500000000 : ℝ), (702674267/1250000000 : ℝ), (-13371033/78125000 : ℝ)] ![(4305251239809/10000000000000 : ℝ), (23518033977993/50000000000000 : ℝ), (495570981507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262702453/500000000 : ℝ)|^4333 ≤ (4305251239809/10000000000000 : ℝ)^3309
        have hw : |(262702453/500000000 : ℝ)|=(262702453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702674267/1250000000 : ℝ)|^4333 ≤ (23518033977993/50000000000000 : ℝ)^3309
        have hw : |(702674267/1250000000 : ℝ)|=(702674267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13371033/78125000 : ℝ)|^4333 ≤ (495570981507/5000000000000 : ℝ)^3309
        have hw : |(-13371033/78125000 : ℝ)|=(13371033/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s1_7 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071945629/2500000000 : ℝ)*x 0 + (98311207/200000000 : ℝ)*x 1 + (3736196521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071945629/2500000000 : ℝ)^4333 ≤ (32993154789241/100000000000000 : ℝ)^3309 := by
    have hnat : (1071945629 : ℕ)^4333*100000000000000^3309 ≤ 32993154789241^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071945629 2500000000 32993154789241 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98311207/200000000 : ℝ)^4333 ≤ (19728656900031/50000000000000 : ℝ)^3309 := by
    have hnat : (98311207 : ℕ)^4333*50000000000000^3309 ≤ 19728656900031^3309*200000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98311207 200000000 19728656900031 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3736196521/10000000000 : ℝ)^4333 ≤ (13774765695159/50000000000000 : ℝ)^3309 := by
    have hnat : (3736196521 : ℕ)^4333*50000000000000^3309 ≤ 13774765695159^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736196521 10000000000 13774765695159 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071945629/2500000000 : ℝ), (98311207/200000000 : ℝ), (3736196521/10000000000 : ℝ)] ![(32993154789241/100000000000000 : ℝ), (19728656900031/50000000000000 : ℝ), (13774765695159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071945629/2500000000 : ℝ)|^4333 ≤ (32993154789241/100000000000000 : ℝ)^3309
        have hw : |(1071945629/2500000000 : ℝ)|=(1071945629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(98311207/200000000 : ℝ)|^4333 ≤ (19728656900031/50000000000000 : ℝ)^3309
        have hw : |(98311207/200000000 : ℝ)|=(98311207/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3736196521/10000000000 : ℝ)|^4333 ≤ (13774765695159/50000000000000 : ℝ)^3309
        have hw : |(3736196521/10000000000 : ℝ)|=(3736196521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1373_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (533/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9617/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (533/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (411/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (533/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (411/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (533/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (411/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (533/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (411/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (533/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (411/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (533/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (411/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (411/25000 : ℝ) ^ (1083/256 : ℝ) ≤ (141709308289/5000000000000000000 : ℝ) := by
    have hpowers : (411/25000 : ℝ)^1083 ≤ (141709308289/5000000000000000000 : ℝ)^256 := by
      have hnat : (411 : ℕ)^1083*5000000000000000000^256 ≤ 141709308289^256*25000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        411 25000 141709308289 5000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (411/25000 : ℝ)) (X := (141709308289/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hpowhi : (533/2000 : ℝ) ^ (1083/256 : ℝ) ≤ (371903279535538577/100000000000000000000 : ℝ) := by
    have hpowers : (533/2000 : ℝ)^1083 ≤ (371903279535538577/100000000000000000000 : ℝ)^256 := by
      have hnat : (533 : ℕ)^1083*100000000000000000000^256 ≤ 371903279535538577^256*2000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        533 2000 371903279535538577 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (533/2000 : ℝ)) (X := (371903279535538577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000141709308289/2500000000000000000 : ℝ) ≤ (1250000016748653/1250000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (2500000141709308289/2500000000000000000 : ℝ)^256 ≤ (1250000016748653/1250000000000000 : ℝ)^1083 := by
      have hnat : (2500000141709308289 : ℕ)^256*1250000000000000^1083 ≤ 1250000016748653^1083*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000141709308289 2500000000000000000 1250000016748653 1250000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000016748653/1250000000000000 : ℝ)) (X := (2500000141709308289/2500000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100371906113721704357/100000000000000000000 : ℝ) ≤ (10008778676556119/10000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (100371906113721704357/100000000000000000000 : ℝ)^256 ≤ (10008778676556119/10000000000000000 : ℝ)^1083 := by
      have hnat : (100371906113721704357 : ℕ)^256*10000000000000000^1083 ≤ 10008778676556119^1083*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100371906113721704357 100000000000000000000 10008778676556119 10000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008778676556119/10000000000000000 : ℝ)) (X := (100371906113721704357/100000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50371903279535538577/50000000000000000000 : ℝ) ≤ (5008778609561507/5000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50371903279535538577/50000000000000000000 : ℝ)^256 ≤ (5008778609561507/5000000000000000 : ℝ)^1083 := by
      have hnat : (50371903279535538577 : ℕ)^256*5000000000000000^1083 ≤ 5008778609561507^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50371903279535538577 50000000000000000000 5008778609561507 5000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008778609561507/5000000000000000 : ℝ)) (X := (50371903279535538577/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(141709308289/5000000000000000000 : ℝ) ≤ ((31253892437821823073/31257500000000000000 : ℝ)+2*(1755708513379/500120000000000 : ℝ)*(411/25000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (31253892437821823073/31257500000000000000 : ℝ)+2*(1755708513379/500120000000000 : ℝ)*(411/25000 : ℝ)=(1250000016748653/1250000000000000 : ℝ) by norm_num, show 1+2*(141709308289/5000000000000000000 : ℝ)=(2500000141709308289/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(371903279535538577/100000000000000000000 : ℝ)+(141709308289/5000000000000000000 : ℝ) ≤ ((31253892437821823073/31257500000000000000 : ℝ)+(1755708513379/500120000000000 : ℝ)*((533/2000 : ℝ)+(411/25000 : ℝ)))^(1083/256 : ℝ) := by
    rw [show (31253892437821823073/31257500000000000000 : ℝ)+(1755708513379/500120000000000 : ℝ)*((533/2000 : ℝ)+(411/25000 : ℝ))=(10008778676556119/10000000000000000 : ℝ) by norm_num, show 1+(371903279535538577/100000000000000000000 : ℝ)+(141709308289/5000000000000000000 : ℝ)=(100371906113721704357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(371903279535538577/100000000000000000000 : ℝ) ≤ ((31253892437821823073/31257500000000000000 : ℝ)+2*(1755708513379/500120000000000 : ℝ)*(533/2000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (31253892437821823073/31257500000000000000 : ℝ)+2*(1755708513379/500120000000000 : ℝ)*(533/2000 : ℝ)=(5008778609561507/5000000000000000 : ℝ) by norm_num, show 1+2*(371903279535538577/100000000000000000000 : ℝ)=(50371903279535538577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31253892437821823073/31257500000000000000 : ℝ)*(X 1 0+X 2 0)+(1755708513379/500120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (411/25000 : ℝ)) (hi := (533/2000 : ℝ)) (c := (31253892437821823073/31257500000000000000 : ℝ)) (alpha := (1755708513379/500120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31253892437821823073/31257500000000000000 : ℝ)*(X 0 1+X 2 1)+(1755708513379/500120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (411/25000 : ℝ)) (hi := (533/2000 : ℝ)) (c := (31253892437821823073/31257500000000000000 : ℝ)) (alpha := (1755708513379/500120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31253892437821823073/31257500000000000000 : ℝ)*(X 0 2+X 1 2)+(1755708513379/500120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (411/25000 : ℝ)) (hi := (533/2000 : ℝ)) (c := (31253892437821823073/31257500000000000000 : ℝ)) (alpha := (1755708513379/500120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1971311091/10000000000 : ℝ)*X 0 0+(5628509827/10000000000 : ℝ)*X 0 1+(5057843489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((540250561/1000000000 : ℝ)*X 1 0+(-568760389/2500000000 : ℝ)*X 1 1+(5057844813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42207079/78125000 : ℝ)*X 2 0+(1264460921/2500000000 : ℝ)*X 2 1+(-455008469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4286759159/10000000000 : ℝ)*X 0 0+(3721121051/10000000000 : ℝ)*X 0 1+(2465187093/5000000000 : ℝ)*X 0 2+(4286759159/10000000000 : ℝ)*X 1 0+(3721121051/10000000000 : ℝ)*X 1 1+(2465187093/5000000000 : ℝ)*X 1 2+(4286759159/10000000000 : ℝ)*X 2 0+(3721121051/10000000000 : ℝ)*X 2 1+(2465187093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-985896839/5000000000 : ℝ)*X 0 0+(316552203/625000000 : ℝ)*X 0 1+(2810696969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627024583/5000000000 : ℝ)*X 1 0+(-855746113/5000000000 : ℝ)*X 1 1+(5621394031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262702453/500000000 : ℝ)*X 2 0+(702674267/1250000000 : ℝ)*X 2 1+(-13371033/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071945629/2500000000 : ℝ)*X 0 0+(98311207/200000000 : ℝ)*X 0 1+(3736196521/10000000000 : ℝ)*X 0 2+(1071945629/2500000000 : ℝ)*X 1 0+(98311207/200000000 : ℝ)*X 1 1+(3736196521/10000000000 : ℝ)*X 1 2+(1071945629/2500000000 : ℝ)*X 2 0+(98311207/200000000 : ℝ)*X 2 1+(3736196521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3551712626482145332125963003/781437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15661733/25000000000000 : ℝ)*(base16) + (498837793/100000000000000 : ℝ)*(base19) + (786077353/100000000000000 : ℝ)*(base23) + (4171037/12500000000000 : ℝ)*(upper2) + (78536743/100000000000000 : ℝ)*(upper3) + (644827841782637/50000000000000 : ℝ)*(major0) + (644827841782637/50000000000000 : ℝ)*(major1) + (644827841782637/50000000000000 : ℝ)*(major2) + (876172392114463/50000000000000 : ℝ)*(sp0) + (438087689621863/25000000000000 : ℝ)*(sp1) + (70094021355793/4000000000000 : ℝ)*(sp2) + (103369757403021/12500000000000 : ℝ)*(sp3) + (6535743251/100000000000000 : ℝ)*(sp4) + (91821541/5000000000000 : ℝ)*(sp7) + (206739973913747/25000000000000 : ℝ)*(f.failure) + (876175659986089/50000000000000 : ℝ)*(f.sum) + (35435455813259/12503000000000000000000000000 : ℝ)*base65 + (4708614925042928999/1562875000000000000000000000000000 : ℝ)*base68 + (313269566168821001/1562875000000000000000000000000000 : ℝ)*base69 + (321607505268178999/1562875000000000000000000000000000 : ℝ)*base72 + (8392322675269/2500600000000000000000000000 : ℝ)*base74 + (198536999459821001/1562875000000000000000000000000000 : ℝ)*base75 + (1389152217023178999/1562875000000000000000000000000000 : ℝ)*base78 + (11577400928761678999/1562875000000000000000000000000000 : ℝ)*base80 + (6487361671697/6251500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2171623/1250000000000000000000 : ℝ)*base89 + (2171623/1250000000000000000000 : ℝ)*base91 + (2171623/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203405750673015821121357/25006000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10309669/12500000000000 : ℝ)*(base1) + (818337031/50000000000000 : ℝ)*(base19) + (320468499/20000000000000 : ℝ)*(base23) + (97137771/50000000000000 : ℝ)*(upper3) + (181554813/100000000000000 : ℝ)*(upper5) + (1322335267598331/100000000000000 : ℝ)*(major0) + (1322335267598331/100000000000000 : ℝ)*(major1) + (1322335267598331/100000000000000 : ℝ)*(major2) + (1092862833/12500000000000 : ℝ)*(sp1) + (34416951/390625000000 : ℝ)*(sp2) + (898377736854861/50000000000000 : ℝ)*(sp4) + (449186252913911/25000000000000 : ℝ)*(sp5) + (1796744978150419/100000000000000 : ℝ)*(sp6) + (105989348793043/12500000000000 : ℝ)*(sp7) + (13248669887839/1562500000000 : ℝ)*(f.failure) + (179675539123237/10000000000000 : ℝ)*(f.sum) + (22883743841479/25006000000000000000000000000 : ℝ)*base66 + (18515287226773153663/3125750000000000000000000000000000 : ℝ)*base67 + (4406622098979846337/3125750000000000000000000000000000 : ℝ)*base70 + (11279219762279153663/3125750000000000000000000000000000 : ℝ)*base71 + (60159189580417/25006000000000000000000000000 : ℝ)*base73 + (12730111632149846337/3125750000000000000000000000000000 : ℝ)*base76 + (4923959530171846337/3125750000000000000000000000000000 : ℝ)*base78 + (2618167108399153663/3125750000000000000000000000000000 : ℝ)*base79 + (14981115044161/25006000000000000000000000000 : ℝ)*base81 + (409101/78125000000000000000 : ℝ)*base89 + (409101/78125000000000000000 : ℝ)*base91 + (409101/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1373_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (533/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9617/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1373_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1373_s2_0 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008837863/10000000000 : ℝ)*x 0 + (2735782187/5000000000 : ℝ)*x 1 + (5190709001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008837863/10000000000 : ℝ)^4333 ≤ (6112303006861/50000000000000 : ℝ)^3309 := by
    have hnat : (2008837863 : ℕ)^4333*50000000000000^3309 ≤ 6112303006861^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008837863 10000000000 6112303006861 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735782187/5000000000 : ℝ)^4333 ≤ (22700621883509/50000000000000 : ℝ)^3309 := by
    have hnat : (2735782187 : ℕ)^4333*50000000000000^3309 ≤ 22700621883509^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735782187 5000000000 22700621883509 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190709001/10000000000 : ℝ)^4333 ≤ (42374150204353/100000000000000 : ℝ)^3309 := by
    have hnat : (5190709001 : ℕ)^4333*100000000000000^3309 ≤ 42374150204353^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190709001 10000000000 42374150204353 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008837863/10000000000 : ℝ), (2735782187/5000000000 : ℝ), (5190709001/10000000000 : ℝ)] ![(6112303006861/50000000000000 : ℝ), (22700621883509/50000000000000 : ℝ), (42374150204353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008837863/10000000000 : ℝ)|^4333 ≤ (6112303006861/50000000000000 : ℝ)^3309
        have hw : |(-2008837863/10000000000 : ℝ)|=(2008837863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735782187/5000000000 : ℝ)|^4333 ≤ (22700621883509/50000000000000 : ℝ)^3309
        have hw : |(2735782187/5000000000 : ℝ)|=(2735782187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190709001/10000000000 : ℝ)|^4333 ≤ (42374150204353/100000000000000 : ℝ)^3309
        have hw : |(5190709001/10000000000 : ℝ)|=(5190709001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_1 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363812629/10000000000 : ℝ)*x 0 + (-1076860209/5000000000 : ℝ)*x 1 + (5190709157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363812629/10000000000 : ℝ)^4333 ≤ (172789277893/390625000000 : ℝ)^3309 := by
    have hnat : (5363812629 : ℕ)^4333*390625000000^3309 ≤ 172789277893^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363812629 10000000000 172789277893 390625000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076860209/5000000000 : ℝ)^4333 ≤ (13391792968883/100000000000000 : ℝ)^3309 := by
    have hnat : (1076860209 : ℕ)^4333*100000000000000^3309 ≤ 13391792968883^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076860209 5000000000 13391792968883 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190709157/10000000000 : ℝ)^4333 ≤ (42374151871949/100000000000000 : ℝ)^3309 := by
    have hnat : (5190709157 : ℕ)^4333*100000000000000^3309 ≤ 42374151871949^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190709157 10000000000 42374151871949 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363812629/10000000000 : ℝ), (-1076860209/5000000000 : ℝ), (5190709157/10000000000 : ℝ)] ![(172789277893/390625000000 : ℝ), (13391792968883/100000000000000 : ℝ), (42374151871949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363812629/10000000000 : ℝ)|^4333 ≤ (172789277893/390625000000 : ℝ)^3309
        have hw : |(5363812629/10000000000 : ℝ)|=(5363812629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076860209/5000000000 : ℝ)|^4333 ≤ (13391792968883/100000000000000 : ℝ)^3309
        have hw : |(-1076860209/5000000000 : ℝ)|=(1076860209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190709157/10000000000 : ℝ)|^4333 ≤ (42374151871949/100000000000000 : ℝ)^3309
        have hw : |(5190709157/10000000000 : ℝ)|=(5190709157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_2 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363812599/10000000000 : ℝ)*x 0 + (2595354587/5000000000 : ℝ)*x 1 + (-538430109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363812599/10000000000 : ℝ)^4333 ≤ (11058513704161/25000000000000 : ℝ)^3309 := by
    have hnat : (5363812599 : ℕ)^4333*25000000000000^3309 ≤ 11058513704161^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363812599 10000000000 11058513704161 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2595354587/5000000000 : ℝ)^4333 ≤ (21187076026837/50000000000000 : ℝ)^3309 := by
    have hnat : (2595354587 : ℕ)^4333*50000000000000^3309 ≤ 21187076026837^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595354587 5000000000 21187076026837 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538430109/2500000000 : ℝ)^4333 ≤ (13391793115443/100000000000000 : ℝ)^3309 := by
    have hnat : (538430109 : ℕ)^4333*100000000000000^3309 ≤ 13391793115443^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538430109 2500000000 13391793115443 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363812599/10000000000 : ℝ), (2595354587/5000000000 : ℝ), (-538430109/2500000000 : ℝ)] ![(11058513704161/25000000000000 : ℝ), (21187076026837/50000000000000 : ℝ), (13391793115443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363812599/10000000000 : ℝ)|^4333 ≤ (11058513704161/25000000000000 : ℝ)^3309
        have hw : |(5363812599/10000000000 : ℝ)|=(5363812599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2595354587/5000000000 : ℝ)|^4333 ≤ (21187076026837/50000000000000 : ℝ)^3309
        have hw : |(2595354587/5000000000 : ℝ)|=(2595354587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538430109/2500000000 : ℝ)|^4333 ≤ (13391793115443/100000000000000 : ℝ)^3309
        have hw : |(-538430109/2500000000 : ℝ)|=(538430109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_3 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156547307/5000000000 : ℝ)*x 0 + (2012482423/5000000000 : ℝ)*x 1 + (924020977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156547307/5000000000 : ℝ)^4333 ≤ (259753352443/781250000000 : ℝ)^3309 := by
    have hnat : (2156547307 : ℕ)^4333*781250000000^3309 ≤ 259753352443^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156547307 5000000000 259753352443 781250000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012482423/5000000000 : ℝ)^4333 ≤ (30370514097883/100000000000000 : ℝ)^3309 := by
    have hnat : (2012482423 : ℕ)^4333*100000000000000^3309 ≤ 30370514097883^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012482423 5000000000 30370514097883 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924020977/2000000000 : ℝ)^4333 ≤ (36381056774723/100000000000000 : ℝ)^3309 := by
    have hnat : (924020977 : ℕ)^4333*100000000000000^3309 ≤ 36381056774723^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924020977 2000000000 36381056774723 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156547307/5000000000 : ℝ), (2012482423/5000000000 : ℝ), (924020977/2000000000 : ℝ)] ![(259753352443/781250000000 : ℝ), (30370514097883/100000000000000 : ℝ), (36381056774723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156547307/5000000000 : ℝ)|^4333 ≤ (259753352443/781250000000 : ℝ)^3309
        have hw : |(2156547307/5000000000 : ℝ)|=(2156547307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012482423/5000000000 : ℝ)|^4333 ≤ (30370514097883/100000000000000 : ℝ)^3309
        have hw : |(2012482423/5000000000 : ℝ)|=(2012482423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924020977/2000000000 : ℝ)|^4333 ≤ (36381056774723/100000000000000 : ℝ)^3309
        have hw : |(924020977/2000000000 : ℝ)|=(924020977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_4 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-200889547/1000000000 : ℝ)*x 0 + (1038482419/2000000000 : ℝ)*x 1 + (5469846409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200889547/1000000000 : ℝ)^4333 ≤ (3056266265693/25000000000000 : ℝ)^3309 := by
    have hnat : (200889547 : ℕ)^4333*25000000000000^3309 ≤ 3056266265693^3309*1000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200889547 1000000000 3056266265693 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038482419/2000000000 : ℝ)^4333 ≤ (42392356722819/100000000000000 : ℝ)^3309 := by
    have hnat : (1038482419 : ℕ)^4333*100000000000000^3309 ≤ 42392356722819^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038482419 2000000000 42392356722819 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469846409/10000000000 : ℝ)^4333 ≤ (907651563843/2000000000000 : ℝ)^3309 := by
    have hnat : (5469846409 : ℕ)^4333*2000000000000^3309 ≤ 907651563843^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469846409 10000000000 907651563843 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200889547/1000000000 : ℝ), (1038482419/2000000000 : ℝ), (5469846409/10000000000 : ℝ)] ![(3056266265693/25000000000000 : ℝ), (42392356722819/100000000000000 : ℝ), (907651563843/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200889547/1000000000 : ℝ)|^4333 ≤ (3056266265693/25000000000000 : ℝ)^3309
        have hw : |(-200889547/1000000000 : ℝ)|=(200889547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038482419/2000000000 : ℝ)|^4333 ≤ (42392356722819/100000000000000 : ℝ)^3309
        have hw : |(1038482419/2000000000 : ℝ)|=(1038482419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469846409/10000000000 : ℝ)|^4333 ≤ (907651563843/2000000000000 : ℝ)^3309
        have hw : |(5469846409/10000000000 : ℝ)|=(5469846409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_5 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330698999/625000000 : ℝ)*x 0 + (-468645731/2500000000 : ℝ)*x 1 + (2734923169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330698999/625000000 : ℝ)^4333 ≤ (43451402038023/100000000000000 : ℝ)^3309 := by
    have hnat : (330698999 : ℕ)^4333*100000000000000^3309 ≤ 43451402038023^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330698999 625000000 43451402038023 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468645731/2500000000 : ℝ)^4333 ≤ (223320410397/2000000000000 : ℝ)^3309 := by
    have hnat : (468645731 : ℕ)^4333*2000000000000^3309 ≤ 223320410397^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468645731 2500000000 223320410397 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734923169/5000000000 : ℝ)^4333 ≤ (45382577420777/100000000000000 : ℝ)^3309 := by
    have hnat : (2734923169 : ℕ)^4333*100000000000000^3309 ≤ 45382577420777^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734923169 5000000000 45382577420777 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330698999/625000000 : ℝ), (-468645731/2500000000 : ℝ), (2734923169/5000000000 : ℝ)] ![(43451402038023/100000000000000 : ℝ), (223320410397/2000000000000 : ℝ), (45382577420777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330698999/625000000 : ℝ)|^4333 ≤ (43451402038023/100000000000000 : ℝ)^3309
        have hw : |(330698999/625000000 : ℝ)|=(330698999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468645731/2500000000 : ℝ)|^4333 ≤ (223320410397/2000000000000 : ℝ)^3309
        have hw : |(-468645731/2500000000 : ℝ)|=(468645731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734923169/5000000000 : ℝ)|^4333 ≤ (45382577420777/100000000000000 : ℝ)^3309
        have hw : |(2734923169/5000000000 : ℝ)|=(2734923169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_6 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529118393/1000000000 : ℝ)*x 0 + (5469846409/10000000000 : ℝ)*x 1 + (-18745829/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529118393/1000000000 : ℝ)^4333 ≤ (678928147771/1562500000000 : ℝ)^3309 := by
    have hnat : (529118393 : ℕ)^4333*1562500000000^3309 ≤ 678928147771^3309*1000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529118393 1000000000 678928147771 1562500000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469846409/10000000000 : ℝ)^4333 ≤ (907651563843/2000000000000 : ℝ)^3309 := by
    have hnat : (5469846409 : ℕ)^4333*2000000000000^3309 ≤ 907651563843^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469846409 10000000000 907651563843 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18745829/100000000 : ℝ)^4333 ≤ (5583010166327/50000000000000 : ℝ)^3309 := by
    have hnat : (18745829 : ℕ)^4333*50000000000000^3309 ≤ 5583010166327^3309*100000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18745829 100000000 5583010166327 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529118393/1000000000 : ℝ), (5469846409/10000000000 : ℝ), (-18745829/100000000 : ℝ)] ![(678928147771/1562500000000 : ℝ), (907651563843/2000000000000 : ℝ), (5583010166327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529118393/1000000000 : ℝ)|^4333 ≤ (678928147771/1562500000000 : ℝ)^3309
        have hw : |(529118393/1000000000 : ℝ)|=(529118393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469846409/10000000000 : ℝ)|^4333 ≤ (907651563843/2000000000000 : ℝ)^3309
        have hw : |(5469846409/10000000000 : ℝ)|=(5469846409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18745829/100000000 : ℝ)|^4333 ≤ (5583010166327/50000000000000 : ℝ)^3309
        have hw : |(-18745829/100000000 : ℝ)|=(18745829/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s2_7 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67394013/156250000 : ℝ)*x 0 + (4616496341/10000000000 : ℝ)*x 1 + (4028604891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67394013/156250000 : ℝ)^4333 ≤ (33249662817191/100000000000000 : ℝ)^3309 := by
    have hnat : (67394013 : ℕ)^4333*100000000000000^3309 ≤ 33249662817191^3309*156250000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67394013 156250000 33249662817191 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4616496341/10000000000 : ℝ)^4333 ≤ (7268770464679/20000000000000 : ℝ)^3309 := by
    have hnat : (4616496341 : ℕ)^4333*20000000000000^3309 ≤ 7268770464679^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616496341 10000000000 7268770464679 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028604891/10000000000 : ℝ)^4333 ≤ (475101325733/1562500000000 : ℝ)^3309 := by
    have hnat : (4028604891 : ℕ)^4333*1562500000000^3309 ≤ 475101325733^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028604891 10000000000 475101325733 1562500000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67394013/156250000 : ℝ), (4616496341/10000000000 : ℝ), (4028604891/10000000000 : ℝ)] ![(33249662817191/100000000000000 : ℝ), (7268770464679/20000000000000 : ℝ), (475101325733/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67394013/156250000 : ℝ)|^4333 ≤ (33249662817191/100000000000000 : ℝ)^3309
        have hw : |(67394013/156250000 : ℝ)|=(67394013/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4616496341/10000000000 : ℝ)|^4333 ≤ (7268770464679/20000000000000 : ℝ)^3309
        have hw : |(4616496341/10000000000 : ℝ)|=(4616496341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028604891/10000000000 : ℝ)|^4333 ≤ (475101325733/1562500000000 : ℝ)^3309
        have hw : |(4028604891/10000000000 : ℝ)|=(4028604891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1373_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (314/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9617/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9617/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9617/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9617/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9617/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9617/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1793/25000 : ℝ) ^ (1083/256 : ℝ) ≤ (1441524305945471/100000000000000000000 : ℝ) := by
    have hpowers : (1793/25000 : ℝ)^1083 ≤ (1441524305945471/100000000000000000000 : ℝ)^256 := by
      have hnat : (1793 : ℕ)^1083*100000000000000000000^256 ≤ 1441524305945471^256*25000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1793 25000 1441524305945471 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1793/25000 : ℝ)) (X := (1441524305945471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9617/50000 : ℝ) ^ (1083/256 : ℝ) ≤ (93600650108323303/100000000000000000000 : ℝ) := by
    have hpowers : (9617/50000 : ℝ)^1083 ≤ (93600650108323303/100000000000000000000 : ℝ)^256 := by
      have hnat : (9617 : ℕ)^1083*100000000000000000000^256 ≤ 93600650108323303^256*50000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9617 50000 93600650108323303 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9617/50000 : ℝ)) (X := (93600650108323303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001441524305945471/50000000000000000000 : ℝ) ≤ (10000068148875383/10000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50001441524305945471/50000000000000000000 : ℝ)^256 ≤ (10000068148875383/10000000000000000 : ℝ)^1083 := by
      have hnat : (50001441524305945471 : ℕ)^256*10000000000000000^1083 ≤ 10000068148875383^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001441524305945471 50000000000000000000 10000068148875383 10000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000068148875383/10000000000000000 : ℝ)) (X := (50001441524305945471/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50047521087207134387/50000000000000000000 : ℝ) ≤ (1250280724519997/1250000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50047521087207134387/50000000000000000000 : ℝ)^256 ≤ (1250280724519997/1250000000000000 : ℝ)^1083 := by
      have hnat : (50047521087207134387 : ℕ)^256*1250000000000000^1083 ≤ 1250280724519997^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047521087207134387 50000000000000000000 1250280724519997 1250000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250280724519997/1250000000000000 : ℝ)) (X := (50047521087207134387/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50093600650108323303/50000000000000000000 : ℝ) ≤ (10004423443444569/10000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50093600650108323303/50000000000000000000 : ℝ)^256 ≤ (10004423443444569/10000000000000000 : ℝ)^1083 := by
      have hnat : (50093600650108323303 : ℕ)^256*10000000000000000^1083 ≤ 10004423443444569^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50093600650108323303 50000000000000000000 10004423443444569 10000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004423443444569/10000000000000000 : ℝ)) (X := (50093600650108323303/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1441524305945471/100000000000000000000 : ℝ) ≤ ((369906705027867079/370000000000000000 : ℝ)+2*(2177647284593/1206200000000000 : ℝ)*(1793/25000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (369906705027867079/370000000000000000 : ℝ)+2*(2177647284593/1206200000000000 : ℝ)*(1793/25000 : ℝ)=(10000068148875383/10000000000000000 : ℝ) by norm_num, show 1+2*(1441524305945471/100000000000000000000 : ℝ)=(50001441524305945471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93600650108323303/100000000000000000000 : ℝ)+(1441524305945471/100000000000000000000 : ℝ) ≤ ((369906705027867079/370000000000000000 : ℝ)+(2177647284593/1206200000000000 : ℝ)*((9617/50000 : ℝ)+(1793/25000 : ℝ)))^(1083/256 : ℝ) := by
    rw [show (369906705027867079/370000000000000000 : ℝ)+(2177647284593/1206200000000000 : ℝ)*((9617/50000 : ℝ)+(1793/25000 : ℝ))=(1250280724519997/1250000000000000 : ℝ) by norm_num, show 1+(93600650108323303/100000000000000000000 : ℝ)+(1441524305945471/100000000000000000000 : ℝ)=(50047521087207134387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93600650108323303/100000000000000000000 : ℝ) ≤ ((369906705027867079/370000000000000000 : ℝ)+2*(2177647284593/1206200000000000 : ℝ)*(9617/50000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (369906705027867079/370000000000000000 : ℝ)+2*(2177647284593/1206200000000000 : ℝ)*(9617/50000 : ℝ)=(10004423443444569/10000000000000000 : ℝ) by norm_num, show 1+2*(93600650108323303/100000000000000000000 : ℝ)=(50093600650108323303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (369906705027867079/370000000000000000 : ℝ)*(X 1 0+X 2 0)+(2177647284593/1206200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (1793/25000 : ℝ)) (hi := (9617/50000 : ℝ)) (c := (369906705027867079/370000000000000000 : ℝ)) (alpha := (2177647284593/1206200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (369906705027867079/370000000000000000 : ℝ)*(X 0 1+X 2 1)+(2177647284593/1206200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (1793/25000 : ℝ)) (hi := (9617/50000 : ℝ)) (c := (369906705027867079/370000000000000000 : ℝ)) (alpha := (2177647284593/1206200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (369906705027867079/370000000000000000 : ℝ)*(X 0 2+X 1 2)+(2177647284593/1206200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (1793/25000 : ℝ)) (hi := (9617/50000 : ℝ)) (c := (369906705027867079/370000000000000000 : ℝ)) (alpha := (2177647284593/1206200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2008837863/10000000000 : ℝ)*X 0 0+(2735782187/5000000000 : ℝ)*X 0 1+(5190709001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363812629/10000000000 : ℝ)*X 1 0+(-1076860209/5000000000 : ℝ)*X 1 1+(5190709157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5363812599/10000000000 : ℝ)*X 2 0+(2595354587/5000000000 : ℝ)*X 2 1+(-538430109/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156547307/5000000000 : ℝ)*X 0 0+(2012482423/5000000000 : ℝ)*X 0 1+(924020977/2000000000 : ℝ)*X 0 2+(2156547307/5000000000 : ℝ)*X 1 0+(2012482423/5000000000 : ℝ)*X 1 1+(924020977/2000000000 : ℝ)*X 1 2+(2156547307/5000000000 : ℝ)*X 2 0+(2012482423/5000000000 : ℝ)*X 2 1+(924020977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200889547/1000000000 : ℝ)*X 0 0+(1038482419/2000000000 : ℝ)*X 0 1+(5469846409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330698999/625000000 : ℝ)*X 1 0+(-468645731/2500000000 : ℝ)*X 1 1+(2734923169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529118393/1000000000 : ℝ)*X 2 0+(5469846409/10000000000 : ℝ)*X 2 1+(-18745829/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67394013/156250000 : ℝ)*X 0 0+(4616496341/10000000000 : ℝ)*X 0 1+(4028604891/10000000000 : ℝ)*X 0 2+(67394013/156250000 : ℝ)*X 1 0+(4616496341/10000000000 : ℝ)*X 1 1+(4028604891/10000000000 : ℝ)*X 1 2+(67394013/156250000 : ℝ)*X 2 0+(4616496341/10000000000 : ℝ)*X 2 1+(4028604891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4469988146815068345792026301/1507750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389562023/100000000000000 : ℝ)*(base19) + (347987427/100000000000000 : ℝ)*(base23) + (5809071/50000000000000 : ℝ)*(lower2) + (34951447/50000000000000 : ℝ)*(upper3) + (2165711/6250000000000 : ℝ)*(upper5) + (1310211580554429/50000000000000 : ℝ)*(major0) + (1310211580554429/50000000000000 : ℝ)*(major1) + (1310211580554429/50000000000000 : ℝ)*(major2) + (35605583108493/1000000000000 : ℝ)*(sp0) + (1780282059361569/50000000000000 : ℝ)*(sp1) + (712112832059547/20000000000000 : ℝ)*(sp2) + (1680279074143537/100000000000000 : ℝ)*(sp3) + (3098717931/50000000000000 : ℝ)*(sp4) + (1320483261/50000000000000 : ℝ)*(sp7) + (84014085755503/5000000000000 : ℝ)*(f.failure) + (1780282254142581/50000000000000 : ℝ)*(f.sum) + (192520352020187/30155000000000000000000000000 : ℝ)*base65 + (21818553242698058767/3015500000000000000000000000000000 : ℝ)*base68 + (21619058401731441233/3015500000000000000000000000000000 : ℝ)*base69 + (24998192664636941233/3015500000000000000000000000000000 : ℝ)*base71 + (15273856496297/30155000000000000000000000000 : ℝ)*base73 + (5542505737707441233/3015500000000000000000000000000000 : ℝ)*base75 + (14066240846960441233/3015500000000000000000000000000000 : ℝ)*base77 + (4441830385598058767/3015500000000000000000000000000000 : ℝ)*base80 + (6293256727807/1884687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2076627/250000000000000000000 : ℝ)*base89 + (2076627/250000000000000000000 : ℝ)*base91 + (2076627/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16330524238257638756156880069/1507750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2177463103/100000000000000 : ℝ)*(base19) + (2351885697/100000000000000 : ℝ)*(base23) + (6093521/2500000000000 : ℝ)*(upper3) + (89223757/100000000000000 : ℝ)*(lower4) + (101051863/50000000000000 : ℝ)*(upper5) + (1326362310369767/50000000000000 : ℝ)*(major0) + (1326362310369767/50000000000000 : ℝ)*(major1) + (1326362310369767/50000000000000 : ℝ)*(major2) + (12844791469/50000000000000 : ℝ)*(sp1) + (28791722607/100000000000000 : ℝ)*(sp2) + (90111366277827/2500000000000 : ℝ)*(sp4) + (1802213392033519/50000000000000 : ℝ)*(sp5) + (450552938438097/12500000000000 : ℝ)*(sp6) + (850497114665393/50000000000000 : ℝ)*(sp7) + (850497114665393/50000000000000 : ℝ)*(f.failure) + (90111366277827/2500000000000 : ℝ)*(f.sum) + (29891151024729/30155000000000000000000000000 : ℝ)*base66 + (22189721585329246659/3015500000000000000000000000000000 : ℝ)*base67 + (16270152090319246659/3015500000000000000000000000000000 : ℝ)*base69 + (21858388336169246659/3015500000000000000000000000000000 : ℝ)*base71 + (185254989341181/30155000000000000000000000000 : ℝ)*base73 + (10699195594274246659/3015500000000000000000000000000000 : ℝ)*base75 + (526946755044746659/3015500000000000000000000000000000 : ℝ)*base77 + (12638597556598246659/3015500000000000000000000000000000 : ℝ)*base79 + (222258779552361/30155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (33061363/2500000000000000000000 : ℝ)*base90 + (33061363/2500000000000000000000 : ℝ)*base92 + (33061363/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1373_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1373_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1373_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15987/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1373_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1373_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1373_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15987/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1373_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

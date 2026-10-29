-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1517_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:31.108822+00:00
-- url     : https://prove2.me/submissions/d390b032-2668-4691-884e-7efba6452c14

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
theorem support_rectangle_w1517_s6_0 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372131543/2000000000 : ℝ)*x 0 + (339536377/625000000 : ℝ)*x 1 + (5217885541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372131543/2000000000 : ℝ)^4531 ≤ (11387234533649/100000000000000 : ℝ)^3507 := by
    have hnat : (372131543 : ℕ)^4531*100000000000000^3507 ≤ 11387234533649^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372131543 2000000000 11387234533649 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339536377/625000000 : ℝ)^4531 ≤ (4546021183491/10000000000000 : ℝ)^3507 := by
    have hnat : (339536377 : ℕ)^4531*10000000000000^3507 ≤ 4546021183491^3507*625000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339536377 625000000 4546021183491 10000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217885541/10000000000 : ℝ)^4531 ≤ (10788138401339/25000000000000 : ℝ)^3507 := by
    have hnat : (5217885541 : ℕ)^4531*25000000000000^3507 ≤ 10788138401339^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217885541 10000000000 10788138401339 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372131543/2000000000 : ℝ), (339536377/625000000 : ℝ), (5217885541/10000000000 : ℝ)] ![(11387234533649/100000000000000 : ℝ), (4546021183491/10000000000000 : ℝ), (10788138401339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372131543/2000000000 : ℝ)|^4531 ≤ (11387234533649/100000000000000 : ℝ)^3507
        have hw : |(-372131543/2000000000 : ℝ)|=(372131543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339536377/625000000 : ℝ)|^4531 ≤ (4546021183491/10000000000000 : ℝ)^3507
        have hw : |(339536377/625000000 : ℝ)|=(339536377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217885541/10000000000 : ℝ)|^4531 ≤ (10788138401339/25000000000000 : ℝ)^3507
        have hw : |(5217885541/10000000000 : ℝ)|=(5217885541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_1 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070262057/2000000000 : ℝ)*x 0 + (-246325463/1250000000 : ℝ)*x 1 + (5217885673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070262057/2000000000 : ℝ)^4531 ≤ (44583473276357/100000000000000 : ℝ)^3507 := by
    have hnat : (1070262057 : ℕ)^4531*100000000000000^3507 ≤ 44583473276357^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070262057 2000000000 44583473276357 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246325463/1250000000 : ℝ)^4531 ≤ (12263971681657/100000000000000 : ℝ)^3507 := by
    have hnat : (246325463 : ℕ)^4531*100000000000000^3507 ≤ 12263971681657^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246325463 1250000000 12263971681657 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217885673/10000000000 : ℝ)^4531 ≤ (21576277507881/50000000000000 : ℝ)^3507 := by
    have hnat : (5217885673 : ℕ)^4531*50000000000000^3507 ≤ 21576277507881^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217885673 10000000000 21576277507881 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070262057/2000000000 : ℝ), (-246325463/1250000000 : ℝ), (5217885673/10000000000 : ℝ)] ![(44583473276357/100000000000000 : ℝ), (12263971681657/100000000000000 : ℝ), (21576277507881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070262057/2000000000 : ℝ)|^4531 ≤ (44583473276357/100000000000000 : ℝ)^3507
        have hw : |(1070262057/2000000000 : ℝ)|=(1070262057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246325463/1250000000 : ℝ)|^4531 ≤ (12263971681657/100000000000000 : ℝ)^3507
        have hw : |(-246325463/1250000000 : ℝ)|=(246325463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217885673/10000000000 : ℝ)|^4531 ≤ (21576277507881/50000000000000 : ℝ)^3507
        have hw : |(5217885673/10000000000 : ℝ)|=(5217885673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_2 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351310323/10000000000 : ℝ)*x 0 + (1304471389/2500000000 : ℝ)*x 1 + (-1970603811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351310323/10000000000 : ℝ)^4531 ≤ (44583473685387/100000000000000 : ℝ)^3507 := by
    have hnat : (5351310323 : ℕ)^4531*100000000000000^3507 ≤ 44583473685387^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351310323 10000000000 44583473685387 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304471389/2500000000 : ℝ)^4531 ≤ (43152553765629/100000000000000 : ℝ)^3507 := by
    have hnat : (1304471389 : ℕ)^4531*100000000000000^3507 ≤ 43152553765629^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304471389 2500000000 43152553765629 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970603811/10000000000 : ℝ)^4531 ≤ (2452794508401/20000000000000 : ℝ)^3507 := by
    have hnat : (1970603811 : ℕ)^4531*20000000000000^3507 ≤ 2452794508401^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970603811 10000000000 2452794508401 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351310323/10000000000 : ℝ), (1304471389/2500000000 : ℝ), (-1970603811/10000000000 : ℝ)] ![(44583473685387/100000000000000 : ℝ), (43152553765629/100000000000000 : ℝ), (2452794508401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351310323/10000000000 : ℝ)|^4531 ≤ (44583473685387/100000000000000 : ℝ)^3507
        have hw : |(5351310323/10000000000 : ℝ)|=(5351310323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304471389/2500000000 : ℝ)|^4531 ≤ (43152553765629/100000000000000 : ℝ)^3507
        have hw : |(1304471389/2500000000 : ℝ)|=(1304471389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970603811/10000000000 : ℝ)|^4531 ≤ (2452794508401/20000000000000 : ℝ)^3507
        have hw : |(-1970603811/10000000000 : ℝ)|=(1970603811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_3 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133724783/5000000000 : ℝ)*x 0 + (2014540801/5000000000 : ℝ)*x 1 + (903528017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133724783/5000000000 : ℝ)^4531 ≤ (8319978765619/25000000000000 : ℝ)^3507 := by
    have hnat : (2133724783 : ℕ)^4531*25000000000000^3507 ≤ 8319978765619^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133724783 5000000000 8319978765619 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014540801/5000000000 : ℝ)^4531 ≤ (30898058213173/100000000000000 : ℝ)^3507 := by
    have hnat : (2014540801 : ℕ)^4531*100000000000000^3507 ≤ 30898058213173^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014540801 5000000000 30898058213173 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903528017/2000000000 : ℝ)^4531 ≤ (17911013351083/50000000000000 : ℝ)^3507 := by
    have hnat : (903528017 : ℕ)^4531*50000000000000^3507 ≤ 17911013351083^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903528017 2000000000 17911013351083 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133724783/5000000000 : ℝ), (2014540801/5000000000 : ℝ), (903528017/2000000000 : ℝ)] ![(8319978765619/25000000000000 : ℝ), (30898058213173/100000000000000 : ℝ), (17911013351083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133724783/5000000000 : ℝ)|^4531 ≤ (8319978765619/25000000000000 : ℝ)^3507
        have hw : |(2133724783/5000000000 : ℝ)|=(2133724783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014540801/5000000000 : ℝ)|^4531 ≤ (30898058213173/100000000000000 : ℝ)^3507
        have hw : |(2014540801/5000000000 : ℝ)|=(2014540801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903528017/2000000000 : ℝ)|^4531 ≤ (17911013351083/50000000000000 : ℝ)^3507
        have hw : |(903528017/2000000000 : ℝ)|=(903528017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_4 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1860686209/10000000000 : ℝ)*x 0 + (5218992213/10000000000 : ℝ)*x 1 + (339466713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1860686209/10000000000 : ℝ)^4531 ≤ (11387459835347/100000000000000 : ℝ)^3507 := by
    have hnat : (1860686209 : ℕ)^4531*100000000000000^3507 ≤ 11387459835347^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860686209 10000000000 11387459835347 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218992213/10000000000 : ℝ)^4531 ≤ (43164378645327/100000000000000 : ℝ)^3507 := by
    have hnat : (5218992213 : ℕ)^4531*100000000000000^3507 ≤ 43164378645327^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218992213 10000000000 43164378645327 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339466713/625000000 : ℝ)^4531 ≤ (1817926460309/4000000000000 : ℝ)^3507 := by
    have hnat : (339466713 : ℕ)^4531*4000000000000^3507 ≤ 1817926460309^3507*625000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339466713 625000000 1817926460309 4000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1860686209/10000000000 : ℝ), (5218992213/10000000000 : ℝ), (339466713/625000000 : ℝ)] ![(11387459835347/100000000000000 : ℝ), (43164378645327/100000000000000 : ℝ), (1817926460309/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1860686209/10000000000 : ℝ)|^4531 ≤ (11387459835347/100000000000000 : ℝ)^3507
        have hw : |(-1860686209/10000000000 : ℝ)|=(1860686209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218992213/10000000000 : ℝ)|^4531 ≤ (43164378645327/100000000000000 : ℝ)^3507
        have hw : |(5218992213/10000000000 : ℝ)|=(5218992213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339466713/625000000 : ℝ)|^4531 ≤ (1817926460309/4000000000000 : ℝ)^3507
        have hw : |(339466713/625000000 : ℝ)|=(339466713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_5 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294907137/10000000000 : ℝ)*x 0 + (-70280859/400000000 : ℝ)*x 1 + (2715734199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294907137/10000000000 : ℝ)^4531 ≤ (43977288628029/100000000000000 : ℝ)^3507 := by
    have hnat : (5294907137 : ℕ)^4531*100000000000000^3507 ≤ 43977288628029^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294907137 10000000000 43977288628029 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70280859/400000000 : ℝ)^4531 ≤ (5287269572933/50000000000000 : ℝ)^3507 := by
    have hnat : (70280859 : ℕ)^4531*50000000000000^3507 ≤ 5287269572933^3507*400000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70280859 400000000 5287269572933 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715734199/5000000000 : ℝ)^4531 ≤ (5681021526301/12500000000000 : ℝ)^3507 := by
    have hnat : (2715734199 : ℕ)^4531*12500000000000^3507 ≤ 5681021526301^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715734199 5000000000 5681021526301 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294907137/10000000000 : ℝ), (-70280859/400000000 : ℝ), (2715734199/5000000000 : ℝ)] ![(43977288628029/100000000000000 : ℝ), (5287269572933/50000000000000 : ℝ), (5681021526301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294907137/10000000000 : ℝ)|^4531 ≤ (43977288628029/100000000000000 : ℝ)^3507
        have hw : |(5294907137/10000000000 : ℝ)|=(5294907137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70280859/400000000 : ℝ)|^4531 ≤ (5287269572933/50000000000000 : ℝ)^3507
        have hw : |(-70280859/400000000 : ℝ)|=(70280859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715734199/5000000000 : ℝ)|^4531 ≤ (5681021526301/12500000000000 : ℝ)^3507
        have hw : |(2715734199/5000000000 : ℝ)|=(2715734199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_6 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294907627/10000000000 : ℝ)*x 0 + (2715734123/5000000000 : ℝ)*x 1 + (-1757021011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294907627/10000000000 : ℝ)^4531 ≤ (43977293886077/100000000000000 : ℝ)^3507 := by
    have hnat : (5294907627 : ℕ)^4531*100000000000000^3507 ≤ 43977293886077^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294907627 10000000000 43977293886077 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715734123/5000000000 : ℝ)^4531 ≤ (88765958139/195312500000 : ℝ)^3507 := by
    have hnat : (2715734123 : ℕ)^4531*195312500000^3507 ≤ 88765958139^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715734123 5000000000 88765958139 195312500000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1757021011/10000000000 : ℝ)^4531 ≤ (2114907107583/20000000000000 : ℝ)^3507 := by
    have hnat : (1757021011 : ℕ)^4531*20000000000000^3507 ≤ 2114907107583^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757021011 10000000000 2114907107583 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294907627/10000000000 : ℝ), (2715734123/5000000000 : ℝ), (-1757021011/10000000000 : ℝ)] ![(43977293886077/100000000000000 : ℝ), (88765958139/195312500000 : ℝ), (2114907107583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294907627/10000000000 : ℝ)|^4531 ≤ (43977293886077/100000000000000 : ℝ)^3507
        have hw : |(5294907627/10000000000 : ℝ)|=(5294907627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715734123/5000000000 : ℝ)|^4531 ≤ (88765958139/195312500000 : ℝ)^3507
        have hw : |(2715734123/5000000000 : ℝ)|=(2715734123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1757021011/10000000000 : ℝ)|^4531 ≤ (2114907107583/20000000000000 : ℝ)^3507
        have hw : |(-1757021011/10000000000 : ℝ)|=(1757021011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s6_7 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133758003/5000000000 : ℝ)*x 0 + (4515121633/10000000000 : ℝ)*x 1 + (403161763/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133758003/5000000000 : ℝ)^4531 ≤ (4160073061087/12500000000000 : ℝ)^3507 := by
    have hnat : (2133758003 : ℕ)^4531*12500000000000^3507 ≤ 4160073061087^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133758003 5000000000 4160073061087 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515121633/10000000000 : ℝ)^4531 ≤ (8949057040271/25000000000000 : ℝ)^3507 := by
    have hnat : (4515121633 : ℕ)^4531*25000000000000^3507 ≤ 8949057040271^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515121633 10000000000 8949057040271 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403161763/1000000000 : ℝ)^4531 ≤ (15461593669041/50000000000000 : ℝ)^3507 := by
    have hnat : (403161763 : ℕ)^4531*50000000000000^3507 ≤ 15461593669041^3507*1000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403161763 1000000000 15461593669041 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133758003/5000000000 : ℝ), (4515121633/10000000000 : ℝ), (403161763/1000000000 : ℝ)] ![(4160073061087/12500000000000 : ℝ), (8949057040271/25000000000000 : ℝ), (15461593669041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133758003/5000000000 : ℝ)|^4531 ≤ (4160073061087/12500000000000 : ℝ)^3507
        have hw : |(2133758003/5000000000 : ℝ)|=(2133758003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515121633/10000000000 : ℝ)|^4531 ≤ (8949057040271/25000000000000 : ℝ)^3507
        have hw : |(4515121633/10000000000 : ℝ)|=(4515121633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403161763/1000000000 : ℝ)|^4531 ≤ (15461593669041/50000000000000 : ℝ)^3507
        have hw : |(403161763/1000000000 : ℝ)|=(403161763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1517_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2187/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5467/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5467/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5467/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5467/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5467/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5467/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5467/50000 : ℝ) ^ (4529/1024 : ℝ) ≤ (5606121499992441/100000000000000000000 : ℝ) := by
    have hpowers : (5467/50000 : ℝ)^4529 ≤ (5606121499992441/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5467 : ℕ)^4529*100000000000000000000^1024 ≤ 5606121499992441^1024*50000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5467 50000 5606121499992441 100000000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5467/50000 : ℝ)) (X := (5606121499992441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4529/1024 : ℝ) ≤ (1632034899609953/6250000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4529 ≤ (1632034899609953/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4529*6250000000000000000^1024 ≤ 1632034899609953^1024*100000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 1632034899609953 6250000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (1632034899609953/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005606121499992441/50000000000000000000 : ℝ) ≤ (10000253496108133/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (50005606121499992441/50000000000000000000 : ℝ)^1024 ≤ (10000253496108133/10000000000000000 : ℝ)^4529 := by
      have hnat : (50005606121499992441 : ℕ)^1024*10000000000000000^4529 ≤ 10000253496108133^4529*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005606121499992441 50000000000000000000 10000253496108133 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000253496108133/10000000000000000 : ℝ)) (X := (50005606121499992441/50000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031718679893751689/100000000000000000000 : ℝ) ≤ (10000717066516071/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (100031718679893751689/100000000000000000000 : ℝ)^1024 ≤ (10000717066516071/10000000000000000 : ℝ)^4529 := by
      have hnat : (100031718679893751689 : ℕ)^1024*10000000000000000^4529 ≤ 10000717066516071^4529*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031718679893751689 100000000000000000000 10000717066516071 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000717066516071/10000000000000000 : ℝ)) (X := (100031718679893751689/100000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126632034899609953/3125000000000000000 : ℝ) ≤ (10001180636924009/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (3126632034899609953/3125000000000000000 : ℝ)^1024 ≤ (10001180636924009/10000000000000000 : ℝ)^4529 := by
      have hnat : (3126632034899609953 : ℕ)^1024*10000000000000000^4529 ≤ 10001180636924009^4529*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126632034899609953 3125000000000000000 10001180636924009 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001180636924009/10000000000000000 : ℝ)) (X := (3126632034899609953/3125000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5606121499992441/100000000000000000000 : ℝ) ≤ ((45481015796115108833/45490000000000000000 : ℝ)+2*(231785203969/227450000000000 : ℝ)*(5467/50000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (45481015796115108833/45490000000000000000 : ℝ)+2*(231785203969/227450000000000 : ℝ)*(5467/50000 : ℝ)=(10000253496108133/10000000000000000 : ℝ) by norm_num, show 1+2*(5606121499992441/100000000000000000000 : ℝ)=(50005606121499992441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1632034899609953/6250000000000000000 : ℝ)+(5606121499992441/100000000000000000000 : ℝ) ≤ ((45481015796115108833/45490000000000000000 : ℝ)+(231785203969/227450000000000 : ℝ)*((15483/100000 : ℝ)+(5467/50000 : ℝ)))^(4529/1024 : ℝ) := by
    rw [show (45481015796115108833/45490000000000000000 : ℝ)+(231785203969/227450000000000 : ℝ)*((15483/100000 : ℝ)+(5467/50000 : ℝ))=(10000717066516071/10000000000000000 : ℝ) by norm_num, show 1+(1632034899609953/6250000000000000000 : ℝ)+(5606121499992441/100000000000000000000 : ℝ)=(100031718679893751689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1632034899609953/6250000000000000000 : ℝ) ≤ ((45481015796115108833/45490000000000000000 : ℝ)+2*(231785203969/227450000000000 : ℝ)*(15483/100000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (45481015796115108833/45490000000000000000 : ℝ)+2*(231785203969/227450000000000 : ℝ)*(15483/100000 : ℝ)=(10001180636924009/10000000000000000 : ℝ) by norm_num, show 1+2*(1632034899609953/6250000000000000000 : ℝ)=(3126632034899609953/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45481015796115108833/45490000000000000000 : ℝ)*(X 1 0+X 2 0)+(231785203969/227450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (5467/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (45481015796115108833/45490000000000000000 : ℝ)) (alpha := (231785203969/227450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45481015796115108833/45490000000000000000 : ℝ)*(X 0 1+X 2 1)+(231785203969/227450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (5467/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (45481015796115108833/45490000000000000000 : ℝ)) (alpha := (231785203969/227450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45481015796115108833/45490000000000000000 : ℝ)*(X 0 2+X 1 2)+(231785203969/227450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (5467/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (45481015796115108833/45490000000000000000 : ℝ)) (alpha := (231785203969/227450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-372131543/2000000000 : ℝ)*X 0 0+(339536377/625000000 : ℝ)*X 0 1+(5217885541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070262057/2000000000 : ℝ)*X 1 0+(-246325463/1250000000 : ℝ)*X 1 1+(5217885673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351310323/10000000000 : ℝ)*X 2 0+(1304471389/2500000000 : ℝ)*X 2 1+(-1970603811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133724783/5000000000 : ℝ)*X 0 0+(2014540801/5000000000 : ℝ)*X 0 1+(903528017/2000000000 : ℝ)*X 0 2+(2133724783/5000000000 : ℝ)*X 1 0+(2014540801/5000000000 : ℝ)*X 1 1+(903528017/2000000000 : ℝ)*X 1 2+(2133724783/5000000000 : ℝ)*X 2 0+(2014540801/5000000000 : ℝ)*X 2 1+(903528017/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1860686209/10000000000 : ℝ)*X 0 0+(5218992213/10000000000 : ℝ)*X 0 1+(339466713/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294907137/10000000000 : ℝ)*X 1 0+(-70280859/400000000 : ℝ)*X 1 1+(2715734199/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294907627/10000000000 : ℝ)*X 2 0+(2715734123/5000000000 : ℝ)*X 2 1+(-1757021011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133758003/5000000000 : ℝ)*X 0 0+(4515121633/10000000000 : ℝ)*X 0 1+(403161763/1000000000 : ℝ)*X 0 2+(2133758003/5000000000 : ℝ)*X 1 0+(4515121633/10000000000 : ℝ)*X 1 1+(403161763/1000000000 : ℝ)*X 1 2+(2133758003/5000000000 : ℝ)*X 2 0+(4515121633/10000000000 : ℝ)*X 2 1+(403161763/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18669844375550130506695173501/2274500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (686895221/50000000000000 : ℝ)*(base19) + (659583491/50000000000000 : ℝ)*(base23) + (23465137/50000000000000 : ℝ)*(lower2) + (71202099/25000000000000 : ℝ)*(upper3) + (123789173/100000000000000 : ℝ)*(upper5) + (3352320165029623/100000000000000 : ℝ)*(major0) + (3352320165029623/100000000000000 : ℝ)*(major1) + (419040020628703/12500000000000 : ℝ)*(major2) + (1164440454121861/25000000000000 : ℝ)*(sp0) + (1164445186440151/25000000000000 : ℝ)*(sp1) + (931556160076813/20000000000000 : ℝ)*(sp2) + (511711703349707/25000000000000 : ℝ)*(sp3) + (20303063603/100000000000000 : ℝ)*(sp4) + (2224699679/20000000000000 : ℝ)*(sp7) + (1023428968448611/50000000000000 : ℝ)*(f.failure) + (4657782119551047/100000000000000 : ℝ)*(f.sum) + (45291994647813/5686250000000000000000000000 : ℝ)*base66 + (14293369395916840041/4549000000000000000000000000000000 : ℝ)*base68 + (1909950338090558599/568625000000000000000000000000000 : ℝ)*base69 + (1344454873103159959/4549000000000000000000000000000000 : ℝ)*base71 + (4741223470883/5686250000000000000000000000 : ℝ)*base74 + (2252132791473558599/568625000000000000000000000000000 : ℝ)*base75 + (85434004367085640041/4549000000000000000000000000000000 : ℝ)*base78 + (52038815594367640041/4549000000000000000000000000000000 : ℝ)*base80 + (108404576106301/22745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9257371/5000000000000000000000 : ℝ)*base90 + (9257371/5000000000000000000000 : ℝ)*base92 + (59257371/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56276526777821482393179/22745000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164805047/50000000000000 : ℝ)*(base23) + (148408951/50000000000000 : ℝ)*(lower1) + (227919723/100000000000000 : ℝ)*(lower2) + (5284929/3125000000000 : ℝ)*(upper3) + (22849457/20000000000000 : ℝ)*(lower4) + (17651373/20000000000000 : ℝ)*(upper5) + (211707891341909/6250000000000 : ℝ)*(major0) + (211707891341909/6250000000000 : ℝ)*(major1) + (211707891341909/6250000000000 : ℝ)*(major2) + (10209322917/100000000000000 : ℝ)*(sp2) + (36768910148869/781250000000 : ℝ)*(sp4) + (36768910148869/781250000000 : ℝ)*(sp5) + (4706409960122221/100000000000000 : ℝ)*(sp6) + (2068231941411273/100000000000000 : ℝ)*(sp7) + (2068231941411273/100000000000000 : ℝ)*(f.failure) + (36768910148869/781250000000 : ℝ)*(f.sum) + (30544255283261/11372500000000000000000000000 : ℝ)*base65 + (676802995780369697/284312500000000000000000000000000 : ℝ)*base67 + (1098400021165192803/284312500000000000000000000000000 : ℝ)*base70 + (200849883458307197/284312500000000000000000000000000 : ℝ)*base71 + (16076664518433/22745000000000000000000000000 : ℝ)*base74 + (589085737314807197/284312500000000000000000000000000 : ℝ)*base75 + (7739102212067803/284312500000000000000000000000000 : ℝ)*base78 + (3624752102738255303/284312500000000000000000000000000 : ℝ)*base80 + (10854251818079/2843125000000000000000000000 : ℝ)*base81 + (86547953/10000000000000000000000 : ℝ)*base90 + (86547953/10000000000000000000000 : ℝ)*base92 + (86547953/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1517_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2187/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1517_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1517_box_0 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-823961597/5000000000 : ℝ)*x 0 + (5402290791/10000000000 : ℝ)*x 1 + (108045821/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823961597/5000000000 : ℝ)^4531 ≤ (2433505845291/25000000000000 : ℝ)^3507 := by
    have hnat : (823961597 : ℕ)^4531*25000000000000^3507 ≤ 2433505845291^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823961597 5000000000 2433505845291 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402290791/10000000000 : ℝ)^4531 ≤ (45132986906269/100000000000000 : ℝ)^3507 := by
    have hnat : (5402290791 : ℕ)^4531*100000000000000^3507 ≤ 45132986906269^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402290791 10000000000 45132986906269 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108045821/200000000 : ℝ)^4531 ≤ (45132989701863/100000000000000 : ℝ)^3507 := by
    have hnat : (108045821 : ℕ)^4531*100000000000000^3507 ≤ 45132989701863^3507*200000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108045821 200000000 45132989701863 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-823961597/5000000000 : ℝ), (5402290791/10000000000 : ℝ), (108045821/200000000 : ℝ)] ![(2433505845291/25000000000000 : ℝ), (45132986906269/100000000000000 : ℝ), (45132989701863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-823961597/5000000000 : ℝ)|^4531 ≤ (2433505845291/25000000000000 : ℝ)^3507
        have hw : |(-823961597/5000000000 : ℝ)|=(823961597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402290791/10000000000 : ℝ)|^4531 ≤ (45132986906269/100000000000000 : ℝ)^3507
        have hw : |(5402290791/10000000000 : ℝ)|=(5402290791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108045821/200000000 : ℝ)|^4531 ≤ (45132989701863/100000000000000 : ℝ)^3507
        have hw : |(108045821/200000000 : ℝ)|=(108045821/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_1 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658854919/1250000000 : ℝ)*x 0 + (-57197071/312500000 : ℝ)*x 1 + (5402290507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658854919/1250000000 : ℝ)^4531 ≤ (2185959790651/5000000000000 : ℝ)^3507 := by
    have hnat : (658854919 : ℕ)^4531*5000000000000^3507 ≤ 2185959790651^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658854919 1250000000 2185959790651 5000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57197071/312500000 : ℝ)^4531 ≤ (1114782033623/10000000000000 : ℝ)^3507 := by
    have hnat : (57197071 : ℕ)^4531*10000000000000^3507 ≤ 1114782033623^3507*312500000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57197071 312500000 1114782033623 10000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402290507/10000000000 : ℝ)^4531 ≤ (45132983840829/100000000000000 : ℝ)^3507 := by
    have hnat : (5402290507 : ℕ)^4531*100000000000000^3507 ≤ 45132983840829^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402290507 10000000000 45132983840829 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658854919/1250000000 : ℝ), (-57197071/312500000 : ℝ), (5402290507/10000000000 : ℝ)] ![(2185959790651/5000000000000 : ℝ), (1114782033623/10000000000000 : ℝ), (45132983840829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658854919/1250000000 : ℝ)|^4531 ≤ (2185959790651/5000000000000 : ℝ)^3507
        have hw : |(658854919/1250000000 : ℝ)|=(658854919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57197071/312500000 : ℝ)|^4531 ≤ (1114782033623/10000000000000 : ℝ)^3507
        have hw : |(-57197071/312500000 : ℝ)|=(57197071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402290507/10000000000 : ℝ)|^4531 ≤ (45132983840829/100000000000000 : ℝ)^3507
        have hw : |(5402290507/10000000000 : ℝ)|=(5402290507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_2 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054167933/2000000000 : ℝ)*x 0 + (2701145179/5000000000 : ℝ)*x 1 + (-36606121/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054167933/2000000000 : ℝ)^4531 ≤ (43719199167267/100000000000000 : ℝ)^3507 := by
    have hnat : (1054167933 : ℕ)^4531*100000000000000^3507 ≤ 43719199167267^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054167933 2000000000 43719199167267 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701145179/5000000000 : ℝ)^4531 ≤ (45132982232553/100000000000000 : ℝ)^3507 := by
    have hnat : (2701145179 : ℕ)^4531*100000000000000^3507 ≤ 45132982232553^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701145179 5000000000 45132982232553 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36606121/200000000 : ℝ)^4531 ≤ (2786954647323/25000000000000 : ℝ)^3507 := by
    have hnat : (36606121 : ℕ)^4531*25000000000000^3507 ≤ 2786954647323^3507*200000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36606121 200000000 2786954647323 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054167933/2000000000 : ℝ), (2701145179/5000000000 : ℝ), (-36606121/200000000 : ℝ)] ![(43719199167267/100000000000000 : ℝ), (45132982232553/100000000000000 : ℝ), (2786954647323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054167933/2000000000 : ℝ)|^4531 ≤ (43719199167267/100000000000000 : ℝ)^3507
        have hw : |(1054167933/2000000000 : ℝ)|=(1054167933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701145179/5000000000 : ℝ)|^4531 ≤ (45132982232553/100000000000000 : ℝ)^3507
        have hw : |(2701145179/5000000000 : ℝ)|=(2701145179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36606121/200000000 : ℝ)|^4531 ≤ (2786954647323/25000000000000 : ℝ)^3507
        have hw : |(-36606121/200000000 : ℝ)|=(36606121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_3 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4470285287/10000000000 : ℝ)*x 0 + (4172981191/10000000000 : ℝ)*x 1 + (2086490767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4470285287/10000000000 : ℝ)^4531 ≤ (17668818985881/50000000000000 : ℝ)^3507 := by
    have hnat : (4470285287 : ℕ)^4531*50000000000000^3507 ≤ 17668818985881^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4470285287 10000000000 17668818985881 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4172981191/10000000000 : ℝ)^4531 ≤ (32331179292239/100000000000000 : ℝ)^3507 := by
    have hnat : (4172981191 : ℕ)^4531*100000000000000^3507 ≤ 32331179292239^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172981191 10000000000 32331179292239 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086490767/5000000000 : ℝ)^4531 ≤ (32331182725663/100000000000000 : ℝ)^3507 := by
    have hnat : (2086490767 : ℕ)^4531*100000000000000^3507 ≤ 32331182725663^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086490767 5000000000 32331182725663 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4470285287/10000000000 : ℝ), (4172981191/10000000000 : ℝ), (2086490767/5000000000 : ℝ)] ![(17668818985881/50000000000000 : ℝ), (32331179292239/100000000000000 : ℝ), (32331182725663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4470285287/10000000000 : ℝ)|^4531 ≤ (17668818985881/50000000000000 : ℝ)^3507
        have hw : |(4470285287/10000000000 : ℝ)|=(4470285287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4172981191/10000000000 : ℝ)|^4531 ≤ (32331179292239/100000000000000 : ℝ)^3507
        have hw : |(4172981191/10000000000 : ℝ)|=(4172981191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086490767/5000000000 : ℝ)|^4531 ≤ (32331182725663/100000000000000 : ℝ)^3507
        have hw : |(2086490767/5000000000 : ℝ)|=(2086490767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_4 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1039413627/5000000000 : ℝ)*x 0 + (2621891917/5000000000 : ℝ)*x 1 + (2621892159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039413627/5000000000 : ℝ)^4531 ≤ (13141045957829/100000000000000 : ℝ)^3507 := by
    have hnat : (1039413627 : ℕ)^4531*100000000000000^3507 ≤ 13141045957829^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039413627 5000000000 13141045957829 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621891917/5000000000 : ℝ)^4531 ≤ (21714737211737/50000000000000 : ℝ)^3507 := by
    have hnat : (2621891917 : ℕ)^4531*50000000000000^3507 ≤ 21714737211737^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621891917 5000000000 21714737211737 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621892159/5000000000 : ℝ)^4531 ≤ (10857369900611/25000000000000 : ℝ)^3507 := by
    have hnat : (2621892159 : ℕ)^4531*25000000000000^3507 ≤ 10857369900611^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621892159 5000000000 10857369900611 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1039413627/5000000000 : ℝ), (2621891917/5000000000 : ℝ), (2621892159/5000000000 : ℝ)] ![(13141045957829/100000000000000 : ℝ), (21714737211737/50000000000000 : ℝ), (10857369900611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1039413627/5000000000 : ℝ)|^4531 ≤ (13141045957829/100000000000000 : ℝ)^3507
        have hw : |(-1039413627/5000000000 : ℝ)|=(1039413627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621891917/5000000000 : ℝ)|^4531 ≤ (21714737211737/50000000000000 : ℝ)^3507
        have hw : |(2621891917/5000000000 : ℝ)|=(2621891917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621892159/5000000000 : ℝ)|^4531 ≤ (10857369900611/25000000000000 : ℝ)^3507
        have hw : |(2621892159/5000000000 : ℝ)|=(2621892159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_5 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381152337/10000000000 : ℝ)*x 0 + (-1895762691/10000000000 : ℝ)*x 1 + (5243784091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381152337/10000000000 : ℝ)^4531 ≤ (44904953096469/100000000000000 : ℝ)^3507 := by
    have hnat : (5381152337 : ℕ)^4531*100000000000000^3507 ≤ 44904953096469^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381152337 10000000000 44904953096469 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895762691/10000000000 : ℝ)^4531 ≤ (2333113940757/20000000000000 : ℝ)^3507 := by
    have hnat : (1895762691 : ℕ)^4531*20000000000000^3507 ≤ 2333113940757^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895762691 10000000000 2333113940757 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243784091/10000000000 : ℝ)^4531 ≤ (5428684646683/12500000000000 : ℝ)^3507 := by
    have hnat : (5243784091 : ℕ)^4531*12500000000000^3507 ≤ 5428684646683^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243784091 10000000000 5428684646683 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381152337/10000000000 : ℝ), (-1895762691/10000000000 : ℝ), (5243784091/10000000000 : ℝ)] ![(44904953096469/100000000000000 : ℝ), (2333113940757/20000000000000 : ℝ), (5428684646683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381152337/10000000000 : ℝ)|^4531 ≤ (44904953096469/100000000000000 : ℝ)^3507
        have hw : |(5381152337/10000000000 : ℝ)|=(5381152337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895762691/10000000000 : ℝ)|^4531 ≤ (2333113940757/20000000000000 : ℝ)^3507
        have hw : |(-1895762691/10000000000 : ℝ)|=(1895762691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243784091/10000000000 : ℝ)|^4531 ≤ (5428684646683/12500000000000 : ℝ)^3507
        have hw : |(5243784091/10000000000 : ℝ)|=(5243784091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_6 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345288081/2500000000 : ℝ)*x 0 + (1310946033/2500000000 : ℝ)*x 1 + (-379152531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345288081/2500000000 : ℝ)^4531 ≤ (4490495295631/10000000000000 : ℝ)^3507 := by
    have hnat : (1345288081 : ℕ)^4531*10000000000000^3507 ≤ 4490495295631^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345288081 2500000000 4490495295631 10000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310946033/2500000000 : ℝ)^4531 ≤ (43429477612179/100000000000000 : ℝ)^3507 := by
    have hnat : (1310946033 : ℕ)^4531*100000000000000^3507 ≤ 43429477612179^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310946033 2500000000 43429477612179 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379152531/2000000000 : ℝ)^4531 ≤ (1458196177197/12500000000000 : ℝ)^3507 := by
    have hnat : (379152531 : ℕ)^4531*12500000000000^3507 ≤ 1458196177197^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379152531 2000000000 1458196177197 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345288081/2500000000 : ℝ), (1310946033/2500000000 : ℝ), (-379152531/2000000000 : ℝ)] ![(4490495295631/10000000000000 : ℝ), (43429477612179/100000000000000 : ℝ), (1458196177197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345288081/2500000000 : ℝ)|^4531 ≤ (4490495295631/10000000000000 : ℝ)^3507
        have hw : |(1345288081/2500000000 : ℝ)|=(1345288081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310946033/2500000000 : ℝ)|^4531 ≤ (43429477612179/100000000000000 : ℝ)^3507
        have hw : |(1310946033/2500000000 : ℝ)|=(1310946033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379152531/2000000000 : ℝ)|^4531 ≤ (1458196177197/12500000000000 : ℝ)^3507
        have hw : |(-379152531/2000000000 : ℝ)|=(379152531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_7 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4062170237/10000000000 : ℝ)*x 0 + (4376905143/10000000000 : ℝ)*x 1 + (4376905337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4062170237/10000000000 : ℝ)^4531 ≤ (15613145386491/50000000000000 : ℝ)^3507 := by
    have hnat : (4062170237 : ℕ)^4531*50000000000000^3507 ≤ 15613145386491^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4062170237 10000000000 15613145386491 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4376905143/10000000000 : ℝ)^4531 ≤ (34386853623857/100000000000000 : ℝ)^3507 := by
    have hnat : (4376905143 : ℕ)^4531*100000000000000^3507 ≤ 34386853623857^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376905143 10000000000 34386853623857 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4376905337/10000000000 : ℝ)^4531 ≤ (34386855593037/100000000000000 : ℝ)^3507 := by
    have hnat : (4376905337 : ℕ)^4531*100000000000000^3507 ≤ 34386855593037^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376905337 10000000000 34386855593037 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4062170237/10000000000 : ℝ), (4376905143/10000000000 : ℝ), (4376905337/10000000000 : ℝ)] ![(15613145386491/50000000000000 : ℝ), (34386853623857/100000000000000 : ℝ), (34386855593037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4062170237/10000000000 : ℝ)|^4531 ≤ (15613145386491/50000000000000 : ℝ)^3507
        have hw : |(4062170237/10000000000 : ℝ)|=(4062170237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4376905143/10000000000 : ℝ)|^4531 ≤ (34386853623857/100000000000000 : ℝ)^3507
        have hw : |(4376905143/10000000000 : ℝ)|=(4376905143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4376905337/10000000000 : ℝ)|^4531 ≤ (34386855593037/100000000000000 : ℝ)^3507
        have hw : |(4376905337/10000000000 : ℝ)|=(4376905337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_8 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993870229/5000000000 : ℝ)*x 0 + (641585381/1250000000 : ℝ)*x 1 + (2711364323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993870229/5000000000 : ℝ)^4531 ≤ (12401936579331/100000000000000 : ℝ)^3507 := by
    have hnat : (993870229 : ℕ)^4531*100000000000000^3507 ≤ 12401936579331^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993870229 5000000000 12401936579331 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641585381/1250000000 : ℝ)^4531 ≤ (21122176315411/50000000000000 : ℝ)^3507 := by
    have hnat : (641585381 : ℕ)^4531*50000000000000^3507 ≤ 21122176315411^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641585381 1250000000 21122176315411 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711364323/5000000000 : ℝ)^4531 ≤ (22676855392351/50000000000000 : ℝ)^3507 := by
    have hnat : (2711364323 : ℕ)^4531*50000000000000^3507 ≤ 22676855392351^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711364323 5000000000 22676855392351 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993870229/5000000000 : ℝ), (641585381/1250000000 : ℝ), (2711364323/5000000000 : ℝ)] ![(12401936579331/100000000000000 : ℝ), (21122176315411/50000000000000 : ℝ), (22676855392351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993870229/5000000000 : ℝ)|^4531 ≤ (12401936579331/100000000000000 : ℝ)^3507
        have hw : |(-993870229/5000000000 : ℝ)|=(993870229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641585381/1250000000 : ℝ)|^4531 ≤ (21122176315411/50000000000000 : ℝ)^3507
        have hw : |(641585381/1250000000 : ℝ)|=(641585381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711364323/5000000000 : ℝ)|^4531 ≤ (22676855392351/50000000000000 : ℝ)^3507
        have hw : |(2711364323/5000000000 : ℝ)|=(2711364323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_9 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256609511/10000000000 : ℝ)*x 0 + (-182162151/1000000000 : ℝ)*x 1 + (5422728643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256609511/10000000000 : ℝ)^4531 ≤ (5445845333443/12500000000000 : ℝ)^3507 := by
    have hnat : (5256609511 : ℕ)^4531*12500000000000^3507 ≤ 5445845333443^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256609511 10000000000 5445845333443 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182162151/1000000000 : ℝ)^4531 ≤ (11079526561663/100000000000000 : ℝ)^3507 := by
    have hnat : (182162151 : ℕ)^4531*100000000000000^3507 ≤ 11079526561663^3507*1000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182162151 1000000000 11079526561663 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422728643/10000000000 : ℝ)^4531 ≤ (9070742150457/20000000000000 : ℝ)^3507 := by
    have hnat : (5422728643 : ℕ)^4531*20000000000000^3507 ≤ 9070742150457^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422728643 10000000000 9070742150457 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256609511/10000000000 : ℝ), (-182162151/1000000000 : ℝ), (5422728643/10000000000 : ℝ)] ![(5445845333443/12500000000000 : ℝ), (11079526561663/100000000000000 : ℝ), (9070742150457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256609511/10000000000 : ℝ)|^4531 ≤ (5445845333443/12500000000000 : ℝ)^3507
        have hw : |(5256609511/10000000000 : ℝ)|=(5256609511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182162151/1000000000 : ℝ)|^4531 ≤ (11079526561663/100000000000000 : ℝ)^3507
        have hw : |(-182162151/1000000000 : ℝ)|=(182162151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422728643/10000000000 : ℝ)|^4531 ≤ (9070742150457/20000000000000 : ℝ)^3507
        have hw : |(5422728643/10000000000 : ℝ)|=(5422728643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_10 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262830469/500000000 : ℝ)*x 0 + (1084545759/2000000000 : ℝ)*x 1 + (-45540537/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262830469/500000000 : ℝ)^4531 ≤ (21783380632399/50000000000000 : ℝ)^3507 := by
    have hnat : (262830469 : ℕ)^4531*50000000000000^3507 ≤ 21783380632399^3507*500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262830469 500000000 21783380632399 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084545759/2000000000 : ℝ)^4531 ≤ (88581469521/195312500000 : ℝ)^3507 := by
    have hnat : (1084545759 : ℕ)^4531*195312500000^3507 ≤ 88581469521^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084545759 2000000000 88581469521 195312500000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45540537/250000000 : ℝ)^4531 ≤ (5539763162959/50000000000000 : ℝ)^3507 := by
    have hnat : (45540537 : ℕ)^4531*50000000000000^3507 ≤ 5539763162959^3507*250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45540537 250000000 5539763162959 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262830469/500000000 : ℝ), (1084545759/2000000000 : ℝ), (-45540537/250000000 : ℝ)] ![(21783380632399/50000000000000 : ℝ), (88581469521/195312500000 : ℝ), (5539763162959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262830469/500000000 : ℝ)|^4531 ≤ (21783380632399/50000000000000 : ℝ)^3507
        have hw : |(262830469/500000000 : ℝ)|=(262830469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084545759/2000000000 : ℝ)|^4531 ≤ (88581469521/195312500000 : ℝ)^3507
        have hw : |(1084545759/2000000000 : ℝ)|=(1084545759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45540537/250000000 : ℝ)|^4531 ≤ (5539763162959/50000000000000 : ℝ)^3507
        have hw : |(-45540537/250000000 : ℝ)|=(45540537/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_11 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4521756879/10000000000 : ℝ)*x 0 + (4146654907/10000000000 : ℝ)*x 1 + (4146654831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4521756879/10000000000 : ℝ)^4531 ≤ (35864207396023/100000000000000 : ℝ)^3507 := by
    have hnat : (4521756879 : ℕ)^4531*100000000000000^3507 ≤ 35864207396023^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521756879 10000000000 35864207396023 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146654907/10000000000 : ℝ)^4531 ≤ (16033948335387/50000000000000 : ℝ)^3507 := by
    have hnat : (4146654907 : ℕ)^4531*50000000000000^3507 ≤ 16033948335387^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146654907 10000000000 16033948335387 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146654831/10000000000 : ℝ)^4531 ≤ (32067895911419/100000000000000 : ℝ)^3507 := by
    have hnat : (4146654831 : ℕ)^4531*100000000000000^3507 ≤ 32067895911419^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146654831 10000000000 32067895911419 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4521756879/10000000000 : ℝ), (4146654907/10000000000 : ℝ), (4146654831/10000000000 : ℝ)] ![(35864207396023/100000000000000 : ℝ), (16033948335387/50000000000000 : ℝ), (32067895911419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4521756879/10000000000 : ℝ)|^4531 ≤ (35864207396023/100000000000000 : ℝ)^3507
        have hw : |(4521756879/10000000000 : ℝ)|=(4521756879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146654907/10000000000 : ℝ)|^4531 ≤ (16033948335387/50000000000000 : ℝ)^3507
        have hw : |(4146654907/10000000000 : ℝ)|=(4146654907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146654831/10000000000 : ℝ)|^4531 ≤ (32067895911419/100000000000000 : ℝ)^3507
        have hw : |(4146654831/10000000000 : ℝ)|=(4146654831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_12 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1738933129/10000000000 : ℝ)*x 0 + (5509837729/10000000000 : ℝ)*x 1 + (1045750743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1738933129/10000000000 : ℝ)^4531 ≤ (5217050238207/50000000000000 : ℝ)^3507 := by
    have hnat : (1738933129 : ℕ)^4531*50000000000000^3507 ≤ 5217050238207^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738933129 10000000000 5217050238207 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509837729/10000000000 : ℝ)^4531 ≤ (23148592657213/50000000000000 : ℝ)^3507 := by
    have hnat : (5509837729 : ℕ)^4531*50000000000000^3507 ≤ 23148592657213^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509837729 10000000000 23148592657213 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045750743/2000000000 : ℝ)^4531 ≤ (5408589274431/12500000000000 : ℝ)^3507 := by
    have hnat : (1045750743 : ℕ)^4531*12500000000000^3507 ≤ 5408589274431^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045750743 2000000000 5408589274431 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1738933129/10000000000 : ℝ), (5509837729/10000000000 : ℝ), (1045750743/2000000000 : ℝ)] ![(5217050238207/50000000000000 : ℝ), (23148592657213/50000000000000 : ℝ), (5408589274431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1738933129/10000000000 : ℝ)|^4531 ≤ (5217050238207/50000000000000 : ℝ)^3507
        have hw : |(-1738933129/10000000000 : ℝ)|=(1738933129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509837729/10000000000 : ℝ)|^4531 ≤ (23148592657213/50000000000000 : ℝ)^3507
        have hw : |(5509837729/10000000000 : ℝ)|=(5509837729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045750743/2000000000 : ℝ)|^4531 ≤ (5408589274431/12500000000000 : ℝ)^3507
        have hw : |(1045750743/2000000000 : ℝ)|=(1045750743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_13 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391612489/10000000000 : ℝ)*x 0 + (-1901791549/10000000000 : ℝ)*x 1 + (5228753927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391612489/10000000000 : ℝ)^4531 ≤ (1406805022307/3125000000000 : ℝ)^3507 := by
    have hnat : (5391612489 : ℕ)^4531*3125000000000^3507 ≤ 1406805022307^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391612489 10000000000 1406805022307 3125000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901791549/10000000000 : ℝ)^4531 ≤ (11713522812949/100000000000000 : ℝ)^3507 := by
    have hnat : (1901791549 : ℕ)^4531*100000000000000^3507 ≤ 11713522812949^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901791549 10000000000 11713522812949 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228753927/10000000000 : ℝ)^4531 ≤ (21634358231011/50000000000000 : ℝ)^3507 := by
    have hnat : (5228753927 : ℕ)^4531*50000000000000^3507 ≤ 21634358231011^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228753927 10000000000 21634358231011 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391612489/10000000000 : ℝ), (-1901791549/10000000000 : ℝ), (5228753927/10000000000 : ℝ)] ![(1406805022307/3125000000000 : ℝ), (11713522812949/100000000000000 : ℝ), (21634358231011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391612489/10000000000 : ℝ)|^4531 ≤ (1406805022307/3125000000000 : ℝ)^3507
        have hw : |(5391612489/10000000000 : ℝ)|=(5391612489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901791549/10000000000 : ℝ)|^4531 ≤ (11713522812949/100000000000000 : ℝ)^3507
        have hw : |(-1901791549/10000000000 : ℝ)|=(1901791549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228753927/10000000000 : ℝ)|^4531 ≤ (21634358231011/50000000000000 : ℝ)^3507
        have hw : |(5228753927/10000000000 : ℝ)|=(5228753927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_14 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391612389/10000000000 : ℝ)*x 0 + (2614376989/5000000000 : ℝ)*x 1 + (-14857747/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391612389/10000000000 : ℝ)^4531 ≤ (45017759635067/100000000000000 : ℝ)^3507 := by
    have hnat : (5391612389 : ℕ)^4531*100000000000000^3507 ≤ 45017759635067^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391612389 10000000000 45017759635067 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614376989/5000000000 : ℝ)^4531 ≤ (43268717007283/100000000000000 : ℝ)^3507 := by
    have hnat : (2614376989 : ℕ)^4531*100000000000000^3507 ≤ 43268717007283^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614376989 5000000000 43268717007283 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14857747/78125000 : ℝ)^4531 ≤ (11713523346109/100000000000000 : ℝ)^3507 := by
    have hnat : (14857747 : ℕ)^4531*100000000000000^3507 ≤ 11713523346109^3507*78125000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14857747 78125000 11713523346109 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391612389/10000000000 : ℝ), (2614376989/5000000000 : ℝ), (-14857747/78125000 : ℝ)] ![(45017759635067/100000000000000 : ℝ), (43268717007283/100000000000000 : ℝ), (11713523346109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391612389/10000000000 : ℝ)|^4531 ≤ (45017759635067/100000000000000 : ℝ)^3507
        have hw : |(5391612389/10000000000 : ℝ)|=(5391612389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614376989/5000000000 : ℝ)|^4531 ≤ (43268717007283/100000000000000 : ℝ)^3507
        have hw : |(2614376989/5000000000 : ℝ)|=(2614376989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14857747/78125000 : ℝ)|^4531 ≤ (11713523346109/100000000000000 : ℝ)^3507
        have hw : |(-14857747/78125000 : ℝ)|=(14857747/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_box_15 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (502826229/1250000000 : ℝ)*x 0 + (549527401/1250000000 : ℝ)*x 1 + (219810949/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502826229/1250000000 : ℝ)^4531 ≤ (15416975669607/50000000000000 : ℝ)^3507 := by
    have hnat : (502826229 : ℕ)^4531*50000000000000^3507 ≤ 15416975669607^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502826229 1250000000 15416975669607 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549527401/1250000000 : ℝ)^4531 ≤ (34583025477139/100000000000000 : ℝ)^3507 := by
    have hnat : (549527401 : ℕ)^4531*100000000000000^3507 ≤ 34583025477139^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549527401 1250000000 34583025477139 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219810949/500000000 : ℝ)^4531 ≤ (8645755789967/25000000000000 : ℝ)^3507 := by
    have hnat : (219810949 : ℕ)^4531*25000000000000^3507 ≤ 8645755789967^3507*500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219810949 500000000 8645755789967 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502826229/1250000000 : ℝ), (549527401/1250000000 : ℝ), (219810949/500000000 : ℝ)] ![(15416975669607/50000000000000 : ℝ), (34583025477139/100000000000000 : ℝ), (8645755789967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502826229/1250000000 : ℝ)|^4531 ≤ (15416975669607/50000000000000 : ℝ)^3507
        have hw : |(502826229/1250000000 : ℝ)|=(502826229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549527401/1250000000 : ℝ)|^4531 ≤ (34583025477139/100000000000000 : ℝ)^3507
        have hw : |(549527401/1250000000 : ℝ)|=(549527401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219810949/500000000 : ℝ)|^4531 ≤ (8645755789967/25000000000000 : ℝ)^3507
        have hw : |(219810949/500000000 : ℝ)|=(219810949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1517_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2187/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31873/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58651/100000 : ℝ) ∧ (80373/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43017/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2187/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2187/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2187/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2187/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2187/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2187/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2187/20000 : ℝ) ^ (4529/1024 : ℝ) ≤ (87631086812697/1562500000000000000 : ℝ) := by
    have hpowers : (2187/20000 : ℝ)^4529 ≤ (87631086812697/1562500000000000000 : ℝ)^1024 := by
      have hnat : (2187 : ℕ)^4529*1562500000000000000^1024 ≤ 87631086812697^1024*20000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2187 20000 87631086812697 1562500000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2187/20000 : ℝ)) (X := (87631086812697/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4529/1024 : ℝ) ≤ (26105099942273011/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4529 ≤ (26105099942273011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4529*100000000000000000000^1024 ≤ 26105099942273011^1024*50000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 26105099942273011 100000000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (26105099942273011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781337631086812697/781250000000000000 : ℝ) ≤ (2000050719732007/2000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (781337631086812697/781250000000000000 : ℝ)^1024 ≤ (2000050719732007/2000000000000000 : ℝ)^4529 := by
      have hnat : (781337631086812697 : ℕ)^1024*2000000000000000^4529 ≤ 2000050719732007^4529*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781337631086812697 781250000000000000 2000050719732007 2000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000050719732007/2000000000000000 : ℝ)) (X := (781337631086812697/781250000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031713489498285619/100000000000000000000 : ℝ) ≤ (10000716949190817/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (100031713489498285619/100000000000000000000 : ℝ)^1024 ≤ (10000716949190817/10000000000000000 : ℝ)^4529 := by
      have hnat : (100031713489498285619 : ℕ)^1024*10000000000000000^4529 ≤ 10000716949190817^4529*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031713489498285619 100000000000000000000 10000716949190817 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000716949190817/10000000000000000 : ℝ)) (X := (100031713489498285619/100000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026105099942273011/50000000000000000000 : ℝ) ≤ (10001180299721599/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (50026105099942273011/50000000000000000000 : ℝ)^1024 ≤ (10001180299721599/10000000000000000 : ℝ)^4529 := by
      have hnat : (50026105099942273011 : ℕ)^1024*10000000000000000^4529 ≤ 10001180299721599^4529*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026105099942273011 50000000000000000000 10001180299721599 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001180299721599/10000000000000000 : ℝ)) (X := (50026105099942273011/50000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87631086812697/1562500000000000000 : ℝ) ≤ ((9092203927399795361/9094000000000000000 : ℝ)+2*(231675265391/227350000000000 : ℝ)*(2187/20000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (9092203927399795361/9094000000000000000 : ℝ)+2*(231675265391/227350000000000 : ℝ)*(2187/20000 : ℝ)=(2000050719732007/2000000000000000 : ℝ) by norm_num, show 1+2*(87631086812697/1562500000000000000 : ℝ)=(781337631086812697/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26105099942273011/100000000000000000000 : ℝ)+(87631086812697/1562500000000000000 : ℝ) ≤ ((9092203927399795361/9094000000000000000 : ℝ)+(231675265391/227350000000000 : ℝ)*((7741/50000 : ℝ)+(2187/20000 : ℝ)))^(4529/1024 : ℝ) := by
    rw [show (9092203927399795361/9094000000000000000 : ℝ)+(231675265391/227350000000000 : ℝ)*((7741/50000 : ℝ)+(2187/20000 : ℝ))=(10000716949190817/10000000000000000 : ℝ) by norm_num, show 1+(26105099942273011/100000000000000000000 : ℝ)+(87631086812697/1562500000000000000 : ℝ)=(100031713489498285619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26105099942273011/100000000000000000000 : ℝ) ≤ ((9092203927399795361/9094000000000000000 : ℝ)+2*(231675265391/227350000000000 : ℝ)*(7741/50000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (9092203927399795361/9094000000000000000 : ℝ)+2*(231675265391/227350000000000 : ℝ)*(7741/50000 : ℝ)=(10001180299721599/10000000000000000 : ℝ) by norm_num, show 1+2*(26105099942273011/100000000000000000000 : ℝ)=(50026105099942273011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9092203927399795361/9094000000000000000 : ℝ)*(X 1 0+X 2 0)+(231675265391/227350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (2187/20000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (9092203927399795361/9094000000000000000 : ℝ)) (alpha := (231675265391/227350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9092203927399795361/9094000000000000000 : ℝ)*(X 0 1+X 2 1)+(231675265391/227350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (2187/20000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (9092203927399795361/9094000000000000000 : ℝ)) (alpha := (231675265391/227350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9092203927399795361/9094000000000000000 : ℝ)*(X 0 2+X 1 2)+(231675265391/227350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (2187/20000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (9092203927399795361/9094000000000000000 : ℝ)) (alpha := (231675265391/227350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-823961597/5000000000 : ℝ)*X 0 0+(5402290791/10000000000 : ℝ)*X 0 1+(108045821/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((658854919/1250000000 : ℝ)*X 1 0+(-57197071/312500000 : ℝ)*X 1 1+(5402290507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054167933/2000000000 : ℝ)*X 2 0+(2701145179/5000000000 : ℝ)*X 2 1+(-36606121/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4470285287/10000000000 : ℝ)*X 0 0+(4172981191/10000000000 : ℝ)*X 0 1+(2086490767/5000000000 : ℝ)*X 0 2+(4470285287/10000000000 : ℝ)*X 1 0+(4172981191/10000000000 : ℝ)*X 1 1+(2086490767/5000000000 : ℝ)*X 1 2+(4470285287/10000000000 : ℝ)*X 2 0+(4172981191/10000000000 : ℝ)*X 2 1+(2086490767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1039413627/5000000000 : ℝ)*X 0 0+(2621891917/5000000000 : ℝ)*X 0 1+(2621892159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5381152337/10000000000 : ℝ)*X 1 0+(-1895762691/10000000000 : ℝ)*X 1 1+(5243784091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1345288081/2500000000 : ℝ)*X 2 0+(1310946033/2500000000 : ℝ)*X 2 1+(-379152531/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4062170237/10000000000 : ℝ)*X 0 0+(4376905143/10000000000 : ℝ)*X 0 1+(4376905337/10000000000 : ℝ)*X 0 2+(4062170237/10000000000 : ℝ)*X 1 0+(4376905143/10000000000 : ℝ)*X 1 1+(4376905337/10000000000 : ℝ)*X 1 2+(4062170237/10000000000 : ℝ)*X 2 0+(4376905143/10000000000 : ℝ)*X 2 1+(4376905337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-993870229/5000000000 : ℝ)*X 0 0+(641585381/1250000000 : ℝ)*X 0 1+(2711364323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256609511/10000000000 : ℝ)*X 1 0+(-182162151/1000000000 : ℝ)*X 1 1+(5422728643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((262830469/500000000 : ℝ)*X 2 0+(1084545759/2000000000 : ℝ)*X 2 1+(-45540537/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4521756879/10000000000 : ℝ)*X 0 0+(4146654907/10000000000 : ℝ)*X 0 1+(4146654831/10000000000 : ℝ)*X 0 2+(4521756879/10000000000 : ℝ)*X 1 0+(4146654907/10000000000 : ℝ)*X 1 1+(4146654831/10000000000 : ℝ)*X 1 2+(4521756879/10000000000 : ℝ)*X 2 0+(4146654907/10000000000 : ℝ)*X 2 1+(4146654831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1738933129/10000000000 : ℝ)*X 0 0+(5509837729/10000000000 : ℝ)*X 0 1+(1045750743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5391612489/10000000000 : ℝ)*X 1 0+(-1901791549/10000000000 : ℝ)*X 1 1+(5228753927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391612389/10000000000 : ℝ)*X 2 0+(2614376989/5000000000 : ℝ)*X 2 1+(-14857747/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((502826229/1250000000 : ℝ)*X 0 0+(549527401/1250000000 : ℝ)*X 0 1+(219810949/500000000 : ℝ)*X 0 2+(502826229/1250000000 : ℝ)*X 1 0+(549527401/1250000000 : ℝ)*X 1 1+(219810949/500000000 : ℝ)*X 1 2+(502826229/1250000000 : ℝ)*X 2 0+(549527401/1250000000 : ℝ)*X 2 1+(219810949/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31873/50000 : ℝ) ≤ (-57968244726705784510412802856533/90940000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2335787/100000000000000 : ℝ)*(upper1) + (11254847/100000000000000 : ℝ)*(lower4) + (44266323/100000000000000 : ℝ)*(upper5) + (1115406701514623/50000000000000 : ℝ)*(major0) + (1115406701514623/50000000000000 : ℝ)*(major1) + (2230813403029247/100000000000000 : ℝ)*(major2) + (389156457/10000000000000 : ℝ)*(sp1) + (4544069269/100000000000000 : ℝ)*(sp2) + (477649047/20000000000000 : ℝ)*(sp3) + (390097644489283/12500000000000 : ℝ)*(sp4) + (3120781803257799/100000000000000 : ℝ)*(sp5) + (31207811507531/1000000000000 : ℝ)*(sp6) + (1362086521805743/100000000000000 : ℝ)*(sp7) + (907781621/20000000000000 : ℝ)*(sp12) + (681044455025489/50000000000000 : ℝ)*(f.failure) + (3120785694822369/100000000000000 : ℝ)*(f.sum) + (28244899375731/11367500000000000000000000000 : ℝ)*base66 + (3706757738407896097/454700000000000000000000000000000 : ℝ)*base68 + (3073262171770163167/909400000000000000000000000000000 : ℝ)*base69 + (6877108283952696097/454700000000000000000000000000000 : ℝ)*base72 + (347900092947/5683750000000000000000000000 : ℝ)*base73 + (7003379164653363167/909400000000000000000000000000000 : ℝ)*base75 + (5181470430755916097/454700000000000000000000000000000 : ℝ)*base78 + (2432099969336416097/454700000000000000000000000000000 : ℝ)*base80 + (101509215314087/22735000000000000000000000000 : ℝ)*base81 + (3827271/5000000000000000000000 : ℝ)*base89 + (3827271/5000000000000000000000 : ℝ)*base91 + (46172729/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58651/100000 : ℝ) ≤ (133349245339935259487830114461651/227350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28181791/100000000000000 : ℝ)*(lower1) + (31714821/50000000000000 : ℝ)*(lower2) + (58884119/50000000000000 : ℝ)*(lower3) + (2832491/100000000000000 : ℝ)*(upper4) + (6462913/100000000000000 : ℝ)*(lower5) + (1153698481165297/50000000000000 : ℝ)*(major0) + (1153698481165297/50000000000000 : ℝ)*(major1) + (1153698481165297/50000000000000 : ℝ)*(major2) + (49787397220787/1562500000000 : ℝ)*(sp0) + (3186352599074551/100000000000000 : ℝ)*(sp1) + (3186329078696467/100000000000000 : ℝ)*(sp2) + (140884926063653/10000000000000 : ℝ)*(sp3) + (40823055817/100000000000000 : ℝ)*(sp9) + (643434339/1000000000000 : ℝ)*(sp10) + (140884926063653/10000000000000 : ℝ)*(f.failure) + (49787397220787/1562500000000 : ℝ)*(f.sum) + (64644181595389/11367500000000000000000000000 : ℝ)*base65 + (2911011356134732783/454700000000000000000000000000000 : ℝ)*base68 + (68861309014132783/454700000000000000000000000000000 : ℝ)*base70 + (130744673570432783/454700000000000000000000000000000 : ℝ)*base72 + (20306524109457/5683750000000000000000000000 : ℝ)*base73 + (3936833830867732783/454700000000000000000000000000000 : ℝ)*base76 + (1237748130384367217/454700000000000000000000000000000 : ℝ)*base77 + (297317924154667217/454700000000000000000000000000000 : ℝ)*base79 + (70824145526471/11367500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11561133/1000000000000000000000 : ℝ)*base90 + (11561133/1000000000000000000000 : ℝ)*base92 + (11561133/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80373/100000 : ℝ) ≤ (182733440709634298040522683895549/227350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1771879/50000000000000 : ℝ)*(upper0) + (18233/80000000000 : ℝ)*(upper1) + (15690469/100000000000000 : ℝ)*(upper2) + (1250351434216897/50000000000000 : ℝ)*(major0) + (1250351434216897/50000000000000 : ℝ)*(major1) + (1250351434216897/50000000000000 : ℝ)*(major2) + (7002863359/25000000000000 : ℝ)*(sp1) + (48723357091/100000000000000 : ℝ)*(sp2) + (5151496297/50000000000000 : ℝ)*(sp3) + (198348059/10000000000000 : ℝ)*(sp4) + (1723867037874259/50000000000000 : ℝ)*(sp8) + (430963505971959/12500000000000 : ℝ)*(sp9) + (1723843667936009/50000000000000 : ℝ)*(sp10) + (1526867579218913/100000000000000 : ℝ)*(sp11) + (1526877882211507/100000000000000 : ℝ)*(f.failure) + (861934014807277/25000000000000 : ℝ)*(f.sum) + (34616029437673/22735000000000000000000000000 : ℝ)*base65 + (1074687376303194817/454700000000000000000000000000000 : ℝ)*base67 + (1885348508316594817/454700000000000000000000000000000 : ℝ)*base69 + (15424440223194817/454700000000000000000000000000000 : ℝ)*base71 + (14663240249653/22735000000000000000000000000 : ℝ)*base73 + (2695500730086594817/454700000000000000000000000000000 : ℝ)*base75 + (205611364134505183/454700000000000000000000000000000 : ℝ)*base78 + (4108475192727605183/454700000000000000000000000000000 : ℝ)*base80 + (38875322377793/22735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (31099627/10000000000000000000000 : ℝ)*base90 + (31099627/10000000000000000000000 : ℝ)*base92 + (31099627/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-43017/50000 : ℝ) ≤ (-195592350441261573351857872641057/227350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42203381/50000000000000 : ℝ)*(upper3) + (7028227/100000000000000 : ℝ)*(lower4) + (4379557/50000000000000 : ℝ)*(upper5) + (1269947635578807/50000000000000 : ℝ)*(major0) + (1269947635578807/50000000000000 : ℝ)*(major1) + (1269947635578807/50000000000000 : ℝ)*(major2) + (33095737/1250000000000 : ℝ)*(sp0) + (4568408581/12500000000000 : ℝ)*(sp5) + (2313711533/25000000000000 : ℝ)*(sp6) + (7184386207/25000000000000 : ℝ)*(sp7) + (3557657063016489/100000000000000 : ℝ)*(sp12) + (8894057908517/250000000000 : ℝ)*(sp13) + (889412613957329/25000000000000 : ℝ)*(sp14) + (1550779221936197/100000000000000 : ℝ)*(sp15) + (775403979740513/50000000000000 : ℝ)*(f.failure) + (444707463834431/12500000000000 : ℝ)*(f.sum) + (7706648095817/22735000000000000000000000000 : ℝ)*base66 + (395294792258705673/454700000000000000000000000000000 : ℝ)*base68 + (3763579397055705673/454700000000000000000000000000000 : ℝ)*base70 + (4308286345835205673/454700000000000000000000000000000 : ℝ)*base72 + (20509630401541/2841875000000000000000000000 : ℝ)*base73 + (1516755706190805673/454700000000000000000000000000000 : ℝ)*base76 + (702356708280405673/454700000000000000000000000000000 : ℝ)*base78 + (1054266780674405673/454700000000000000000000000000000 : ℝ)*base80 + (5472776517981/2841875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (40404407/5000000000000000000000 : ℝ)*base89 + (40404407/5000000000000000000000 : ℝ)*base91 + (40404407/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1517_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2187/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31873/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58651/100000 : ℝ) else (80373/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43017/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1517_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1517_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31873/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58651/100000 : ℝ) else (80373/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43017/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1517_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1517_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31873/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58651/100000 : ℝ) else (80373/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43017/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1517_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

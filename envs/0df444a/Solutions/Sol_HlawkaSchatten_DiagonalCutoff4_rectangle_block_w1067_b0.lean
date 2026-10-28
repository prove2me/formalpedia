-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1067_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:07:19.877149+00:00
-- url     : https://prove2.me/submissions/2d01e07f-6b87-4ca4-a9b8-e45b87da83df

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
theorem support_rectangle_w1067_s0_0 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-478944297/2500000000 : ℝ)*x 0 + (6071827093/10000000000 : ℝ)*x 1 + (4770914453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478944297/2500000000 : ℝ)^2065 ≤ (2777699680279/25000000000000 : ℝ)^1553 := by
    have hnat : (478944297 : ℕ)^2065*25000000000000^1553 ≤ 2777699680279^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478944297 2500000000 2777699680279 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6071827093/10000000000 : ℝ)^2065 ≤ (12877251317717/25000000000000 : ℝ)^1553 := by
    have hnat : (6071827093 : ℕ)^2065*25000000000000^1553 ≤ 12877251317717^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6071827093 10000000000 12877251317717 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770914453/10000000000 : ℝ)^2065 ≤ (584065562287/1562500000000 : ℝ)^1553 := by
    have hnat : (4770914453 : ℕ)^2065*1562500000000^1553 ≤ 584065562287^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770914453 10000000000 584065562287 1562500000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478944297/2500000000 : ℝ), (6071827093/10000000000 : ℝ), (4770914453/10000000000 : ℝ)] ![(2777699680279/25000000000000 : ℝ), (12877251317717/25000000000000 : ℝ), (584065562287/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478944297/2500000000 : ℝ)|^2065 ≤ (2777699680279/25000000000000 : ℝ)^1553
        have hw : |(-478944297/2500000000 : ℝ)|=(478944297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6071827093/10000000000 : ℝ)|^2065 ≤ (12877251317717/25000000000000 : ℝ)^1553
        have hw : |(6071827093/10000000000 : ℝ)|=(6071827093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770914453/10000000000 : ℝ)|^2065 ≤ (584065562287/1562500000000 : ℝ)^1553
        have hw : |(4770914453/10000000000 : ℝ)|=(4770914453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_1 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (690126873/1250000000 : ℝ)*x 0 + (-266456053/1000000000 : ℝ)*x 1 + (4770915411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690126873/1250000000 : ℝ)^2065 ≤ (45390667470397/100000000000000 : ℝ)^1553 := by
    have hnat : (690126873 : ℕ)^2065*100000000000000^1553 ≤ 45390667470397^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690126873 1250000000 45390667470397 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266456053/1000000000 : ℝ)^2065 ≤ (17229126548877/100000000000000 : ℝ)^1553 := by
    have hnat : (266456053 : ℕ)^2065*100000000000000^1553 ≤ 17229126548877^1553*1000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266456053 1000000000 17229126548877 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770915411/10000000000 : ℝ)^2065 ≤ (9345051491727/25000000000000 : ℝ)^1553 := by
    have hnat : (4770915411 : ℕ)^2065*25000000000000^1553 ≤ 9345051491727^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770915411 10000000000 9345051491727 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690126873/1250000000 : ℝ), (-266456053/1000000000 : ℝ), (4770915411/10000000000 : ℝ)] ![(45390667470397/100000000000000 : ℝ), (17229126548877/100000000000000 : ℝ), (9345051491727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690126873/1250000000 : ℝ)|^2065 ≤ (45390667470397/100000000000000 : ℝ)^1553
        have hw : |(690126873/1250000000 : ℝ)|=(690126873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266456053/1000000000 : ℝ)|^2065 ≤ (17229126548877/100000000000000 : ℝ)^1553
        have hw : |(-266456053/1000000000 : ℝ)|=(266456053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770915411/10000000000 : ℝ)|^2065 ≤ (9345051491727/25000000000000 : ℝ)^1553
        have hw : |(4770915411/10000000000 : ℝ)|=(4770915411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_2 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5521018137/10000000000 : ℝ)*x 0 + (596364217/1250000000 : ℝ)*x 1 + (-333069819/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521018137/10000000000 : ℝ)^2065 ≤ (5673837742341/12500000000000 : ℝ)^1553 := by
    have hnat : (5521018137 : ℕ)^2065*12500000000000^1553 ≤ 5673837742341^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521018137 10000000000 5673837742341 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596364217/1250000000 : ℝ)^2065 ≤ (3738018851659/10000000000000 : ℝ)^1553 := by
    have hnat : (596364217 : ℕ)^2065*10000000000000^1553 ≤ 3738018851659^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596364217 1250000000 3738018851659 10000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333069819/1250000000 : ℝ)^2065 ≤ (17229109542473/100000000000000 : ℝ)^1553 := by
    have hnat : (333069819 : ℕ)^2065*100000000000000^1553 ≤ 17229109542473^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333069819 1250000000 17229109542473 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521018137/10000000000 : ℝ), (596364217/1250000000 : ℝ), (-333069819/1250000000 : ℝ)] ![(5673837742341/12500000000000 : ℝ), (3738018851659/10000000000000 : ℝ), (17229109542473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521018137/10000000000 : ℝ)|^2065 ≤ (5673837742341/12500000000000 : ℝ)^1553
        have hw : |(5521018137/10000000000 : ℝ)|=(5521018137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596364217/1250000000 : ℝ)|^2065 ≤ (3738018851659/10000000000000 : ℝ)^1553
        have hw : |(596364217/1250000000 : ℝ)|=(596364217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333069819/1250000000 : ℝ)|^2065 ≤ (17229109542473/100000000000000 : ℝ)^1553
        have hw : |(-333069819/1250000000 : ℝ)|=(333069819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_3 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2103564059/5000000000 : ℝ)*x 0 + (624962363/2000000000 : ℝ)*x 1 + (2837463913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103564059/5000000000 : ℝ)^2065 ≤ (3162420891937/10000000000000 : ℝ)^1553 := by
    have hnat : (2103564059 : ℕ)^2065*10000000000000^1553 ≤ 3162420891937^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103564059 5000000000 3162420891937 10000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624962363/2000000000 : ℝ)^2065 ≤ (10647438522053/50000000000000 : ℝ)^1553 := by
    have hnat : (624962363 : ℕ)^2065*50000000000000^1553 ≤ 10647438522053^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624962363 2000000000 10647438522053 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837463913/5000000000 : ℝ)^2065 ≤ (4708091402191/10000000000000 : ℝ)^1553 := by
    have hnat : (2837463913 : ℕ)^2065*10000000000000^1553 ≤ 4708091402191^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837463913 5000000000 4708091402191 10000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103564059/5000000000 : ℝ), (624962363/2000000000 : ℝ), (2837463913/5000000000 : ℝ)] ![(3162420891937/10000000000000 : ℝ), (10647438522053/50000000000000 : ℝ), (4708091402191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103564059/5000000000 : ℝ)|^2065 ≤ (3162420891937/10000000000000 : ℝ)^1553
        have hw : |(2103564059/5000000000 : ℝ)|=(2103564059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624962363/2000000000 : ℝ)|^2065 ≤ (10647438522053/50000000000000 : ℝ)^1553
        have hw : |(624962363/2000000000 : ℝ)|=(624962363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2837463913/5000000000 : ℝ)|^2065 ≤ (4708091402191/10000000000000 : ℝ)^1553
        have hw : |(2837463913/5000000000 : ℝ)|=(2837463913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_4 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1921147123/10000000000 : ℝ)*x 0 + (4804504131/10000000000 : ℝ)*x 1 + (1207412509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1921147123/10000000000 : ℝ)^2065 ≤ (11152229052517/100000000000000 : ℝ)^1553 := by
    have hnat : (1921147123 : ℕ)^2065*100000000000000^1553 ≤ 11152229052517^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921147123 10000000000 11152229052517 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4804504131/10000000000 : ℝ)^2065 ≤ (9432635531089/25000000000000 : ℝ)^1553 := by
    have hnat : (4804504131 : ℕ)^2065*25000000000000^1553 ≤ 9432635531089^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804504131 10000000000 9432635531089 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207412509/2000000000 : ℝ)^2065 ≤ (3194826800411/6250000000000 : ℝ)^1553 := by
    have hnat : (1207412509 : ℕ)^2065*6250000000000^1553 ≤ 3194826800411^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207412509 2000000000 3194826800411 6250000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1921147123/10000000000 : ℝ), (4804504131/10000000000 : ℝ), (1207412509/2000000000 : ℝ)] ![(11152229052517/100000000000000 : ℝ), (9432635531089/25000000000000 : ℝ), (3194826800411/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1921147123/10000000000 : ℝ)|^2065 ≤ (11152229052517/100000000000000 : ℝ)^1553
        have hw : |(-1921147123/10000000000 : ℝ)|=(1921147123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4804504131/10000000000 : ℝ)|^2065 ≤ (9432635531089/25000000000000 : ℝ)^1553
        have hw : |(4804504131/10000000000 : ℝ)|=(4804504131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207412509/2000000000 : ℝ)|^2065 ≤ (3194826800411/6250000000000 : ℝ)^1553
        have hw : |(1207412509/2000000000 : ℝ)|=(1207412509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_5 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1033584551/2000000000 : ℝ)*x 0 + (-1398415061/10000000000 : ℝ)*x 1 + (3018530201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033584551/2000000000 : ℝ)^2065 ≤ (20785992034589/50000000000000 : ℝ)^1553 := by
    have hnat : (1033584551 : ℕ)^2065*50000000000000^1553 ≤ 20785992034589^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033584551 2000000000 20785992034589 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398415061/10000000000 : ℝ)^2065 ≤ (7310811238257/100000000000000 : ℝ)^1553 := by
    have hnat : (1398415061 : ℕ)^2065*100000000000000^1553 ≤ 7310811238257^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398415061 10000000000 7310811238257 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3018530201/5000000000 : ℝ)^2065 ≤ (51117204679073/100000000000000 : ℝ)^1553 := by
    have hnat : (3018530201 : ℕ)^2065*100000000000000^1553 ≤ 51117204679073^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018530201 5000000000 51117204679073 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033584551/2000000000 : ℝ), (-1398415061/10000000000 : ℝ), (3018530201/5000000000 : ℝ)] ![(20785992034589/50000000000000 : ℝ), (7310811238257/100000000000000 : ℝ), (51117204679073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033584551/2000000000 : ℝ)|^2065 ≤ (20785992034589/50000000000000 : ℝ)^1553
        have hw : |(1033584551/2000000000 : ℝ)|=(1033584551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1398415061/10000000000 : ℝ)|^2065 ≤ (7310811238257/100000000000000 : ℝ)^1553
        have hw : |(-1398415061/10000000000 : ℝ)|=(1398415061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3018530201/5000000000 : ℝ)|^2065 ≤ (51117204679073/100000000000000 : ℝ)^1553
        have hw : |(3018530201/5000000000 : ℝ)|=(3018530201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_6 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5167922887/10000000000 : ℝ)*x 0 + (6037061629/10000000000 : ℝ)*x 1 + (-1398412869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167922887/10000000000 : ℝ)^2065 ≤ (41571985481089/100000000000000 : ℝ)^1553 := by
    have hnat : (5167922887 : ℕ)^2065*100000000000000^1553 ≤ 41571985481089^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167922887 10000000000 41571985481089 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6037061629/10000000000 : ℝ)^2065 ≤ (1277930462339/2500000000000 : ℝ)^1553 := by
    have hnat : (6037061629 : ℕ)^2065*2500000000000^1553 ≤ 1277930462339^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6037061629 10000000000 1277930462339 2500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398412869/10000000000 : ℝ)^2065 ≤ (1827699000147/25000000000000 : ℝ)^1553 := by
    have hnat : (1398412869 : ℕ)^2065*25000000000000^1553 ≤ 1827699000147^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398412869 10000000000 1827699000147 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167922887/10000000000 : ℝ), (6037061629/10000000000 : ℝ), (-1398412869/10000000000 : ℝ)] ![(41571985481089/100000000000000 : ℝ), (1277930462339/2500000000000 : ℝ), (1827699000147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167922887/10000000000 : ℝ)|^2065 ≤ (41571985481089/100000000000000 : ℝ)^1553
        have hw : |(5167922887/10000000000 : ℝ)|=(5167922887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6037061629/10000000000 : ℝ)|^2065 ≤ (1277930462339/2500000000000 : ℝ)^1553
        have hw : |(6037061629/10000000000 : ℝ)|=(6037061629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1398412869/10000000000 : ℝ)|^2065 ≤ (1827699000147/25000000000000 : ℝ)^1553
        have hw : |(-1398412869/10000000000 : ℝ)|=(1398412869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s0_7 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4217652701/10000000000 : ℝ)*x 0 + (5609080629/10000000000 : ℝ)*x 1 + (19956019/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217652701/10000000000 : ℝ)^2065 ≤ (495772584633/1562500000000 : ℝ)^1553 := by
    have hnat : (4217652701 : ℕ)^2065*1562500000000^1553 ≤ 495772584633^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217652701 10000000000 495772584633 1562500000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5609080629/10000000000 : ℝ)^2065 ≤ (23177958018229/50000000000000 : ℝ)^1553 := by
    have hnat : (5609080629 : ℕ)^2065*50000000000000^1553 ≤ 23177958018229^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609080629 10000000000 23177958018229 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19956019/62500000 : ℝ)^2065 ≤ (21914638525247/100000000000000 : ℝ)^1553 := by
    have hnat : (19956019 : ℕ)^2065*100000000000000^1553 ≤ 21914638525247^1553*62500000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19956019 62500000 21914638525247 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217652701/10000000000 : ℝ), (5609080629/10000000000 : ℝ), (19956019/62500000 : ℝ)] ![(495772584633/1562500000000 : ℝ), (23177958018229/50000000000000 : ℝ), (21914638525247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217652701/10000000000 : ℝ)|^2065 ≤ (495772584633/1562500000000 : ℝ)^1553
        have hw : |(4217652701/10000000000 : ℝ)|=(4217652701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5609080629/10000000000 : ℝ)|^2065 ≤ (23177958018229/50000000000000 : ℝ)^1553
        have hw : |(5609080629/10000000000 : ℝ)|=(5609080629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19956019/62500000 : ℝ)|^2065 ≤ (21914638525247/100000000000000 : ℝ)^1553
        have hw : |(19956019/62500000 : ℝ)|=(19956019/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1067_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5621/20000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8259/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8259 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8259*1^2048 ≤ 0^2048*1^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8259/2048 : ℝ) ≤ (1242199712636471519/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8259 ≤ (1242199712636471519/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8259*50000000000000000000^2048 ≤ 1242199712636471519^2048*5^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1242199712636471519 50000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1242199712636471519/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8259 := by
      have hnat : (1 : ℕ)^2048*1^8259 ≤ 1^8259*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51242199712636471519/50000000000000000000 : ℝ) ≤ (5030519415751257/5000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (51242199712636471519/50000000000000000000 : ℝ)^2048 ≤ (5030519415751257/5000000000000000 : ℝ)^8259 := by
      have hnat : (51242199712636471519 : ℕ)^2048*5000000000000000^8259 ≤ 5030519415751257^8259*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51242199712636471519 50000000000000000000 5030519415751257 5000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030519415751257/5000000000000000 : ℝ)) (X := (51242199712636471519/50000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26242199712636471519/25000000000000000000 : ℝ) ≤ (2530519415751257/2500000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (26242199712636471519/25000000000000000000 : ℝ)^2048 ≤ (2530519415751257/2500000000000000 : ℝ)^8259 := by
      have hnat : (26242199712636471519 : ℕ)^2048*2500000000000000^8259 ≤ 2530519415751257^8259*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26242199712636471519 25000000000000000000 2530519415751257 2500000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530519415751257/2500000000000000 : ℝ)) (X := (26242199712636471519/25000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30519415751257/2000000000000000 : ℝ)*(0 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30519415751257/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1242199712636471519/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30519415751257/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8259/2048 : ℝ) := by
    rw [show (1 : ℝ)+(30519415751257/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030519415751257/5000000000000000 : ℝ) by norm_num, show 1+(1242199712636471519/50000000000000000000 : ℝ)+(0 : ℝ)=(51242199712636471519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1242199712636471519/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30519415751257/2000000000000000 : ℝ)*(2/5 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30519415751257/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530519415751257/2500000000000000 : ℝ) by norm_num, show 1+2*(1242199712636471519/50000000000000000000 : ℝ)=(26242199712636471519/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30519415751257/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30519415751257/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30519415751257/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30519415751257/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30519415751257/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30519415751257/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-478944297/2500000000 : ℝ)*X 0 0+(6071827093/10000000000 : ℝ)*X 0 1+(4770914453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((690126873/1250000000 : ℝ)*X 1 0+(-266456053/1000000000 : ℝ)*X 1 1+(4770915411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521018137/10000000000 : ℝ)*X 2 0+(596364217/1250000000 : ℝ)*X 2 1+(-333069819/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2103564059/5000000000 : ℝ)*X 0 0+(624962363/2000000000 : ℝ)*X 0 1+(2837463913/5000000000 : ℝ)*X 0 2+(2103564059/5000000000 : ℝ)*X 1 0+(624962363/2000000000 : ℝ)*X 1 1+(2837463913/5000000000 : ℝ)*X 1 2+(2103564059/5000000000 : ℝ)*X 2 0+(624962363/2000000000 : ℝ)*X 2 1+(2837463913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1921147123/10000000000 : ℝ)*X 0 0+(4804504131/10000000000 : ℝ)*X 0 1+(1207412509/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1033584551/2000000000 : ℝ)*X 1 0+(-1398415061/10000000000 : ℝ)*X 1 1+(3018530201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5167922887/10000000000 : ℝ)*X 2 0+(6037061629/10000000000 : ℝ)*X 2 1+(-1398412869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4217652701/10000000000 : ℝ)*X 0 0+(5609080629/10000000000 : ℝ)*X 0 1+(19956019/62500000 : ℝ)*X 0 2+(4217652701/10000000000 : ℝ)*X 1 0+(5609080629/10000000000 : ℝ)*X 1 1+(19956019/62500000 : ℝ)*X 1 2+(4217652701/10000000000 : ℝ)*X 2 0+(5609080629/10000000000 : ℝ)*X 2 1+(19956019/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43345004723808831520467/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2786461/4000000000000 : ℝ)*(base1) + (538140417/100000000000000 : ℝ)*(base19) + (180967563/25000000000000 : ℝ)*(base23) + (253263031/100000000000000 : ℝ)*(base24) + (227848837/100000000000000 : ℝ)*(upper3) + (116083354913177/20000000000000 : ℝ)*(major0) + (116083354913177/20000000000000 : ℝ)*(major1) + (116083354913177/20000000000000 : ℝ)*(major2) + (384346203468511/50000000000000 : ℝ)*(sp0) + (192173135297651/25000000000000 : ℝ)*(sp1) + (96086512774717/12500000000000 : ℝ)*(sp2) + (9803479177537/2500000000000 : ℝ)*(sp3) + (371027761/50000000000000 : ℝ)*(sp4) + (36274877/3125000000000 : ℝ)*(sp7) + (392140397559069/100000000000000 : ℝ)*(f.failure) + (38434653966551/5000000000000 : ℝ)*(f.sum) + (45413859626511/20000000000000000000000000000 : ℝ)*base66 + (170212308253489/40000000000000000000000000000 : ℝ)*base67 + (137015083773489/40000000000000000000000000000 : ℝ)*base69 + (172854289986511/40000000000000000000000000000 : ℝ)*base72 + (7102056893489/20000000000000000000000000000 : ℝ)*base73 + (303576747746511/40000000000000000000000000000 : ℝ)*base76 + (18147389826511/40000000000000000000000000000 : ℝ)*base78 + (79580177533489/40000000000000000000000000000 : ℝ)*base79 + (159074911746511/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (4972487/2500000000000000000000 : ℝ)*base89 + (4972487/2500000000000000000000 : ℝ)*base91 + (4972487/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187787471790600003359349/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (686551763/100000000000000 : ℝ)*(base19) + (172725209/20000000000000 : ℝ)*(base23) + (4281837/4000000000000 : ℝ)*(base39) + (6011751/12500000000000 : ℝ)*(base45) + (12529071/25000000000000 : ℝ)*(upper3) + (248194097/100000000000000 : ℝ)*(upper5) + (306301853238719/50000000000000 : ℝ)*(major0) + (306301853238719/50000000000000 : ℝ)*(major1) + (612603599431513/100000000000000 : ℝ)*(major2) + (767899883/100000000000000 : ℝ)*(sp2) + (405660345839317/50000000000000 : ℝ)*(sp4) + (811320005126871/100000000000000 : ℝ)*(sp5) + (811319167198631/100000000000000 : ℝ)*(sp6) + (413886489038667/100000000000000 : ℝ)*(sp7) + (413886489038667/100000000000000 : ℝ)*(f.failure) + (811320798724559/100000000000000 : ℝ)*(f.sum) + (189534988801407/200000000000000000000000000000 : ℝ)*base65 + (404200704238159/200000000000000000000000000000 : ℝ)*base68 + (434584824319783/100000000000000000000000000000 : ℝ)*base69 + (37855180761841/200000000000000000000000000000 : ℝ)*base71 + (63096576598593/200000000000000000000000000000 : ℝ)*base74 + (105625036880217/100000000000000000000000000000 : ℝ)*base76 + (267674421819783/100000000000000000000000000000 : ℝ)*base77 + (250472487680217/100000000000000000000000000000 : ℝ)*base80 + (42653850930217/50000000000000000000000000000 : ℝ)*base82 + (3242959/2500000000000000000000 : ℝ)*base90 + (3242959/2500000000000000000000 : ℝ)*base92 + (3242959/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1067_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5621/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1067_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1067_s1_0 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062919987/5000000000 : ℝ)*x 0 + (5722031269/10000000000 : ℝ)*x 1 + (4986185497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062919987/5000000000 : ℝ)^2065 ≤ (12759328929671/100000000000000 : ℝ)^1553 := by
    have hnat : (1062919987 : ℕ)^2065*100000000000000^1553 ≤ 12759328929671^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062919987 5000000000 12759328929671 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5722031269/10000000000 : ℝ)^2065 ≤ (47601243595567/100000000000000 : ℝ)^1553 := by
    have hnat : (5722031269 : ℕ)^2065*100000000000000^1553 ≤ 47601243595567^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5722031269 10000000000 47601243595567 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986185497/10000000000 : ℝ)^2065 ≤ (39639427462403/100000000000000 : ℝ)^1553 := by
    have hnat : (4986185497 : ℕ)^2065*100000000000000^1553 ≤ 39639427462403^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986185497 10000000000 39639427462403 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062919987/5000000000 : ℝ), (5722031269/10000000000 : ℝ), (4986185497/10000000000 : ℝ)] ![(12759328929671/100000000000000 : ℝ), (47601243595567/100000000000000 : ℝ), (39639427462403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062919987/5000000000 : ℝ)|^2065 ≤ (12759328929671/100000000000000 : ℝ)^1553
        have hw : |(-1062919987/5000000000 : ℝ)|=(1062919987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5722031269/10000000000 : ℝ)|^2065 ≤ (47601243595567/100000000000000 : ℝ)^1553
        have hw : |(5722031269/10000000000 : ℝ)|=(5722031269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986185497/10000000000 : ℝ)|^2065 ≤ (39639427462403/100000000000000 : ℝ)^1553
        have hw : |(4986185497/10000000000 : ℝ)|=(4986185497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_1 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2711627623/5000000000 : ℝ)*x 0 + (-1262249669/5000000000 : ℝ)*x 1 + (4986185813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711627623/5000000000 : ℝ)^2065 ≤ (22162549063529/50000000000000 : ℝ)^1553 := by
    have hnat : (2711627623 : ℕ)^2065*50000000000000^1553 ≤ 22162549063529^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711627623 5000000000 22162549063529 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262249669/5000000000 : ℝ)^2065 ≤ (16035471047449/100000000000000 : ℝ)^1553 := by
    have hnat : (1262249669 : ℕ)^2065*100000000000000^1553 ≤ 16035471047449^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262249669 5000000000 16035471047449 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986185813/10000000000 : ℝ)^2065 ≤ (39639430802773/100000000000000 : ℝ)^1553 := by
    have hnat : (4986185813 : ℕ)^2065*100000000000000^1553 ≤ 39639430802773^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986185813 10000000000 39639430802773 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711627623/5000000000 : ℝ), (-1262249669/5000000000 : ℝ), (4986185813/10000000000 : ℝ)] ![(22162549063529/50000000000000 : ℝ), (16035471047449/100000000000000 : ℝ), (39639430802773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711627623/5000000000 : ℝ)|^2065 ≤ (22162549063529/50000000000000 : ℝ)^1553
        have hw : |(2711627623/5000000000 : ℝ)|=(2711627623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1262249669/5000000000 : ℝ)|^2065 ≤ (16035471047449/100000000000000 : ℝ)^1553
        have hw : |(-1262249669/5000000000 : ℝ)|=(1262249669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986185813/10000000000 : ℝ)|^2065 ≤ (39639430802773/100000000000000 : ℝ)^1553
        have hw : |(4986185813/10000000000 : ℝ)|=(4986185813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_2 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (677906979/1250000000 : ℝ)*x 0 + (4986185151/10000000000 : ℝ)*x 1 + (-2524499413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677906979/1250000000 : ℝ)^2065 ≤ (44325104495539/100000000000000 : ℝ)^1553 := by
    have hnat : (677906979 : ℕ)^2065*100000000000000^1553 ≤ 44325104495539^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677906979 1250000000 44325104495539 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986185151/10000000000 : ℝ)^2065 ≤ (39639423804909/100000000000000 : ℝ)^1553 := by
    have hnat : (4986185151 : ℕ)^2065*100000000000000^1553 ≤ 39639423804909^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986185151 10000000000 39639423804909 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2524499413/10000000000 : ℝ)^2065 ≤ (2004433960113/12500000000000 : ℝ)^1553 := by
    have hnat : (2524499413 : ℕ)^2065*12500000000000^1553 ≤ 2004433960113^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524499413 10000000000 2004433960113 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677906979/1250000000 : ℝ), (4986185151/10000000000 : ℝ), (-2524499413/10000000000 : ℝ)] ![(44325104495539/100000000000000 : ℝ), (39639423804909/100000000000000 : ℝ), (2004433960113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677906979/1250000000 : ℝ)|^2065 ≤ (44325104495539/100000000000000 : ℝ)^1553
        have hw : |(677906979/1250000000 : ℝ)|=(677906979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986185151/10000000000 : ℝ)|^2065 ≤ (39639423804909/100000000000000 : ℝ)^1553
        have hw : |(4986185151/10000000000 : ℝ)|=(4986185151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2524499413/10000000000 : ℝ)|^2065 ≤ (2004433960113/12500000000000 : ℝ)^1553
        have hw : |(-2524499413/10000000000 : ℝ)|=(2524499413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_3 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67558159/156250000 : ℝ)*x 0 + (915688241/2500000000 : ℝ)*x 1 + (5105193127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67558159/156250000 : ℝ)^2065 ≤ (32794856982871/100000000000000 : ℝ)^1553 := by
    have hnat : (67558159 : ℕ)^2065*100000000000000^1553 ≤ 32794856982871^1553*156250000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67558159 156250000 32794856982871 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915688241/2500000000 : ℝ)^2065 ≤ (1643924204551/6250000000000 : ℝ)^1553 := by
    have hnat : (915688241 : ℕ)^2065*6250000000000^1553 ≤ 1643924204551^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915688241 2500000000 1643924204551 6250000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5105193127/10000000000 : ℝ)^2065 ≤ (8180471145301/20000000000000 : ℝ)^1553 := by
    have hnat : (5105193127 : ℕ)^2065*20000000000000^1553 ≤ 8180471145301^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105193127 10000000000 8180471145301 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67558159/156250000 : ℝ), (915688241/2500000000 : ℝ), (5105193127/10000000000 : ℝ)] ![(32794856982871/100000000000000 : ℝ), (1643924204551/6250000000000 : ℝ), (8180471145301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67558159/156250000 : ℝ)|^2065 ≤ (32794856982871/100000000000000 : ℝ)^1553
        have hw : |(67558159/156250000 : ℝ)|=(67558159/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915688241/2500000000 : ℝ)|^2065 ≤ (1643924204551/6250000000000 : ℝ)^1553
        have hw : |(915688241/2500000000 : ℝ)|=(915688241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5105193127/10000000000 : ℝ)|^2065 ≤ (8180471145301/20000000000000 : ℝ)^1553
        have hw : |(5105193127/10000000000 : ℝ)|=(5105193127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_4 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063380239/5000000000 : ℝ)*x 0 + (99930451/200000000 : ℝ)*x 1 + (1427870521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063380239/5000000000 : ℝ)^2065 ≤ (3191668950697/25000000000000 : ℝ)^1553 := by
    have hnat : (1063380239 : ℕ)^2065*25000000000000^1553 ≤ 3191668950697^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063380239 5000000000 3191668950697 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99930451/200000000 : ℝ)^2065 ≤ (39748735628303/100000000000000 : ℝ)^1553 := by
    have hnat : (99930451 : ℕ)^2065*100000000000000^1553 ≤ 39748735628303^1553*200000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99930451 200000000 39748735628303 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1427870521/2500000000 : ℝ)^2065 ≤ (1483893392231/3125000000000 : ℝ)^1553 := by
    have hnat : (1427870521 : ℕ)^2065*3125000000000^1553 ≤ 1483893392231^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427870521 2500000000 1483893392231 3125000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063380239/5000000000 : ℝ), (99930451/200000000 : ℝ), (1427870521/2500000000 : ℝ)] ![(3191668950697/25000000000000 : ℝ), (39748735628303/100000000000000 : ℝ), (1483893392231/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063380239/5000000000 : ℝ)|^2065 ≤ (3191668950697/25000000000000 : ℝ)^1553
        have hw : |(-1063380239/5000000000 : ℝ)|=(1063380239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(99930451/200000000 : ℝ)|^2065 ≤ (39748735628303/100000000000000 : ℝ)^1553
        have hw : |(99930451/200000000 : ℝ)|=(99930451/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1427870521/2500000000 : ℝ)|^2065 ≤ (1483893392231/3125000000000 : ℝ)^1553
        have hw : |(1427870521/2500000000 : ℝ)|=(1427870521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_5 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2617660891/5000000000 : ℝ)*x 0 + (-1799200829/10000000000 : ℝ)*x 1 + (5711483831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617660891/5000000000 : ℝ)^2065 ≤ (42294449259703/100000000000000 : ℝ)^1553 := by
    have hnat : (2617660891 : ℕ)^2065*100000000000000^1553 ≤ 42294449259703^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617660891 5000000000 42294449259703 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799200829/10000000000 : ℝ)^2065 ≤ (20441885731/200000000000 : ℝ)^1553 := by
    have hnat : (1799200829 : ℕ)^2065*200000000000^1553 ≤ 20441885731^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799200829 10000000000 20441885731 200000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5711483831/10000000000 : ℝ)^2065 ≤ (47484607864199/100000000000000 : ℝ)^1553 := by
    have hnat : (5711483831 : ℕ)^2065*100000000000000^1553 ≤ 47484607864199^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711483831 10000000000 47484607864199 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617660891/5000000000 : ℝ), (-1799200829/10000000000 : ℝ), (5711483831/10000000000 : ℝ)] ![(42294449259703/100000000000000 : ℝ), (20441885731/200000000000 : ℝ), (47484607864199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617660891/5000000000 : ℝ)|^2065 ≤ (42294449259703/100000000000000 : ℝ)^1553
        have hw : |(2617660891/5000000000 : ℝ)|=(2617660891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799200829/10000000000 : ℝ)|^2065 ≤ (20441885731/200000000000 : ℝ)^1553
        have hw : |(-1799200829/10000000000 : ℝ)|=(1799200829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5711483831/10000000000 : ℝ)|^2065 ≤ (47484607864199/100000000000000 : ℝ)^1553
        have hw : |(5711483831/10000000000 : ℝ)|=(5711483831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_6 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5235319743/10000000000 : ℝ)*x 0 + (1427871521/2500000000 : ℝ)*x 1 + (-1799200431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235319743/10000000000 : ℝ)^2065 ≤ (42294427356593/100000000000000 : ℝ)^1553 := by
    have hnat : (5235319743 : ℕ)^2065*100000000000000^1553 ≤ 42294427356593^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235319743 10000000000 42294427356593 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1427871521/2500000000 : ℝ)^2065 ≤ (23742316385379/50000000000000 : ℝ)^1553 := by
    have hnat : (1427871521 : ℕ)^2065*50000000000000^1553 ≤ 23742316385379^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427871521 2500000000 23742316385379 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799200431/10000000000 : ℝ)^2065 ≤ (5110469929563/50000000000000 : ℝ)^1553 := by
    have hnat : (1799200431 : ℕ)^2065*50000000000000^1553 ≤ 5110469929563^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799200431 10000000000 5110469929563 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235319743/10000000000 : ℝ), (1427871521/2500000000 : ℝ), (-1799200431/10000000000 : ℝ)] ![(42294427356593/100000000000000 : ℝ), (23742316385379/50000000000000 : ℝ), (5110469929563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235319743/10000000000 : ℝ)|^2065 ≤ (42294427356593/100000000000000 : ℝ)^1553
        have hw : |(5235319743/10000000000 : ℝ)|=(5235319743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1427871521/2500000000 : ℝ)|^2065 ≤ (23742316385379/50000000000000 : ℝ)^1553
        have hw : |(1427871521/2500000000 : ℝ)|=(1427871521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1799200431/10000000000 : ℝ)|^2065 ≤ (5110469929563/50000000000000 : ℝ)^1553
        have hw : |(-1799200431/10000000000 : ℝ)|=(1799200431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s1_7 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162761271/5000000000 : ℝ)*x 0 + (63561581/125000000 : ℝ)*x 1 + (920857111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162761271/5000000000 : ℝ)^2065 ≤ (32813015783891/100000000000000 : ℝ)^1553 := by
    have hnat : (2162761271 : ℕ)^2065*100000000000000^1553 ≤ 32813015783891^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162761271 5000000000 32813015783891 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63561581/125000000 : ℝ)^2065 ≤ (508582377209/1250000000000 : ℝ)^1553 := by
    have hnat : (63561581 : ℕ)^2065*1250000000000^1553 ≤ 508582377209^1553*125000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63561581 125000000 508582377209 1250000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920857111/2500000000 : ℝ)^2065 ≤ (13250197007989/50000000000000 : ℝ)^1553 := by
    have hnat : (920857111 : ℕ)^2065*50000000000000^1553 ≤ 13250197007989^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920857111 2500000000 13250197007989 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162761271/5000000000 : ℝ), (63561581/125000000 : ℝ), (920857111/2500000000 : ℝ)] ![(32813015783891/100000000000000 : ℝ), (508582377209/1250000000000 : ℝ), (13250197007989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162761271/5000000000 : ℝ)|^2065 ≤ (32813015783891/100000000000000 : ℝ)^1553
        have hw : |(2162761271/5000000000 : ℝ)|=(2162761271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63561581/125000000 : ℝ)|^2065 ≤ (508582377209/1250000000000 : ℝ)^1553
        have hw : |(63561581/125000000 : ℝ)|=(63561581/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920857111/2500000000 : ℝ)|^2065 ≤ (13250197007989/50000000000000 : ℝ)^1553
        have hw : |(920857111/2500000000 : ℝ)|=(920857111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1067_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5621/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10393/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5621/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5621/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5621/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5621/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5621/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5621/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (101/100000 : ℝ) ^ (8259/2048 : ℝ) ≤ (20759761/25000000000000000000 : ℝ) := by
    have hpowers : (101/100000 : ℝ)^8259 ≤ (20759761/25000000000000000000 : ℝ)^2048 := by
      have hnat : (101 : ℕ)^8259*25000000000000000000^2048 ≤ 20759761^2048*100000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101 100000 20759761 25000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (101/100000 : ℝ)) (X := (20759761/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5621/20000 : ℝ) ^ (8259/2048 : ℝ) ≤ (149637832369883361/25000000000000000000 : ℝ) := by
    have hpowers : (5621/20000 : ℝ)^8259 ≤ (149637832369883361/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5621 : ℕ)^8259*25000000000000000000^2048 ≤ 149637832369883361^2048*20000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5621 20000 149637832369883361 25000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5621/20000 : ℝ)) (X := (149637832369883361/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000000020759761/12500000000000000000 : ℝ) ≤ (10000000000004119/10000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (12500000000020759761/12500000000000000000 : ℝ)^2048 ≤ (10000000000004119/10000000000000000 : ℝ)^8259 := by
      have hnat : (12500000000020759761 : ℕ)^2048*10000000000000000^8259 ≤ 10000000000004119^8259*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000000020759761 12500000000000000000 10000000000004119 10000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000004119/10000000000000000 : ℝ)) (X := (12500000000020759761/12500000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12574818916195321561/12500000000000000000 : ℝ) ≤ (2002961820612569/2000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (12574818916195321561/12500000000000000000 : ℝ)^2048 ≤ (2002961820612569/2000000000000000 : ℝ)^8259 := by
      have hnat : (12574818916195321561 : ℕ)^2048*2000000000000000^8259 ≤ 2002961820612569^8259*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12574818916195321561 12500000000000000000 2002961820612569 2000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002961820612569/2000000000000000 : ℝ)) (X := (12574818916195321561/12500000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12649637832369883361/12500000000000000000 : ℝ) ≤ (10029618206121571/10000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (12649637832369883361/12500000000000000000 : ℝ)^2048 ≤ (10029618206121571/10000000000000000 : ℝ)^8259 := by
      have hnat : (12649637832369883361 : ℕ)^2048*10000000000000000^8259 ≤ 10029618206121571^8259*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12649637832369883361 12500000000000000000 10029618206121571 10000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029618206121571/10000000000000000 : ℝ)) (X := (12649637832369883361/12500000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20759761/25000000000000000000 : ℝ) ≤ ((68368410293285519/68369140625000000 : ℝ)+2*(7404551529363/1400200000000000 : ℝ)*(101/100000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (68368410293285519/68369140625000000 : ℝ)+2*(7404551529363/1400200000000000 : ℝ)*(101/100000 : ℝ)=(10000000000004119/10000000000000000 : ℝ) by norm_num, show 1+2*(20759761/25000000000000000000 : ℝ)=(12500000000020759761/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(149637832369883361/25000000000000000000 : ℝ)+(20759761/25000000000000000000 : ℝ) ≤ ((68368410293285519/68369140625000000 : ℝ)+(7404551529363/1400200000000000 : ℝ)*((5621/20000 : ℝ)+(101/100000 : ℝ)))^(8259/2048 : ℝ) := by
    rw [show (68368410293285519/68369140625000000 : ℝ)+(7404551529363/1400200000000000 : ℝ)*((5621/20000 : ℝ)+(101/100000 : ℝ))=(2002961820612569/2000000000000000 : ℝ) by norm_num, show 1+(149637832369883361/25000000000000000000 : ℝ)+(20759761/25000000000000000000 : ℝ)=(12574818916195321561/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(149637832369883361/25000000000000000000 : ℝ) ≤ ((68368410293285519/68369140625000000 : ℝ)+2*(7404551529363/1400200000000000 : ℝ)*(5621/20000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (68368410293285519/68369140625000000 : ℝ)+2*(7404551529363/1400200000000000 : ℝ)*(5621/20000 : ℝ)=(10029618206121571/10000000000000000 : ℝ) by norm_num, show 1+2*(149637832369883361/25000000000000000000 : ℝ)=(12649637832369883361/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68368410293285519/68369140625000000 : ℝ)*(X 1 0+X 2 0)+(7404551529363/1400200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (101/100000 : ℝ)) (hi := (5621/20000 : ℝ)) (c := (68368410293285519/68369140625000000 : ℝ)) (alpha := (7404551529363/1400200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68368410293285519/68369140625000000 : ℝ)*(X 0 1+X 2 1)+(7404551529363/1400200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (101/100000 : ℝ)) (hi := (5621/20000 : ℝ)) (c := (68368410293285519/68369140625000000 : ℝ)) (alpha := (7404551529363/1400200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68368410293285519/68369140625000000 : ℝ)*(X 0 2+X 1 2)+(7404551529363/1400200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (101/100000 : ℝ)) (hi := (5621/20000 : ℝ)) (c := (68368410293285519/68369140625000000 : ℝ)) (alpha := (7404551529363/1400200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1062919987/5000000000 : ℝ)*X 0 0+(5722031269/10000000000 : ℝ)*X 0 1+(4986185497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711627623/5000000000 : ℝ)*X 1 0+(-1262249669/5000000000 : ℝ)*X 1 1+(4986185813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677906979/1250000000 : ℝ)*X 2 0+(4986185151/10000000000 : ℝ)*X 2 1+(-2524499413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67558159/156250000 : ℝ)*X 0 0+(915688241/2500000000 : ℝ)*X 0 1+(5105193127/10000000000 : ℝ)*X 0 2+(67558159/156250000 : ℝ)*X 1 0+(915688241/2500000000 : ℝ)*X 1 1+(5105193127/10000000000 : ℝ)*X 1 2+(67558159/156250000 : ℝ)*X 2 0+(915688241/2500000000 : ℝ)*X 2 1+(5105193127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063380239/5000000000 : ℝ)*X 0 0+(99930451/200000000 : ℝ)*X 0 1+(1427870521/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617660891/5000000000 : ℝ)*X 1 0+(-1799200829/10000000000 : ℝ)*X 1 1+(5711483831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5235319743/10000000000 : ℝ)*X 2 0+(1427871521/2500000000 : ℝ)*X 2 1+(-1799200431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162761271/5000000000 : ℝ)*X 0 0+(63561581/125000000 : ℝ)*X 0 1+(920857111/2500000000 : ℝ)*X 0 2+(2162761271/5000000000 : ℝ)*X 1 0+(63561581/125000000 : ℝ)*X 1 1+(920857111/2500000000 : ℝ)*X 1 2+(2162761271/5000000000 : ℝ)*X 2 0+(63561581/125000000 : ℝ)*X 2 1+(920857111/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (740968136680715807138154267/109390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126043747/100000000000000 : ℝ)*(base1) + (146590397/10000000000000 : ℝ)*(base19) + (1612747561/100000000000000 : ℝ)*(base23) + (149278287/100000000000000 : ℝ)*(upper3) + (163935037/100000000000000 : ℝ)*(upper5) + (128267009695151/12500000000000 : ℝ)*(major0) + (128267009695151/12500000000000 : ℝ)*(major1) + (128267009695151/12500000000000 : ℝ)*(major2) + (679493791627923/50000000000000 : ℝ)*(sp0) + (1358993792188973/100000000000000 : ℝ)*(sp1) + (679496822672691/50000000000000 : ℝ)*(sp2) + (34663650479117/5000000000000 : ℝ)*(sp3) + (1950220211/25000000000000 : ℝ)*(sp4) + (141424671/4000000000000 : ℝ)*(sp7) + (346638335621431/50000000000000 : ℝ)*(f.failure) + (1358995258092943/100000000000000 : ℝ)*(f.sum) + (27845055863509/17502500000000000000000000000 : ℝ)*base66 + (124108706206872183/27347656250000000000000000000000 : ℝ)*base67 + (141922487070877817/27347656250000000000000000000000 : ℝ)*base70 + (16523818072228741/54695312500000000000000000000000 : ℝ)*base71 + (47975504037911/17502500000000000000000000000 : ℝ)*base73 + (359538807856808143/109390625000000000000000000000000 : ℝ)*base76 + (4362353236543673/6836914062500000000000000000000 : ℝ)*base78 + (12423459587790471/13673828125000000000000000000000 : ℝ)*base80 + (122297683218659/17502500000000000000000000000 : ℝ)*base82 + (7270987/1250000000000000000000 : ℝ)*base90 + (7270987/1250000000000000000000 : ℝ)*base92 + (7270987/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7453400852397428720378733/4375625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (449213821/20000000000000 : ℝ)*(base19) + (2213256493/100000000000000 : ℝ)*(base23) + (121339943/50000000000000 : ℝ)*(upper2) + (382049081/100000000000000 : ℝ)*(upper3) + (50319987/10000000000000 : ℝ)*(upper5) + (42244009724111/4000000000000 : ℝ)*(major0) + (42244009724111/4000000000000 : ℝ)*(major1) + (42244009724111/4000000000000 : ℝ)*(major2) + (2845487507/25000000000000 : ℝ)*(sp1) + (3182423169/25000000000000 : ℝ)*(sp2) + (1398679409117111/100000000000000 : ℝ)*(sp4) + (699332890548989/50000000000000 : ℝ)*(sp5) + (699332233083971/50000000000000 : ℝ)*(sp6) + (89190127538591/12500000000000 : ℝ)*(sp7) + (89190127538591/12500000000000 : ℝ)*(f.failure) + (1398679409117111/100000000000000 : ℝ)*(f.sum) + (57857192589429/14002000000000000000000000000 : ℝ)*base65 + (83180582661776601/17502500000000000000000000000000 : ℝ)*base67 + (17636729436611601/17502500000000000000000000000000 : ℝ)*base69 + (44804955237351601/17502500000000000000000000000000 : ℝ)*base71 + (14734841963963/14002000000000000000000000000 : ℝ)*base74 + (106409284153716601/17502500000000000000000000000000 : ℝ)*base75 + (47770549888216601/17502500000000000000000000000000 : ℝ)*base77 + (140899974416391601/17502500000000000000000000000000 : ℝ)*base79 + (50860909685619/14002000000000000000000000000 : ℝ)*base82 + (1855307/312500000000000000000 : ℝ)*base90 + (1855307/312500000000000000000 : ℝ)*base92 + (1855307/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1067_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5621/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10393/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1067_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1067_s2_0 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-545800841/2500000000 : ℝ)*x 0 + (1381424073/2500000000 : ℝ)*x 1 + (2573062513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545800841/2500000000 : ℝ)^2065 ≤ (13219158292593/100000000000000 : ℝ)^1553 := by
    have hnat : (545800841 : ℕ)^2065*100000000000000^1553 ≤ 13219158292593^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545800841 2500000000 13219158292593 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381424073/2500000000 : ℝ)^2065 ≤ (2272092514137/5000000000000 : ℝ)^1553 := by
    have hnat : (1381424073 : ℕ)^2065*5000000000000^1553 ≤ 2272092514137^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381424073 2500000000 2272092514137 5000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573062513/5000000000 : ℝ)^2065 ≤ (41338991409831/100000000000000 : ℝ)^1553 := by
    have hnat : (2573062513 : ℕ)^2065*100000000000000^1553 ≤ 41338991409831^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573062513 5000000000 41338991409831 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545800841/2500000000 : ℝ), (1381424073/2500000000 : ℝ), (2573062513/5000000000 : ℝ)] ![(13219158292593/100000000000000 : ℝ), (2272092514137/5000000000000 : ℝ), (41338991409831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545800841/2500000000 : ℝ)|^2065 ≤ (13219158292593/100000000000000 : ℝ)^1553
        have hw : |(-545800841/2500000000 : ℝ)|=(545800841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381424073/2500000000 : ℝ)|^2065 ≤ (2272092514137/5000000000000 : ℝ)^1553
        have hw : |(1381424073/2500000000 : ℝ)|=(1381424073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2573062513/5000000000 : ℝ)|^2065 ≤ (41338991409831/100000000000000 : ℝ)^1553
        have hw : |(2573062513/5000000000 : ℝ)|=(2573062513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_1 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2688579209/5000000000 : ℝ)*x 0 + (-297642993/1250000000 : ℝ)*x 1 + (5146126241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688579209/5000000000 : ℝ)^2065 ≤ (21912417087207/50000000000000 : ℝ)^1553 := by
    have hnat : (2688579209 : ℕ)^2065*50000000000000^1553 ≤ 21912417087207^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688579209 5000000000 21912417087207 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297642993/1250000000 : ℝ)^2065 ≤ (7418080713169/50000000000000 : ℝ)^1553 := by
    have hnat : (297642993 : ℕ)^2065*50000000000000^1553 ≤ 7418080713169^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297642993 1250000000 7418080713169 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146126241/10000000000 : ℝ)^2065 ≤ (10334751096933/25000000000000 : ℝ)^1553 := by
    have hnat : (5146126241 : ℕ)^2065*25000000000000^1553 ≤ 10334751096933^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146126241 10000000000 10334751096933 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688579209/5000000000 : ℝ), (-297642993/1250000000 : ℝ), (5146126241/10000000000 : ℝ)] ![(21912417087207/50000000000000 : ℝ), (7418080713169/50000000000000 : ℝ), (10334751096933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688579209/5000000000 : ℝ)|^2065 ≤ (21912417087207/50000000000000 : ℝ)^1553
        have hw : |(2688579209/5000000000 : ℝ)|=(2688579209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297642993/1250000000 : ℝ)|^2065 ≤ (7418080713169/50000000000000 : ℝ)^1553
        have hw : |(-297642993/1250000000 : ℝ)|=(297642993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146126241/10000000000 : ℝ)|^2065 ≤ (10334751096933/25000000000000 : ℝ)^1553
        have hw : |(5146126241/10000000000 : ℝ)|=(5146126241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_2 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134428959/250000000 : ℝ)*x 0 + (1029225263/2000000000 : ℝ)*x 1 + (-595285981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134428959/250000000 : ℝ)^2065 ≤ (21912416772929/50000000000000 : ℝ)^1553 := by
    have hnat : (134428959 : ℕ)^2065*50000000000000^1553 ≤ 21912416772929^1553*250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134428959 250000000 21912416772929 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029225263/2000000000 : ℝ)^2065 ≤ (8267801035631/20000000000000 : ℝ)^1553 := by
    have hnat : (1029225263 : ℕ)^2065*20000000000000^1553 ≤ 8267801035631^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029225263 2000000000 8267801035631 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595285981/2500000000 : ℝ)^2065 ≤ (7418080630321/50000000000000 : ℝ)^1553 := by
    have hnat : (595285981 : ℕ)^2065*50000000000000^1553 ≤ 7418080630321^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595285981 2500000000 7418080630321 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134428959/250000000 : ℝ), (1029225263/2000000000 : ℝ), (-595285981/2500000000 : ℝ)] ![(21912416772929/50000000000000 : ℝ), (8267801035631/20000000000000 : ℝ), (7418080630321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134428959/250000000 : ℝ)|^2065 ≤ (21912416772929/50000000000000 : ℝ)^1553
        have hw : |(134428959/250000000 : ℝ)|=(134428959/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029225263/2000000000 : ℝ)|^2065 ≤ (8267801035631/20000000000000 : ℝ)^1553
        have hw : |(1029225263/2000000000 : ℝ)|=(1029225263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-595285981/2500000000 : ℝ)|^2065 ≤ (7418080630321/50000000000000 : ℝ)^1553
        have hw : |(-595285981/2500000000 : ℝ)|=(595285981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_3 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4362868241/10000000000 : ℝ)*x 0 + (2003416753/5000000000 : ℝ)*x 1 + (2375439107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362868241/10000000000 : ℝ)^2065 ≤ (33190251869021/100000000000000 : ℝ)^1553 := by
    have hnat : (4362868241 : ℕ)^2065*100000000000000^1553 ≤ 33190251869021^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362868241 10000000000 33190251869021 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003416753/5000000000 : ℝ)^2065 ≤ (29638147032149/100000000000000 : ℝ)^1553 := by
    have hnat : (2003416753 : ℕ)^2065*100000000000000^1553 ≤ 29638147032149^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003416753 5000000000 29638147032149 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2375439107/5000000000 : ℝ)^2065 ≤ (18585800538077/50000000000000 : ℝ)^1553 := by
    have hnat : (2375439107 : ℕ)^2065*50000000000000^1553 ≤ 18585800538077^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375439107 5000000000 18585800538077 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362868241/10000000000 : ℝ), (2003416753/5000000000 : ℝ), (2375439107/5000000000 : ℝ)] ![(33190251869021/100000000000000 : ℝ), (29638147032149/100000000000000 : ℝ), (18585800538077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362868241/10000000000 : ℝ)|^2065 ≤ (33190251869021/100000000000000 : ℝ)^1553
        have hw : |(4362868241/10000000000 : ℝ)|=(4362868241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003416753/5000000000 : ℝ)|^2065 ≤ (29638147032149/100000000000000 : ℝ)^1553
        have hw : |(2003416753/5000000000 : ℝ)|=(2003416753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2375439107/5000000000 : ℝ)|^2065 ≤ (18585800538077/50000000000000 : ℝ)^1553
        have hw : |(2375439107/5000000000 : ℝ)|=(2375439107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_4 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183328623/10000000000 : ℝ)*x 0 + (2574442931/5000000000 : ℝ)*x 1 + (276145339/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183328623/10000000000 : ℝ)^2065 ≤ (1322016678181/10000000000000 : ℝ)^1553 := by
    have hnat : (2183328623 : ℕ)^2065*10000000000000^1553 ≤ 1322016678181^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183328623 10000000000 1322016678181 10000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574442931/5000000000 : ℝ)^2065 ≤ (41368483608701/100000000000000 : ℝ)^1553 := by
    have hnat : (2574442931 : ℕ)^2065*100000000000000^1553 ≤ 41368483608701^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574442931 5000000000 41368483608701 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276145339/500000000 : ℝ)^2065 ≤ (11352837397847/25000000000000 : ℝ)^1553 := by
    have hnat : (276145339 : ℕ)^2065*25000000000000^1553 ≤ 11352837397847^1553*500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276145339 500000000 11352837397847 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183328623/10000000000 : ℝ), (2574442931/5000000000 : ℝ), (276145339/500000000 : ℝ)] ![(1322016678181/10000000000000 : ℝ), (41368483608701/100000000000000 : ℝ), (11352837397847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183328623/10000000000 : ℝ)|^2065 ≤ (1322016678181/10000000000000 : ℝ)^1553
        have hw : |(-2183328623/10000000000 : ℝ)|=(2183328623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574442931/5000000000 : ℝ)|^2065 ≤ (41368483608701/100000000000000 : ℝ)^1553
        have hw : |(2574442931/5000000000 : ℝ)|=(2574442931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276145339/500000000 : ℝ)|^2065 ≤ (11352837397847/25000000000000 : ℝ)^1553
        have hw : |(276145339/500000000 : ℝ)|=(276145339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_5 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2640671869/5000000000 : ℝ)*x 0 + (-200436493/1000000000 : ℝ)*x 1 + (2761453433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640671869/5000000000 : ℝ)^2065 ≤ (21394768006347/50000000000000 : ℝ)^1553 := by
    have hnat : (2640671869 : ℕ)^2065*50000000000000^1553 ≤ 21394768006347^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640671869 5000000000 21394768006347 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200436493/1000000000 : ℝ)^2065 ≤ (2359822690121/20000000000000 : ℝ)^1553 := by
    have hnat : (200436493 : ℕ)^2065*20000000000000^1553 ≤ 2359822690121^1553*1000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200436493 1000000000 2359822690121 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761453433/5000000000 : ℝ)^2065 ≤ (45411350531639/100000000000000 : ℝ)^1553 := by
    have hnat : (2761453433 : ℕ)^2065*100000000000000^1553 ≤ 45411350531639^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761453433 5000000000 45411350531639 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640671869/5000000000 : ℝ), (-200436493/1000000000 : ℝ), (2761453433/5000000000 : ℝ)] ![(21394768006347/50000000000000 : ℝ), (2359822690121/20000000000000 : ℝ), (45411350531639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640671869/5000000000 : ℝ)|^2065 ≤ (21394768006347/50000000000000 : ℝ)^1553
        have hw : |(2640671869/5000000000 : ℝ)|=(2640671869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200436493/1000000000 : ℝ)|^2065 ≤ (2359822690121/20000000000000 : ℝ)^1553
        have hw : |(-200436493/1000000000 : ℝ)|=(200436493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2761453433/5000000000 : ℝ)|^2065 ≤ (45411350531639/100000000000000 : ℝ)^1553
        have hw : |(2761453433/5000000000 : ℝ)|=(2761453433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_6 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2640671991/5000000000 : ℝ)*x 0 + (2761453351/5000000000 : ℝ)*x 1 + (-1002182411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640671991/5000000000 : ℝ)^2065 ≤ (42789538641337/100000000000000 : ℝ)^1553 := by
    have hnat : (2640671991 : ℕ)^2065*100000000000000^1553 ≤ 42789538641337^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640671991 5000000000 42789538641337 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761453351/5000000000 : ℝ)^2065 ≤ (22705674369301/50000000000000 : ℝ)^1553 := by
    have hnat : (2761453351 : ℕ)^2065*50000000000000^1553 ≤ 22705674369301^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761453351 5000000000 22705674369301 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002182411/5000000000 : ℝ)^2065 ≤ (11799112605239/100000000000000 : ℝ)^1553 := by
    have hnat : (1002182411 : ℕ)^2065*100000000000000^1553 ≤ 11799112605239^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002182411 5000000000 11799112605239 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640671991/5000000000 : ℝ), (2761453351/5000000000 : ℝ), (-1002182411/5000000000 : ℝ)] ![(42789538641337/100000000000000 : ℝ), (22705674369301/50000000000000 : ℝ), (11799112605239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640671991/5000000000 : ℝ)|^2065 ≤ (42789538641337/100000000000000 : ℝ)^1553
        have hw : |(2640671991/5000000000 : ℝ)|=(2640671991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761453351/5000000000 : ℝ)|^2065 ≤ (22705674369301/50000000000000 : ℝ)^1553
        have hw : |(2761453351/5000000000 : ℝ)|=(2761453351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002182411/5000000000 : ℝ)|^2065 ≤ (11799112605239/100000000000000 : ℝ)^1553
        have hw : |(-1002182411/5000000000 : ℝ)|=(1002182411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_7 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4363111961/10000000000 : ℝ)*x 0 + (593184109/1250000000 : ℝ)*x 1 + (1003074527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363111961/10000000000 : ℝ)^2065 ≤ (1659635861983/5000000000000 : ℝ)^1553 := by
    have hnat : (4363111961 : ℕ)^2065*5000000000000^1553 ≤ 1659635861983^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363111961 10000000000 1659635861983 5000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593184109/1250000000 : ℝ)^2065 ≤ (7423075261759/20000000000000 : ℝ)^1553 := by
    have hnat : (593184109 : ℕ)^2065*20000000000000^1553 ≤ 7423075261759^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593184109 1250000000 7423075261759 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003074527/2500000000 : ℝ)^2065 ≤ (14845953220453/50000000000000 : ℝ)^1553 := by
    have hnat : (1003074527 : ℕ)^2065*50000000000000^1553 ≤ 14845953220453^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003074527 2500000000 14845953220453 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363111961/10000000000 : ℝ), (593184109/1250000000 : ℝ), (1003074527/2500000000 : ℝ)] ![(1659635861983/5000000000000 : ℝ), (7423075261759/20000000000000 : ℝ), (14845953220453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363111961/10000000000 : ℝ)|^2065 ≤ (1659635861983/5000000000000 : ℝ)^1553
        have hw : |(4363111961/10000000000 : ℝ)|=(4363111961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(593184109/1250000000 : ℝ)|^2065 ≤ (7423075261759/20000000000000 : ℝ)^1553
        have hw : |(593184109/1250000000 : ℝ)|=(593184109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003074527/2500000000 : ℝ)|^2065 ≤ (14845953220453/50000000000000 : ℝ)^1553
        have hw : |(1003074527/2500000000 : ℝ)|=(1003074527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_8 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-49513221/5000000000 : ℝ)*x 0 + (592799089/1000000000 : ℝ)*x 1 + (2963904157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49513221/5000000000 : ℝ)^2065 ≤ (216262610143/100000000000000 : ℝ)^1553 := by
    have hnat : (49513221 : ℕ)^2065*100000000000000^1553 ≤ 216262610143^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49513221 5000000000 216262610143 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592799089/1000000000 : ℝ)^2065 ≤ (1995715612483/4000000000000 : ℝ)^1553 := by
    have hnat : (592799089 : ℕ)^2065*4000000000000^1553 ≤ 1995715612483^1553*1000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592799089 1000000000 1995715612483 4000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2963904157/5000000000 : ℝ)^2065 ≤ (6236355882929/12500000000000 : ℝ)^1553 := by
    have hnat : (2963904157 : ℕ)^2065*12500000000000^1553 ≤ 6236355882929^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963904157 5000000000 6236355882929 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49513221/5000000000 : ℝ), (592799089/1000000000 : ℝ), (2963904157/5000000000 : ℝ)] ![(216262610143/100000000000000 : ℝ), (1995715612483/4000000000000 : ℝ), (6236355882929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49513221/5000000000 : ℝ)|^2065 ≤ (216262610143/100000000000000 : ℝ)^1553
        have hw : |(-49513221/5000000000 : ℝ)|=(49513221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(592799089/1000000000 : ℝ)|^2065 ≤ (1995715612483/4000000000000 : ℝ)^1553
        have hw : |(592799089/1000000000 : ℝ)|=(592799089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2963904157/5000000000 : ℝ)|^2065 ≤ (6236355882929/12500000000000 : ℝ)^1553
        have hw : |(2963904157/5000000000 : ℝ)|=(2963904157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_9 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (158787733/2000000000 : ℝ)*x 0 + (-4971632869/10000000000 : ℝ)*x 1 + (3279264411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158787733/2000000000 : ℝ)^2065 ≤ (3444005088913/100000000000000 : ℝ)^1553 := by
    have hnat : (158787733 : ℕ)^2065*100000000000000^1553 ≤ 3444005088913^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158787733 2000000000 3444005088913 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4971632869/10000000000 : ℝ)^2065 ≤ (7897133742371/20000000000000 : ℝ)^1553 := by
    have hnat : (4971632869 : ℕ)^2065*20000000000000^1553 ≤ 7897133742371^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971632869 10000000000 7897133742371 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3279264411/5000000000 : ℝ)^2065 ≤ (11414065236163/20000000000000 : ℝ)^1553 := by
    have hnat : (3279264411 : ℕ)^2065*20000000000000^1553 ≤ 11414065236163^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279264411 5000000000 11414065236163 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(158787733/2000000000 : ℝ), (-4971632869/10000000000 : ℝ), (3279264411/5000000000 : ℝ)] ![(3444005088913/100000000000000 : ℝ), (7897133742371/20000000000000 : ℝ), (11414065236163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(158787733/2000000000 : ℝ)|^2065 ≤ (3444005088913/100000000000000 : ℝ)^1553
        have hw : |(158787733/2000000000 : ℝ)|=(158787733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4971632869/10000000000 : ℝ)|^2065 ≤ (7897133742371/20000000000000 : ℝ)^1553
        have hw : |(-4971632869/10000000000 : ℝ)|=(4971632869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3279264411/5000000000 : ℝ)|^2065 ≤ (11414065236163/20000000000000 : ℝ)^1553
        have hw : |(3279264411/5000000000 : ℝ)|=(3279264411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_10 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (792563179/10000000000 : ℝ)*x 0 + (1310997177/2000000000 : ℝ)*x 1 + (-2488132303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792563179/10000000000 : ℝ)^2065 ≤ (3436073549037/100000000000000 : ℝ)^1553 := by
    have hnat : (792563179 : ℕ)^2065*100000000000000^1553 ≤ 3436073549037^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792563179 10000000000 3436073549037 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310997177/2000000000 : ℝ)^2065 ≤ (28514668120821/50000000000000 : ℝ)^1553 := by
    have hnat : (1310997177 : ℕ)^2065*50000000000000^1553 ≤ 28514668120821^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310997177 2000000000 28514668120821 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2488132303/5000000000 : ℝ)^2065 ≤ (7906918039/20000000000 : ℝ)^1553 := by
    have hnat : (2488132303 : ℕ)^2065*20000000000^1553 ≤ 7906918039^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488132303 5000000000 7906918039 20000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792563179/10000000000 : ℝ), (1310997177/2000000000 : ℝ), (-2488132303/5000000000 : ℝ)] ![(3436073549037/100000000000000 : ℝ), (28514668120821/50000000000000 : ℝ), (7906918039/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792563179/10000000000 : ℝ)|^2065 ≤ (3436073549037/100000000000000 : ℝ)^1553
        have hw : |(792563179/10000000000 : ℝ)|=(792563179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310997177/2000000000 : ℝ)|^2065 ≤ (28514668120821/50000000000000 : ℝ)^1553
        have hw : |(1310997177/2000000000 : ℝ)|=(1310997177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2488132303/5000000000 : ℝ)|^2065 ≤ (7906918039/20000000000 : ℝ)^1553
        have hw : |(-2488132303/5000000000 : ℝ)|=(2488132303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s2_11 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26271351/625000000 : ℝ)*x 0 + (1173893921/2000000000 : ℝ)*x 1 + (1468340539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26271351/625000000 : ℝ)^2065 ≤ (739257026541/50000000000000 : ℝ)^1553 := by
    have hnat : (26271351 : ℕ)^2065*50000000000000^1553 ≤ 739257026541^1553*625000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26271351 625000000 739257026541 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173893921/2000000000 : ℝ)^2065 ≤ (78782448651/160000000000 : ℝ)^1553 := by
    have hnat : (1173893921 : ℕ)^2065*160000000000^1553 ≤ 78782448651^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173893921 2000000000 78782448651 160000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468340539/2500000000 : ℝ)^2065 ≤ (3080153470347/6250000000000 : ℝ)^1553 := by
    have hnat : (1468340539 : ℕ)^2065*6250000000000^1553 ≤ 3080153470347^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468340539 2500000000 3080153470347 6250000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26271351/625000000 : ℝ), (1173893921/2000000000 : ℝ), (1468340539/2500000000 : ℝ)] ![(739257026541/50000000000000 : ℝ), (78782448651/160000000000 : ℝ), (3080153470347/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26271351/625000000 : ℝ)|^2065 ≤ (739257026541/50000000000000 : ℝ)^1553
        have hw : |(26271351/625000000 : ℝ)|=(26271351/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1173893921/2000000000 : ℝ)|^2065 ≤ (78782448651/160000000000 : ℝ)^1553
        have hw : |(1173893921/2000000000 : ℝ)|=(1173893921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1468340539/2500000000 : ℝ)|^2065 ≤ (3080153470347/6250000000000 : ℝ)^1553
        have hw : |(1468340539/2500000000 : ℝ)|=(1468340539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1067_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8717/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5219/100000 : ℝ) ^ (8259/2048 : ℝ) ≤ (673589418587377/100000000000000000000 : ℝ) := by
    have hpowers : (5219/100000 : ℝ)^8259 ≤ (673589418587377/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5219 : ℕ)^8259*100000000000000000000^2048 ≤ 673589418587377^2048*100000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5219 100000 673589418587377 100000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5219/100000 : ℝ)) (X := (673589418587377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10393/50000 : ℝ) ^ (8259/2048 : ℝ) ≤ (177322838287804299/100000000000000000000 : ℝ) := by
    have hpowers : (10393/50000 : ℝ)^8259 ≤ (177322838287804299/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10393 : ℕ)^8259*100000000000000000000^2048 ≤ 177322838287804299^2048*50000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10393 50000 177322838287804299 100000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10393/50000 : ℝ)) (X := (177322838287804299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000673589418587377/50000000000000000000 : ℝ) ≤ (250000835152041/250000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (50000673589418587377/50000000000000000000 : ℝ)^2048 ≤ (250000835152041/250000000000000 : ℝ)^8259 := by
      have hnat : (50000673589418587377 : ℕ)^2048*250000000000000^8259 ≤ 250000835152041^8259*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000673589418587377 50000000000000000000 250000835152041 250000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000835152041/250000000000000 : ℝ)) (X := (50000673589418587377/50000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25044499106926597919/25000000000000000000 : ℝ) ≤ (5002205430172697/5000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (25044499106926597919/25000000000000000000 : ℝ)^2048 ≤ (5002205430172697/5000000000000000 : ℝ)^8259 := by
      have hnat : (25044499106926597919 : ℕ)^2048*5000000000000000^8259 ≤ 5002205430172697^8259*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044499106926597919 25000000000000000000 5002205430172697 5000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002205430172697/5000000000000000 : ℝ)) (X := (25044499106926597919/25000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50177322838287804299/50000000000000000000 : ℝ) ≤ (2502197078652287/2500000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (50177322838287804299/50000000000000000000 : ℝ)^2048 ≤ (2502197078652287/2500000000000000 : ℝ)^8259 := by
      have hnat : (50177322838287804299 : ℕ)^2048*2500000000000000^8259 ≤ 2502197078652287^8259*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50177322838287804299 50000000000000000000 2502197078652287 2500000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502197078652287/2500000000000000 : ℝ)) (X := (50177322838287804299/50000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(673589418587377/100000000000000000000 : ℝ) ≤ ((38906207041216956407/38917500000000000000 : ℝ)+2*(2188727131877/778350000000000 : ℝ)*(5219/100000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (38906207041216956407/38917500000000000000 : ℝ)+2*(2188727131877/778350000000000 : ℝ)*(5219/100000 : ℝ)=(250000835152041/250000000000000 : ℝ) by norm_num, show 1+2*(673589418587377/100000000000000000000 : ℝ)=(50000673589418587377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(177322838287804299/100000000000000000000 : ℝ)+(673589418587377/100000000000000000000 : ℝ) ≤ ((38906207041216956407/38917500000000000000 : ℝ)+(2188727131877/778350000000000 : ℝ)*((10393/50000 : ℝ)+(5219/100000 : ℝ)))^(8259/2048 : ℝ) := by
    rw [show (38906207041216956407/38917500000000000000 : ℝ)+(2188727131877/778350000000000 : ℝ)*((10393/50000 : ℝ)+(5219/100000 : ℝ))=(5002205430172697/5000000000000000 : ℝ) by norm_num, show 1+(177322838287804299/100000000000000000000 : ℝ)+(673589418587377/100000000000000000000 : ℝ)=(25044499106926597919/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(177322838287804299/100000000000000000000 : ℝ) ≤ ((38906207041216956407/38917500000000000000 : ℝ)+2*(2188727131877/778350000000000 : ℝ)*(10393/50000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (38906207041216956407/38917500000000000000 : ℝ)+2*(2188727131877/778350000000000 : ℝ)*(10393/50000 : ℝ)=(2502197078652287/2500000000000000 : ℝ) by norm_num, show 1+2*(177322838287804299/100000000000000000000 : ℝ)=(50177322838287804299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38906207041216956407/38917500000000000000 : ℝ)*(X 1 0+X 2 0)+(2188727131877/778350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (5219/100000 : ℝ)) (hi := (10393/50000 : ℝ)) (c := (38906207041216956407/38917500000000000000 : ℝ)) (alpha := (2188727131877/778350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38906207041216956407/38917500000000000000 : ℝ)*(X 0 1+X 2 1)+(2188727131877/778350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (5219/100000 : ℝ)) (hi := (10393/50000 : ℝ)) (c := (38906207041216956407/38917500000000000000 : ℝ)) (alpha := (2188727131877/778350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38906207041216956407/38917500000000000000 : ℝ)*(X 0 2+X 1 2)+(2188727131877/778350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (5219/100000 : ℝ)) (hi := (10393/50000 : ℝ)) (c := (38906207041216956407/38917500000000000000 : ℝ)) (alpha := (2188727131877/778350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-545800841/2500000000 : ℝ)*X 0 0+(1381424073/2500000000 : ℝ)*X 0 1+(2573062513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688579209/5000000000 : ℝ)*X 1 0+(-297642993/1250000000 : ℝ)*X 1 1+(5146126241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134428959/250000000 : ℝ)*X 2 0+(1029225263/2000000000 : ℝ)*X 2 1+(-595285981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362868241/10000000000 : ℝ)*X 0 0+(2003416753/5000000000 : ℝ)*X 0 1+(2375439107/5000000000 : ℝ)*X 0 2+(4362868241/10000000000 : ℝ)*X 1 0+(2003416753/5000000000 : ℝ)*X 1 1+(2375439107/5000000000 : ℝ)*X 1 2+(4362868241/10000000000 : ℝ)*X 2 0+(2003416753/5000000000 : ℝ)*X 2 1+(2375439107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183328623/10000000000 : ℝ)*X 0 0+(2574442931/5000000000 : ℝ)*X 0 1+(276145339/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640671869/5000000000 : ℝ)*X 1 0+(-200436493/1000000000 : ℝ)*X 1 1+(2761453433/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640671991/5000000000 : ℝ)*X 2 0+(2761453351/5000000000 : ℝ)*X 2 1+(-1002182411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363111961/10000000000 : ℝ)*X 0 0+(593184109/1250000000 : ℝ)*X 0 1+(1003074527/2500000000 : ℝ)*X 0 2+(4363111961/10000000000 : ℝ)*X 1 0+(593184109/1250000000 : ℝ)*X 1 1+(1003074527/2500000000 : ℝ)*X 1 2+(4363111961/10000000000 : ℝ)*X 2 0+(593184109/1250000000 : ℝ)*X 2 1+(1003074527/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-49513221/5000000000 : ℝ)*X 0 0+(592799089/1000000000 : ℝ)*X 0 1+(2963904157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((158787733/2000000000 : ℝ)*X 1 0+(-4971632869/10000000000 : ℝ)*X 1 1+(3279264411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((792563179/10000000000 : ℝ)*X 2 0+(1310997177/2000000000 : ℝ)*X 2 1+(-2488132303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((26271351/625000000 : ℝ)*X 0 0+(1173893921/2000000000 : ℝ)*X 0 1+(1468340539/2500000000 : ℝ)*X 0 2+(26271351/625000000 : ℝ)*X 1 0+(1173893921/2000000000 : ℝ)*X 1 1+(1468340539/2500000000 : ℝ)*X 1 2+(26271351/625000000 : ℝ)*X 2 0+(1173893921/2000000000 : ℝ)*X 2 1+(1468340539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68506520016928462073621/25945000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248662197481007/12500000000000 : ℝ)*(major0) + (248662197481007/12500000000000 : ℝ)*(major1) + (248662197481007/12500000000000 : ℝ)*(major2) + (1317284620058933/50000000000000 : ℝ)*(sp0) + (26345794654409/1000000000000 : ℝ)*(sp1) + (658644962383663/25000000000000 : ℝ)*(sp2) + (67200263884321/5000000000000 : ℝ)*(sp3) + (18081172333/100000000000000 : ℝ)*(sp4) + (398034987/5000000000000 : ℝ)*(sp5) + (7602785879/100000000000000 : ℝ)*(sp6) + (48216973/4000000000000 : ℝ)*(sp8) + (275143471/25000000000000 : ℝ)*(sp9) + (1074393993/100000000000000 : ℝ)*(sp10) + (633640053/50000000000000 : ℝ)*(sp11) + (672003272483263/50000000000000 : ℝ)*(f.failure) + (658647131678631/25000000000000 : ℝ)*(f.sum) + (106630773938419/77835000000000000000000000000 : ℝ)*base65 + (1938342419175217/162156250000000000000000000000000 : ℝ)*base68 + (49744908164675217/162156250000000000000000000000000 : ℝ)*base70 + (2048032395582637283/162156250000000000000000000000000 : ℝ)*base71 + (43922223408433/38917500000000000000000000000 : ℝ)*base74 + (369239110648987717/162156250000000000000000000000000 : ℝ)*base76 + (1150861517211231033/162156250000000000000000000000000 : ℝ)*base77 + (573293267262856033/162156250000000000000000000000000 : ℝ)*base79 + (13745074376513/9729375000000000000000000000 : ℝ)*base81 + (3769651/1250000000000000000000 : ℝ)*base90 + (3769651/1250000000000000000000 : ℝ)*base92 + (3769651/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2537251278086246142602208747/162156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1009395761071871/50000000000000 : ℝ)*(major0) + (1009395761071871/50000000000000 : ℝ)*(major1) + (1009395761071871/50000000000000 : ℝ)*(major2) + (218470093/20000000000000 : ℝ)*(sp1) + (135240291/25000000000000 : ℝ)*(sp2) + (56646907/20000000000000 : ℝ)*(sp3) + (1336823755688241/50000000000000 : ℝ)*(sp4) + (10443934942589/390625000000 : ℝ)*(sp5) + (1336823881699347/50000000000000 : ℝ)*(sp6) + (1363931712900493/100000000000000 : ℝ)*(sp7) + (904453991/50000000000000 : ℝ)*(sp8) + (176526243/20000000000000 : ℝ)*(sp9) + (1015924607/100000000000000 : ℝ)*(sp10) + (603151437/50000000000000 : ℝ)*(sp11) + (681966601218951/50000000000000 : ℝ)*(f.failure) + (167103082517779/6250000000000 : ℝ)*(f.sum) + (34281045723901/38917500000000000000000000000 : ℝ)*base66 + (3274322745571907501/648625000000000000000000000000000 : ℝ)*base68 + (4373646478221157501/648625000000000000000000000000000 : ℝ)*base70 + (581375905712967499/648625000000000000000000000000000 : ℝ)*base71 + (245293907679467/77835000000000000000000000000 : ℝ)*base74 + (3822986834653532501/648625000000000000000000000000000 : ℝ)*base76 + (2799242847149032501/648625000000000000000000000000000 : ℝ)*base78 + (8125952502625782501/648625000000000000000000000000000 : ℝ)*base80 + (20587727405063/19458750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (18783973/1250000000000000000000 : ℝ)*base89 + (18783973/1250000000000000000000 : ℝ)*base91 + (18783973/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1067_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8717/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1067_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1067_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8717/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8369/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1067_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1067_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1067_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8717/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8369/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1067_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

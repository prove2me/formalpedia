-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1263_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:55:37.477977+00:00
-- url     : https://prove2.me/submissions/e590f2ad-ed30-4001-9d4c-e3a4fffc0ce7

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
theorem support_rectangle_w1263_s6_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-527579097/2500000000 : ℝ)*x 0 + (67387191/125000000 : ℝ)*x 1 + (5267329093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527579097/2500000000 : ℝ)^1057 ≤ (6417689811113/50000000000000 : ℝ)^801 := by
    have hnat : (527579097 : ℕ)^1057*50000000000000^801 ≤ 6417689811113^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527579097 2500000000 6417689811113 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67387191/125000000 : ℝ)^1057 ≤ (5531183942459/12500000000000 : ℝ)^801 := by
    have hnat : (67387191 : ℕ)^1057*12500000000000^801 ≤ 5531183942459^801*125000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67387191 125000000 5531183942459 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267329093/10000000000 : ℝ)^1057 ≤ (42915148821147/100000000000000 : ℝ)^801 := by
    have hnat : (5267329093 : ℕ)^1057*100000000000000^801 ≤ 42915148821147^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267329093 10000000000 42915148821147 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527579097/2500000000 : ℝ), (67387191/125000000 : ℝ), (5267329093/10000000000 : ℝ)] ![(6417689811113/50000000000000 : ℝ), (5531183942459/12500000000000 : ℝ), (42915148821147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527579097/2500000000 : ℝ)|^1057 ≤ (6417689811113/50000000000000 : ℝ)^801
        have hw : |(-527579097/2500000000 : ℝ)|=(527579097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67387191/125000000 : ℝ)|^1057 ≤ (5531183942459/12500000000000 : ℝ)^801
        have hw : |(67387191/125000000 : ℝ)|=(67387191/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267329093/10000000000 : ℝ)|^1057 ≤ (42915148821147/100000000000000 : ℝ)^801
        have hw : |(5267329093/10000000000 : ℝ)|=(5267329093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672119171/5000000000 : ℝ)*x 0 + (-2173005707/10000000000 : ℝ)*x 1 + (82302017/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672119171/5000000000 : ℝ)^1057 ≤ (43743949372621/100000000000000 : ℝ)^801 := by
    have hnat : (2672119171 : ℕ)^1057*100000000000000^801 ≤ 43743949372621^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672119171 5000000000 43743949372621 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173005707/10000000000 : ℝ)^1057 ≤ (13340901846427/100000000000000 : ℝ)^801 := by
    have hnat : (2173005707 : ℕ)^1057*100000000000000^801 ≤ 13340901846427^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173005707 10000000000 13340901846427 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82302017/156250000 : ℝ)^1057 ≤ (4291514876739/10000000000000 : ℝ)^801 := by
    have hnat : (82302017 : ℕ)^1057*10000000000000^801 ≤ 4291514876739^801*156250000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82302017 156250000 4291514876739 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672119171/5000000000 : ℝ), (-2173005707/10000000000 : ℝ), (82302017/156250000 : ℝ)] ![(43743949372621/100000000000000 : ℝ), (13340901846427/100000000000000 : ℝ), (4291514876739/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672119171/5000000000 : ℝ)|^1057 ≤ (43743949372621/100000000000000 : ℝ)^801
        have hw : |(2672119171/5000000000 : ℝ)|=(2672119171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173005707/10000000000 : ℝ)|^1057 ≤ (13340901846427/100000000000000 : ℝ)^801
        have hw : |(-2173005707/10000000000 : ℝ)|=(2173005707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82302017/156250000 : ℝ)|^1057 ≤ (4291514876739/10000000000000 : ℝ)^801
        have hw : |(82302017/156250000 : ℝ)|=(82302017/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336059587/2500000000 : ℝ)*x 0 + (5267329087/10000000000 : ℝ)*x 1 + (-21730057/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336059587/2500000000 : ℝ)^1057 ≤ (43743949437429/100000000000000 : ℝ)^801 := by
    have hnat : (1336059587 : ℕ)^1057*100000000000000^801 ≤ 43743949437429^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336059587 2500000000 43743949437429 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267329087/10000000000 : ℝ)^1057 ≤ (42915148756639/100000000000000 : ℝ)^801 := by
    have hnat : (5267329087 : ℕ)^1057*100000000000000^801 ≤ 42915148756639^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267329087 10000000000 42915148756639 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21730057/100000000 : ℝ)^1057 ≤ (3335225447429/25000000000000 : ℝ)^801 := by
    have hnat : (21730057 : ℕ)^1057*25000000000000^801 ≤ 3335225447429^801*100000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21730057 100000000 3335225447429 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336059587/2500000000 : ℝ), (5267329087/10000000000 : ℝ), (-21730057/100000000 : ℝ)] ![(43743949437429/100000000000000 : ℝ), (42915148756639/100000000000000 : ℝ), (3335225447429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336059587/2500000000 : ℝ)|^1057 ≤ (43743949437429/100000000000000 : ℝ)^801
        have hw : |(1336059587/2500000000 : ℝ)|=(1336059587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267329087/10000000000 : ℝ)|^1057 ≤ (42915148756639/100000000000000 : ℝ)^801
        have hw : |(5267329087/10000000000 : ℝ)|=(5267329087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21730057/100000000 : ℝ)|^1057 ≤ (3335225447429/25000000000000 : ℝ)^801
        have hw : |(-21730057/100000000 : ℝ)|=(21730057/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4347892719/10000000000 : ℝ)*x 0 + (4223735777/10000000000 : ℝ)*x 1 + (895115651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347892719/10000000000 : ℝ)^1057 ≤ (33317511000357/100000000000000 : ℝ)^801 := by
    have hnat : (4347892719 : ℕ)^1057*100000000000000^801 ≤ 33317511000357^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347892719 10000000000 33317511000357 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223735777/10000000000 : ℝ)^1057 ≤ (32067805017031/100000000000000 : ℝ)^801 := by
    have hnat : (4223735777 : ℕ)^1057*100000000000000^801 ≤ 32067805017031^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223735777 10000000000 32067805017031 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895115651/2000000000 : ℝ)^1057 ≤ (6922936791761/20000000000000 : ℝ)^801 := by
    have hnat : (895115651 : ℕ)^1057*20000000000000^801 ≤ 6922936791761^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895115651 2000000000 6922936791761 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347892719/10000000000 : ℝ), (4223735777/10000000000 : ℝ), (895115651/2000000000 : ℝ)] ![(33317511000357/100000000000000 : ℝ), (32067805017031/100000000000000 : ℝ), (6922936791761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347892719/10000000000 : ℝ)|^1057 ≤ (33317511000357/100000000000000 : ℝ)^801
        have hw : |(4347892719/10000000000 : ℝ)|=(4347892719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223735777/10000000000 : ℝ)|^1057 ≤ (32067805017031/100000000000000 : ℝ)^801
        have hw : |(4223735777/10000000000 : ℝ)|=(4223735777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895115651/2000000000 : ℝ)|^1057 ≤ (6922936791761/20000000000000 : ℝ)^801
        have hw : |(895115651/2000000000 : ℝ)|=(895115651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110321237/10000000000 : ℝ)*x 0 + (5267641551/10000000000 : ℝ)*x 1 + (5390661531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110321237/10000000000 : ℝ)^1057 ≤ (6417709270357/50000000000000 : ℝ)^801 := by
    have hnat : (2110321237 : ℕ)^1057*50000000000000^801 ≤ 6417709270357^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110321237 10000000000 6417709270357 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267641551/10000000000 : ℝ)^1057 ≤ (42918508195531/100000000000000 : ℝ)^801 := by
    have hnat : (5267641551 : ℕ)^1057*100000000000000^801 ≤ 42918508195531^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267641551 10000000000 42918508195531 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390661531/10000000000 : ℝ)^1057 ≤ (44246073241121/100000000000000 : ℝ)^801 := by
    have hnat : (5390661531 : ℕ)^1057*100000000000000^801 ≤ 44246073241121^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390661531 10000000000 44246073241121 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110321237/10000000000 : ℝ), (5267641551/10000000000 : ℝ), (5390661531/10000000000 : ℝ)] ![(6417709270357/50000000000000 : ℝ), (42918508195531/100000000000000 : ℝ), (44246073241121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110321237/10000000000 : ℝ)|^1057 ≤ (6417709270357/50000000000000 : ℝ)^801
        have hw : |(-2110321237/10000000000 : ℝ)|=(2110321237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267641551/10000000000 : ℝ)|^1057 ≤ (42918508195531/100000000000000 : ℝ)^801
        have hw : |(5267641551/10000000000 : ℝ)|=(5267641551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390661531/10000000000 : ℝ)|^1057 ≤ (44246073241121/100000000000000 : ℝ)^801
        have hw : |(5390661531/10000000000 : ℝ)|=(5390661531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062529113/2000000000 : ℝ)*x 0 + (-2049673379/10000000000 : ℝ)*x 1 + (2695330437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062529113/2000000000 : ℝ)^1057 ≤ (43403030192947/100000000000000 : ℝ)^801 := by
    have hnat : (1062529113 : ℕ)^1057*100000000000000^801 ≤ 43403030192947^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062529113 2000000000 43403030192947 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049673379/10000000000 : ℝ)^1057 ≤ (1235090366649/10000000000000 : ℝ)^801 := by
    have hnat : (2049673379 : ℕ)^1057*10000000000000^801 ≤ 1235090366649^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049673379 10000000000 1235090366649 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695330437/5000000000 : ℝ)^1057 ≤ (22123033062523/50000000000000 : ℝ)^801 := by
    have hnat : (2695330437 : ℕ)^1057*50000000000000^801 ≤ 22123033062523^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695330437 5000000000 22123033062523 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062529113/2000000000 : ℝ), (-2049673379/10000000000 : ℝ), (2695330437/5000000000 : ℝ)] ![(43403030192947/100000000000000 : ℝ), (1235090366649/10000000000000 : ℝ), (22123033062523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062529113/2000000000 : ℝ)|^1057 ≤ (43403030192947/100000000000000 : ℝ)^801
        have hw : |(1062529113/2000000000 : ℝ)|=(1062529113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049673379/10000000000 : ℝ)|^1057 ≤ (1235090366649/10000000000000 : ℝ)^801
        have hw : |(-2049673379/10000000000 : ℝ)|=(2049673379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695330437/5000000000 : ℝ)|^1057 ≤ (22123033062523/50000000000000 : ℝ)^801
        have hw : |(2695330437/5000000000 : ℝ)|=(2695330437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312645937/10000000000 : ℝ)*x 0 + (5390660421/10000000000 : ℝ)*x 1 + (-512418373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312645937/10000000000 : ℝ)^1057 ≤ (43403034203411/100000000000000 : ℝ)^801 := by
    have hnat : (5312645937 : ℕ)^1057*100000000000000^801 ≤ 43403034203411^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312645937 10000000000 43403034203411 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390660421/10000000000 : ℝ)^1057 ≤ (44246061218529/100000000000000 : ℝ)^801 := by
    have hnat : (5390660421 : ℕ)^1057*100000000000000^801 ≤ 44246061218529^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390660421 10000000000 44246061218529 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512418373/2500000000 : ℝ)^1057 ≤ (494036182601/4000000000000 : ℝ)^801 := by
    have hnat : (512418373 : ℕ)^1057*4000000000000^801 ≤ 494036182601^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512418373 2500000000 494036182601 4000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312645937/10000000000 : ℝ), (5390660421/10000000000 : ℝ), (-512418373/2500000000 : ℝ)] ![(43403034203411/100000000000000 : ℝ), (44246061218529/100000000000000 : ℝ), (494036182601/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312645937/10000000000 : ℝ)|^1057 ≤ (43403034203411/100000000000000 : ℝ)^801
        have hw : |(5312645937/10000000000 : ℝ)|=(5312645937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390660421/10000000000 : ℝ)|^1057 ≤ (44246061218529/100000000000000 : ℝ)^801
        have hw : |(5390660421/10000000000 : ℝ)|=(5390660421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512418373/2500000000 : ℝ)|^1057 ≤ (494036182601/4000000000000 : ℝ)^801
        have hw : |(-512418373/2500000000 : ℝ)|=(512418373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (271743867/625000000 : ℝ)*x 0 + (894988253/2000000000 : ℝ)*x 1 + (21121877/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271743867/625000000 : ℝ)^1057 ≤ (33317603555341/100000000000000 : ℝ)^801 := by
    have hnat : (271743867 : ℕ)^1057*100000000000000^801 ≤ 33317603555341^801*625000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271743867 625000000 33317603555341 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894988253/2000000000 : ℝ)^1057 ≤ (8652045753707/25000000000000 : ℝ)^801 := by
    have hnat : (894988253 : ℕ)^1057*25000000000000^801 ≤ 8652045753707^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894988253 2000000000 8652045753707 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21121877/50000000 : ℝ)^1057 ≤ (32074213416037/100000000000000 : ℝ)^801 := by
    have hnat : (21121877 : ℕ)^1057*100000000000000^801 ≤ 32074213416037^801*50000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21121877 50000000 32074213416037 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271743867/625000000 : ℝ), (894988253/2000000000 : ℝ), (21121877/50000000 : ℝ)] ![(33317603555341/100000000000000 : ℝ), (8652045753707/25000000000000 : ℝ), (32074213416037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271743867/625000000 : ℝ)|^1057 ≤ (33317603555341/100000000000000 : ℝ)^801
        have hw : |(271743867/625000000 : ℝ)|=(271743867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894988253/2000000000 : ℝ)|^1057 ≤ (8652045753707/25000000000000 : ℝ)^801
        have hw : |(894988253/2000000000 : ℝ)|=(894988253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21121877/50000000 : ℝ)|^1057 ≤ (32074213416037/100000000000000 : ℝ)^801
        have hw : |(21121877/50000000 : ℝ)|=(21121877/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_8 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-9580211/2000000000 : ℝ)*x 0 + (5910040477/10000000000 : ℝ)*x 1 + (5910078019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9580211/2000000000 : ℝ)^1057 ≤ (43446241483/50000000000000 : ℝ)^801 := by
    have hnat : (9580211 : ℕ)^1057*50000000000000^801 ≤ 43446241483^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9580211 2000000000 43446241483 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910040477/10000000000 : ℝ)^1057 ≤ (49956344375437/100000000000000 : ℝ)^801 := by
    have hnat : (5910040477 : ℕ)^1057*100000000000000^801 ≤ 49956344375437^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910040477 10000000000 49956344375437 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5910078019/10000000000 : ℝ)^1057 ≤ (24978381565463/50000000000000 : ℝ)^801 := by
    have hnat : (5910078019 : ℕ)^1057*50000000000000^801 ≤ 24978381565463^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910078019 10000000000 24978381565463 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9580211/2000000000 : ℝ), (5910040477/10000000000 : ℝ), (5910078019/10000000000 : ℝ)] ![(43446241483/50000000000000 : ℝ), (49956344375437/100000000000000 : ℝ), (24978381565463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9580211/2000000000 : ℝ)|^1057 ≤ (43446241483/50000000000000 : ℝ)^801
        have hw : |(-9580211/2000000000 : ℝ)|=(9580211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910040477/10000000000 : ℝ)|^1057 ≤ (49956344375437/100000000000000 : ℝ)^801
        have hw : |(5910040477/10000000000 : ℝ)|=(5910040477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5910078019/10000000000 : ℝ)|^1057 ≤ (24978381565463/50000000000000 : ℝ)^801
        have hw : |(5910078019/10000000000 : ℝ)|=(5910078019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s6_9 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (19222757/125000000 : ℝ)*x 0 + (2861960939/5000000000 : ℝ)*x 1 + (5336055311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19222757/125000000 : ℝ)^1057 ≤ (8453572989389/100000000000000 : ℝ)^801 := by
    have hnat : (19222757 : ℕ)^1057*100000000000000^801 ≤ 8453572989389^801*125000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19222757 125000000 8453572989389 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2861960939/5000000000 : ℝ)^1057 ≤ (47890843080889/100000000000000 : ℝ)^801 := by
    have hnat : (2861960939 : ℕ)^1057*100000000000000^801 ≤ 47890843080889^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861960939 5000000000 47890843080889 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5336055311/10000000000 : ℝ)^1057 ≤ (43655583916309/100000000000000 : ℝ)^801 := by
    have hnat : (5336055311 : ℕ)^1057*100000000000000^801 ≤ 43655583916309^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336055311 10000000000 43655583916309 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19222757/125000000 : ℝ), (2861960939/5000000000 : ℝ), (5336055311/10000000000 : ℝ)] ![(8453572989389/100000000000000 : ℝ), (47890843080889/100000000000000 : ℝ), (43655583916309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19222757/125000000 : ℝ)|^1057 ≤ (8453572989389/100000000000000 : ℝ)^801
        have hw : |(19222757/125000000 : ℝ)|=(19222757/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2861960939/5000000000 : ℝ)|^1057 ≤ (47890843080889/100000000000000 : ℝ)^801
        have hw : |(2861960939/5000000000 : ℝ)|=(2861960939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5336055311/10000000000 : ℝ)|^1057 ≤ (43655583916309/100000000000000 : ℝ)^801
        have hw : |(5336055311/10000000000 : ℝ)|=(5336055311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (23/200 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14139/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14139/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14139/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14139/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14139/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14139/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11481/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (13158408730034783/100000000000000000000 : ℝ) := by
    have hpowers : (11481/100000 : ℝ)^8455 ≤ (13158408730034783/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11481 : ℕ)^8455*100000000000000000000^2048 ≤ 13158408730034783^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11481 100000 13158408730034783 100000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11481/100000 : ℝ)) (X := (13158408730034783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14139/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (31086603388522487/100000000000000000000 : ℝ) := by
    have hpowers : (14139/100000 : ℝ)^8455 ≤ (31086603388522487/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14139 : ℕ)^8455*100000000000000000000^2048 ≤ 31086603388522487^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14139 100000 31086603388522487 100000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14139/100000 : ℝ)) (X := (31086603388522487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013158408730034783/50000000000000000000 : ℝ) ≤ (10000637391707407/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (50013158408730034783/50000000000000000000 : ℝ)^2048 ≤ (10000637391707407/10000000000000000 : ℝ)^8455 := by
      have hnat : (50013158408730034783 : ℕ)^2048*10000000000000000^8455 ≤ 10000637391707407^8455*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013158408730034783 50000000000000000000 10000637391707407 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000637391707407/10000000000000000 : ℝ)) (X := (50013158408730034783/50000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004424501211855727/10000000000000000000 : ℝ) ≤ (10001071538714823/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (10004424501211855727/10000000000000000000 : ℝ)^2048 ≤ (10001071538714823/10000000000000000 : ℝ)^8455 := by
      have hnat : (10004424501211855727 : ℕ)^2048*10000000000000000^8455 ≤ 10001071538714823^8455*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004424501211855727 10000000000000000000 10001071538714823 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001071538714823/10000000000000000 : ℝ)) (X := (10004424501211855727/10000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031086603388522487/50000000000000000000 : ℝ) ≤ (10001505685722239/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (50031086603388522487/50000000000000000000 : ℝ)^2048 ≤ (10001505685722239/10000000000000000 : ℝ)^8455 := by
      have hnat : (50031086603388522487 : ℕ)^2048*10000000000000000^8455 ≤ 10001505685722239^8455*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031086603388522487 50000000000000000000 10001505685722239 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001505685722239/10000000000000000 : ℝ)) (X := (50031086603388522487/50000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13158408730034783/100000000000000000000 : ℝ) ≤ ((4428620883929000269/4430000000000000000 : ℝ)+2*(54268375927/33225000000000 : ℝ)*(11481/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (4428620883929000269/4430000000000000000 : ℝ)+2*(54268375927/33225000000000 : ℝ)*(11481/100000 : ℝ)=(10000637391707407/10000000000000000 : ℝ) by norm_num, show 1+2*(13158408730034783/100000000000000000000 : ℝ)=(50013158408730034783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31086603388522487/100000000000000000000 : ℝ)+(13158408730034783/100000000000000000000 : ℝ) ≤ ((4428620883929000269/4430000000000000000 : ℝ)+(54268375927/33225000000000 : ℝ)*((14139/100000 : ℝ)+(11481/100000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (4428620883929000269/4430000000000000000 : ℝ)+(54268375927/33225000000000 : ℝ)*((14139/100000 : ℝ)+(11481/100000 : ℝ))=(10001071538714823/10000000000000000 : ℝ) by norm_num, show 1+(31086603388522487/100000000000000000000 : ℝ)+(13158408730034783/100000000000000000000 : ℝ)=(10004424501211855727/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31086603388522487/100000000000000000000 : ℝ) ≤ ((4428620883929000269/4430000000000000000 : ℝ)+2*(54268375927/33225000000000 : ℝ)*(14139/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (4428620883929000269/4430000000000000000 : ℝ)+2*(54268375927/33225000000000 : ℝ)*(14139/100000 : ℝ)=(10001505685722239/10000000000000000 : ℝ) by norm_num, show 1+2*(31086603388522487/100000000000000000000 : ℝ)=(50031086603388522487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4428620883929000269/4430000000000000000 : ℝ)*(X 1 0+X 2 0)+(54268375927/33225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (14139/100000 : ℝ)) (c := (4428620883929000269/4430000000000000000 : ℝ)) (alpha := (54268375927/33225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4428620883929000269/4430000000000000000 : ℝ)*(X 0 1+X 2 1)+(54268375927/33225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (14139/100000 : ℝ)) (c := (4428620883929000269/4430000000000000000 : ℝ)) (alpha := (54268375927/33225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4428620883929000269/4430000000000000000 : ℝ)*(X 0 2+X 1 2)+(54268375927/33225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (14139/100000 : ℝ)) (c := (4428620883929000269/4430000000000000000 : ℝ)) (alpha := (54268375927/33225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527579097/2500000000 : ℝ)*X 0 0+(67387191/125000000 : ℝ)*X 0 1+(5267329093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672119171/5000000000 : ℝ)*X 1 0+(-2173005707/10000000000 : ℝ)*X 1 1+(82302017/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336059587/2500000000 : ℝ)*X 2 0+(5267329087/10000000000 : ℝ)*X 2 1+(-21730057/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347892719/10000000000 : ℝ)*X 0 0+(4223735777/10000000000 : ℝ)*X 0 1+(895115651/2000000000 : ℝ)*X 0 2+(4347892719/10000000000 : ℝ)*X 1 0+(4223735777/10000000000 : ℝ)*X 1 1+(895115651/2000000000 : ℝ)*X 1 2+(4347892719/10000000000 : ℝ)*X 2 0+(4223735777/10000000000 : ℝ)*X 2 1+(895115651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2110321237/10000000000 : ℝ)*X 0 0+(5267641551/10000000000 : ℝ)*X 0 1+(5390661531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062529113/2000000000 : ℝ)*X 1 0+(-2049673379/10000000000 : ℝ)*X 1 1+(2695330437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312645937/10000000000 : ℝ)*X 2 0+(5390660421/10000000000 : ℝ)*X 2 1+(-512418373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((271743867/625000000 : ℝ)*X 0 0+(894988253/2000000000 : ℝ)*X 0 1+(21121877/50000000 : ℝ)*X 0 2+(271743867/625000000 : ℝ)*X 1 0+(894988253/2000000000 : ℝ)*X 1 1+(21121877/50000000 : ℝ)*X 1 2+(271743867/625000000 : ℝ)*X 2 0+(894988253/2000000000 : ℝ)*X 2 1+(21121877/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-9580211/2000000000 : ℝ)*X 0 0+(5910040477/10000000000 : ℝ)*X 0 1+(5910078019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((19222757/125000000 : ℝ)*X 0 0+(2861960939/5000000000 : ℝ)*X 0 1+(5336055311/10000000000 : ℝ)*X 0 2+(19222757/125000000 : ℝ)*X 1 0+(2861960939/5000000000 : ℝ)*X 1 1+(5336055311/10000000000 : ℝ)*X 1 2+(19222757/125000000 : ℝ)*X 2 0+(2861960939/5000000000 : ℝ)*X 2 1+(5336055311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s6_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1558426728633646992504894383/221500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45862371/12500000000000 : ℝ)*(lower2) + (141997947/100000000000000 : ℝ)*(lower3) + (366503571/100000000000000 : ℝ)*(lower4) + (97149569/100000000000000 : ℝ)*(lower5) + (6029165424594169/100000000000000 : ℝ)*(major0) + (6029165424594169/100000000000000 : ℝ)*(major1) + (6029165424594169/100000000000000 : ℝ)*(major2) + (8087590420867319/100000000000000 : ℝ)*(sp0) + (4043793846189733/50000000000000 : ℝ)*(sp1) + (1617517256296143/20000000000000 : ℝ)*(sp2) + (3970736889993953/100000000000000 : ℝ)*(sp3) + (150807217/2500000000000 : ℝ)*(sp5) + (7443187431/100000000000000 : ℝ)*(sp6) + (3303800827/100000000000000 : ℝ)*(sp8) + (3970736889993953/100000000000000 : ℝ)*(f.failure) + (4043796862334073/50000000000000 : ℝ)*(f.sum) + (208998687685451/3322500000000000000000000000 : ℝ)*base65 + (10887381021604305617/1329000000000000000000000000000000 : ℝ)*base68 + (3597045354439305617/1329000000000000000000000000000000 : ℝ)*base70 + (136500164267224694383/1329000000000000000000000000000000 : ℝ)*base71 + (8032594938203/6645000000000000000000000000 : ℝ)*base74 + (9812087205331305617/1329000000000000000000000000000000 : ℝ)*base76 + (5629324882030305617/1329000000000000000000000000000000 : ℝ)*base78 + (381905235442694383/1329000000000000000000000000000000 : ℝ)*base79 + (14357592762983/6645000000000000000000000000 : ℝ)*base82 + (6256261/10000000000000000000000 : ℝ)*base90 + (6256261/10000000000000000000000 : ℝ)*base92 + (6256261/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (547256129720404330265787829/221500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75598183/25000000000000 : ℝ)*(lower2) + (316189783/100000000000000 : ℝ)*(lower3) + (796735717/100000000000000 : ℝ)*(lower5) + (6059911376314751/100000000000000 : ℝ)*(major0) + (6059911376314751/100000000000000 : ℝ)*(major1) + (6059911376314751/100000000000000 : ℝ)*(major2) + (19913550651/50000000000000 : ℝ)*(sp0) + (2340360729/100000000000000 : ℝ)*(sp3) + (1625758354334651/20000000000000 : ℝ)*(sp4) + (4064418430441139/50000000000000 : ℝ)*(sp5) + (4064418430441139/50000000000000 : ℝ)*(sp6) + (49887270494759/1250000000000 : ℝ)*(sp7) + (5262107721/100000000000000 : ℝ)*(sp8) + (365889937/20000000000000 : ℝ)*(sp9) + (124718306543473/3125000000000 : ℝ)*(f.failure) + (4064418430441139/50000000000000 : ℝ)*(f.sum) + (27172203657083/6645000000000000000000000000 : ℝ)*base65 + (5199103689188804057/1329000000000000000000000000000000 : ℝ)*base67 + (18958501870913804057/1329000000000000000000000000000000 : ℝ)*base69 + (13744727831924804057/1329000000000000000000000000000000 : ℝ)*base71 + (3628560638437/6645000000000000000000000000 : ℝ)*base74 + (15596831214635804057/1329000000000000000000000000000000 : ℝ)*base75 + (24046860176060804057/1329000000000000000000000000000000 : ℝ)*base77 + (21493357287764804057/1329000000000000000000000000000000 : ℝ)*base79 + (31539483656689/3322500000000000000000000000 : ℝ)*base81 + (1336499/312500000000000000000 : ℝ)*base89 + (1336499/312500000000000000000 : ℝ)*base91 + (1336499/312500000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1263_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (23/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1263_s7_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055166041/5000000000 : ℝ)*x 0 + (5390794813/10000000000 : ℝ)*x 1 + (1053499837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055166041/5000000000 : ℝ)^1057 ≤ (6417752791857/50000000000000 : ℝ)^801 := by
    have hnat : (1055166041 : ℕ)^1057*50000000000000^801 ≤ 6417752791857^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055166041 5000000000 6417752791857 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390794813/10000000000 : ℝ)^1057 ≤ (8849503369211/20000000000000 : ℝ)^801 := by
    have hnat : (5390794813 : ℕ)^1057*20000000000000^801 ≤ 8849503369211^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390794813 10000000000 8849503369211 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053499837/2000000000 : ℝ)^1057 ≤ (8583395509539/20000000000000 : ℝ)^801 := by
    have hnat : (1053499837 : ℕ)^1057*20000000000000^801 ≤ 8583395509539^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053499837 2000000000 8583395509539 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055166041/5000000000 : ℝ), (5390794813/10000000000 : ℝ), (1053499837/2000000000 : ℝ)] ![(6417752791857/50000000000000 : ℝ), (8849503369211/20000000000000 : ℝ), (8583395509539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055166041/5000000000 : ℝ)|^1057 ≤ (6417752791857/50000000000000 : ℝ)^801
        have hw : |(-1055166041/5000000000 : ℝ)|=(1055166041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390794813/10000000000 : ℝ)|^1057 ≤ (8849503369211/20000000000000 : ℝ)^801
        have hw : |(5390794813/10000000000 : ℝ)|=(5390794813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053499837/2000000000 : ℝ)|^1057 ≤ (8583395509539/20000000000000 : ℝ)^801
        have hw : |(1053499837/2000000000 : ℝ)|=(1053499837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672096213/5000000000 : ℝ)*x 0 + (-2172841181/10000000000 : ℝ)*x 1 + (5267499191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672096213/5000000000 : ℝ)^1057 ≤ (43743453422393/100000000000000 : ℝ)^801 := by
    have hnat : (2672096213 : ℕ)^1057*100000000000000^801 ≤ 43743453422393^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672096213 5000000000 43743453422393 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172841181/10000000000 : ℝ)^1057 ≤ (13339568951001/100000000000000 : ℝ)^801 := by
    have hnat : (2172841181 : ℕ)^1057*100000000000000^801 ≤ 13339568951001^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172841181 10000000000 13339568951001 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267499191/10000000000 : ℝ)^1057 ≤ (10729244403051/25000000000000 : ℝ)^801 := by
    have hnat : (5267499191 : ℕ)^1057*25000000000000^801 ≤ 10729244403051^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267499191 10000000000 10729244403051 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672096213/5000000000 : ℝ), (-2172841181/10000000000 : ℝ), (5267499191/10000000000 : ℝ)] ![(43743453422393/100000000000000 : ℝ), (13339568951001/100000000000000 : ℝ), (10729244403051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672096213/5000000000 : ℝ)|^1057 ≤ (43743453422393/100000000000000 : ℝ)^801
        have hw : |(2672096213/5000000000 : ℝ)|=(2672096213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172841181/10000000000 : ℝ)|^1057 ≤ (13339568951001/100000000000000 : ℝ)^801
        have hw : |(-2172841181/10000000000 : ℝ)|=(2172841181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267499191/10000000000 : ℝ)|^1057 ≤ (10729244403051/25000000000000 : ℝ)^801
        have hw : |(5267499191/10000000000 : ℝ)|=(5267499191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344192417/10000000000 : ℝ)*x 0 + (2633749609/5000000000 : ℝ)*x 1 + (-1086420579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344192417/10000000000 : ℝ)^1057 ≤ (21871726662591/50000000000000 : ℝ)^801 := by
    have hnat : (5344192417 : ℕ)^1057*50000000000000^801 ≤ 21871726662591^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344192417 10000000000 21871726662591 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633749609/5000000000 : ℝ)^1057 ≤ (42916977902493/100000000000000 : ℝ)^801 := by
    have hnat : (2633749609 : ℕ)^1057*100000000000000^801 ≤ 42916977902493^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633749609 5000000000 42916977902493 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086420579/5000000000 : ℝ)^1057 ≤ (1333956876467/10000000000000 : ℝ)^801 := by
    have hnat : (1086420579 : ℕ)^1057*10000000000000^801 ≤ 1333956876467^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086420579 5000000000 1333956876467 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344192417/10000000000 : ℝ), (2633749609/5000000000 : ℝ), (-1086420579/5000000000 : ℝ)] ![(21871726662591/50000000000000 : ℝ), (42916977902493/100000000000000 : ℝ), (1333956876467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344192417/10000000000 : ℝ)|^1057 ≤ (21871726662591/50000000000000 : ℝ)^801
        have hw : |(5344192417/10000000000 : ℝ)|=(5344192417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633749609/5000000000 : ℝ)|^1057 ≤ (42916977902493/100000000000000 : ℝ)^801
        have hw : |(2633749609/5000000000 : ℝ)|=(2633749609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086420579/5000000000 : ℝ)|^1057 ≤ (1333956876467/10000000000000 : ℝ)^801
        have hw : |(-1086420579/5000000000 : ℝ)|=(1086420579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4347901591/10000000000 : ℝ)*x 0 + (4224091713/10000000000 : ℝ)*x 1 + (279701253/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347901591/10000000000 : ℝ)^1057 ≤ (33317600713873/100000000000000 : ℝ)^801 := by
    have hnat : (4347901591 : ℕ)^1057*100000000000000^801 ≤ 33317600713873^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347901591 10000000000 33317600713873 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224091713/10000000000 : ℝ)^1057 ≤ (32071371110541/100000000000000 : ℝ)^801 := by
    have hnat : (4224091713 : ℕ)^1057*100000000000000^801 ≤ 32071371110541^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224091713 10000000000 32071371110541 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279701253/625000000 : ℝ)^1057 ≤ (34611028160723/100000000000000 : ℝ)^801 := by
    have hnat : (279701253 : ℕ)^1057*100000000000000^801 ≤ 34611028160723^801*625000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279701253 625000000 34611028160723 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347901591/10000000000 : ℝ), (4224091713/10000000000 : ℝ), (279701253/625000000 : ℝ)] ![(33317600713873/100000000000000 : ℝ), (32071371110541/100000000000000 : ℝ), (34611028160723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347901591/10000000000 : ℝ)|^1057 ≤ (33317600713873/100000000000000 : ℝ)^801
        have hw : |(4347901591/10000000000 : ℝ)|=(4347901591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224091713/10000000000 : ℝ)|^1057 ≤ (32071371110541/100000000000000 : ℝ)^801
        have hw : |(4224091713/10000000000 : ℝ)|=(4224091713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279701253/625000000 : ℝ)|^1057 ≤ (34611028160723/100000000000000 : ℝ)^801
        have hw : |(279701253/625000000 : ℝ)|=(279701253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110337017/10000000000 : ℝ)*x 0 + (526781011/1000000000 : ℝ)*x 1 + (1347620629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110337017/10000000000 : ℝ)^1057 ≤ (641777259627/5000000000000 : ℝ)^801 := by
    have hnat : (2110337017 : ℕ)^1057*5000000000000^801 ≤ 641777259627^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110337017 10000000000 641777259627 5000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526781011/1000000000 : ℝ)^1057 ≤ (42920320474461/100000000000000 : ℝ)^801 := by
    have hnat : (526781011 : ℕ)^1057*100000000000000^801 ≤ 42920320474461^801*1000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526781011 1000000000 42920320474461 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347620629/2500000000 : ℝ)^1057 ≤ (22122067155273/50000000000000 : ℝ)^801 := by
    have hnat : (1347620629 : ℕ)^1057*50000000000000^801 ≤ 22122067155273^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347620629 2500000000 22122067155273 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110337017/10000000000 : ℝ), (526781011/1000000000 : ℝ), (1347620629/2500000000 : ℝ)] ![(641777259627/5000000000000 : ℝ), (42920320474461/100000000000000 : ℝ), (22122067155273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110337017/10000000000 : ℝ)|^1057 ≤ (641777259627/5000000000000 : ℝ)^801
        have hw : |(-2110337017/10000000000 : ℝ)|=(2110337017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526781011/1000000000 : ℝ)|^1057 ≤ (42920320474461/100000000000000 : ℝ)^801
        have hw : |(526781011/1000000000 : ℝ)|=(526781011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347620629/2500000000 : ℝ)|^1057 ≤ (22122067155273/50000000000000 : ℝ)^801
        have hw : |(1347620629/2500000000 : ℝ)|=(1347620629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312688323/10000000000 : ℝ)*x 0 + (-2049858351/10000000000 : ℝ)*x 1 + (1347620629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312688323/10000000000 : ℝ)^1057 ≤ (43403491159719/100000000000000 : ℝ)^801 := by
    have hnat : (5312688323 : ℕ)^1057*100000000000000^801 ≤ 43403491159719^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312688323 10000000000 43403491159719 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049858351/10000000000 : ℝ)^1057 ≤ (12352374517897/100000000000000 : ℝ)^801 := by
    have hnat : (2049858351 : ℕ)^1057*100000000000000^801 ≤ 12352374517897^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049858351 10000000000 12352374517897 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347620629/2500000000 : ℝ)^1057 ≤ (22122067155273/50000000000000 : ℝ)^801 := by
    have hnat : (1347620629 : ℕ)^1057*50000000000000^801 ≤ 22122067155273^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347620629 2500000000 22122067155273 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312688323/10000000000 : ℝ), (-2049858351/10000000000 : ℝ), (1347620629/2500000000 : ℝ)] ![(43403491159719/100000000000000 : ℝ), (12352374517897/100000000000000 : ℝ), (22122067155273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312688323/10000000000 : ℝ)|^1057 ≤ (43403491159719/100000000000000 : ℝ)^801
        have hw : |(5312688323/10000000000 : ℝ)|=(5312688323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049858351/10000000000 : ℝ)|^1057 ≤ (12352374517897/100000000000000 : ℝ)^801
        have hw : |(-2049858351/10000000000 : ℝ)|=(2049858351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347620629/2500000000 : ℝ)|^1057 ≤ (22122067155273/50000000000000 : ℝ)^801
        have hw : |(1347620629/2500000000 : ℝ)|=(1347620629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656344251/5000000000 : ℝ)*x 0 + (2695241267/5000000000 : ℝ)*x 1 + (-512464521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656344251/5000000000 : ℝ)^1057 ≤ (4340349308949/10000000000000 : ℝ)^801 := by
    have hnat : (2656344251 : ℕ)^1057*10000000000000^801 ≤ 4340349308949^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656344251 5000000000 4340349308949 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695241267/5000000000 : ℝ)^1057 ≤ (1382629203297/3125000000000 : ℝ)^801 := by
    have hnat : (2695241267 : ℕ)^1057*3125000000000^801 ≤ 1382629203297^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695241267 5000000000 1382629203297 3125000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512464521/2500000000 : ℝ)^1057 ≤ (12352372394749/100000000000000 : ℝ)^801 := by
    have hnat : (512464521 : ℕ)^1057*100000000000000^801 ≤ 12352372394749^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512464521 2500000000 12352372394749 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656344251/5000000000 : ℝ), (2695241267/5000000000 : ℝ), (-512464521/2500000000 : ℝ)] ![(4340349308949/10000000000000 : ℝ), (1382629203297/3125000000000 : ℝ), (12352372394749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656344251/5000000000 : ℝ)|^1057 ≤ (4340349308949/10000000000000 : ℝ)^801
        have hw : |(2656344251/5000000000 : ℝ)|=(2656344251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695241267/5000000000 : ℝ)|^1057 ≤ (1382629203297/3125000000000 : ℝ)^801
        have hw : |(2695241267/5000000000 : ℝ)|=(2695241267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512464521/2500000000 : ℝ)|^1057 ≤ (12352372394749/100000000000000 : ℝ)^801
        have hw : |(-512464521/2500000000 : ℝ)|=(512464521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s7_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (543488893/1250000000 : ℝ)*x 0 + (4474586633/10000000000 : ℝ)*x 1 + (528090907/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543488893/1250000000 : ℝ)^1057 ≤ (6663539462743/20000000000000 : ℝ)^801 := by
    have hnat : (543488893 : ℕ)^1057*20000000000000^801 ≤ 6663539462743^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543488893 1250000000 6663539462743 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474586633/10000000000 : ℝ)^1057 ≤ (34604563866757/100000000000000 : ℝ)^801 := by
    have hnat : (4474586633 : ℕ)^1057*100000000000000^801 ≤ 34604563866757^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474586633 10000000000 34604563866757 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528090907/1250000000 : ℝ)^1057 ≤ (16038869401209/50000000000000 : ℝ)^801 := by
    have hnat : (528090907 : ℕ)^1057*50000000000000^801 ≤ 16038869401209^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528090907 1250000000 16038869401209 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543488893/1250000000 : ℝ), (4474586633/10000000000 : ℝ), (528090907/1250000000 : ℝ)] ![(6663539462743/20000000000000 : ℝ), (34604563866757/100000000000000 : ℝ), (16038869401209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543488893/1250000000 : ℝ)|^1057 ≤ (6663539462743/20000000000000 : ℝ)^801
        have hw : |(543488893/1250000000 : ℝ)|=(543488893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474586633/10000000000 : ℝ)|^1057 ≤ (34604563866757/100000000000000 : ℝ)^801
        have hw : |(4474586633/10000000000 : ℝ)|=(4474586633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528090907/1250000000 : ℝ)|^1057 ≤ (16038869401209/50000000000000 : ℝ)^801
        have hw : |(528090907/1250000000 : ℝ)|=(528090907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/200 : ℝ)*pair X i i ≤ pair X i h) :
    (11503/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (23/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (23/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (23/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (23/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (23/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (23/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (23/200 : ℝ) ^ (8455/2048 : ℝ) ≤ (6624270987314133/50000000000000000000 : ℝ) := by
    have hpowers : (23/200 : ℝ)^8455 ≤ (6624270987314133/50000000000000000000 : ℝ)^2048 := by
      have hnat : (23 : ℕ)^8455*50000000000000000000^2048 ≤ 6624270987314133^2048*200^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23 200 6624270987314133 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23/200 : ℝ)) (X := (6624270987314133/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (15452733186544721/50000000000000000000 : ℝ) := by
    have hpowers : (14119/100000 : ℝ)^8455 ≤ (15452733186544721/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14119 : ℕ)^8455*50000000000000000000^2048 ≤ 15452733186544721^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 100000 15452733186544721 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/100000 : ℝ)) (X := (15452733186544721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006624270987314133/25000000000000000000 : ℝ) ≤ (10000641757312503/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25006624270987314133/25000000000000000000 : ℝ)^2048 ≤ (10000641757312503/10000000000000000 : ℝ)^8455 := by
      have hnat : (25006624270987314133 : ℕ)^2048*10000000000000000^8455 ≤ 10000641757312503^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006624270987314133 25000000000000000000 10000641757312503 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641757312503/10000000000000000 : ℝ)) (X := (25006624270987314133/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011038502086929427/25000000000000000000 : ℝ) ≤ (250026733378183/250000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25011038502086929427/25000000000000000000 : ℝ)^2048 ≤ (250026733378183/250000000000000 : ℝ)^8455 := by
      have hnat : (25011038502086929427 : ℕ)^2048*250000000000000^8455 ≤ 250026733378183^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011038502086929427 25000000000000000000 250026733378183 250000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250026733378183/250000000000000 : ℝ)) (X := (25011038502086929427/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015452733186544721/25000000000000000000 : ℝ) ≤ (10001496912942137/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25015452733186544721/25000000000000000000 : ℝ)^2048 ≤ (10001496912942137/10000000000000000 : ℝ)^8455 := by
      have hnat : (25015452733186544721 : ℕ)^2048*10000000000000000^8455 ≤ 10001496912942137^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015452733186544721 25000000000000000000 10001496912942137 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001496912942137/10000000000000000 : ℝ)) (X := (25015452733186544721/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6624270987314133/50000000000000000000 : ℝ) ≤ ((26181846472660654357/26190000000000000000 : ℝ)+2*(427577814817/261900000000000 : ℝ)*(23/200 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (26181846472660654357/26190000000000000000 : ℝ)+2*(427577814817/261900000000000 : ℝ)*(23/200 : ℝ)=(10000641757312503/10000000000000000 : ℝ) by norm_num, show 1+2*(6624270987314133/50000000000000000000 : ℝ)=(25006624270987314133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15452733186544721/50000000000000000000 : ℝ)+(6624270987314133/50000000000000000000 : ℝ) ≤ ((26181846472660654357/26190000000000000000 : ℝ)+(427577814817/261900000000000 : ℝ)*((14119/100000 : ℝ)+(23/200 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (26181846472660654357/26190000000000000000 : ℝ)+(427577814817/261900000000000 : ℝ)*((14119/100000 : ℝ)+(23/200 : ℝ))=(250026733378183/250000000000000 : ℝ) by norm_num, show 1+(15452733186544721/50000000000000000000 : ℝ)+(6624270987314133/50000000000000000000 : ℝ)=(25011038502086929427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15452733186544721/50000000000000000000 : ℝ) ≤ ((26181846472660654357/26190000000000000000 : ℝ)+2*(427577814817/261900000000000 : ℝ)*(14119/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (26181846472660654357/26190000000000000000 : ℝ)+2*(427577814817/261900000000000 : ℝ)*(14119/100000 : ℝ)=(10001496912942137/10000000000000000 : ℝ) by norm_num, show 1+2*(15452733186544721/50000000000000000000 : ℝ)=(25015452733186544721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26181846472660654357/26190000000000000000 : ℝ)*(X 1 0+X 2 0)+(427577814817/261900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (23/200 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (26181846472660654357/26190000000000000000 : ℝ)) (alpha := (427577814817/261900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26181846472660654357/26190000000000000000 : ℝ)*(X 0 1+X 2 1)+(427577814817/261900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (23/200 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (26181846472660654357/26190000000000000000 : ℝ)) (alpha := (427577814817/261900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26181846472660654357/26190000000000000000 : ℝ)*(X 0 2+X 1 2)+(427577814817/261900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (23/200 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (26181846472660654357/26190000000000000000 : ℝ)) (alpha := (427577814817/261900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1055166041/5000000000 : ℝ)*X 0 0+(5390794813/10000000000 : ℝ)*X 0 1+(1053499837/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672096213/5000000000 : ℝ)*X 1 0+(-2172841181/10000000000 : ℝ)*X 1 1+(5267499191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344192417/10000000000 : ℝ)*X 2 0+(2633749609/5000000000 : ℝ)*X 2 1+(-1086420579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347901591/10000000000 : ℝ)*X 0 0+(4224091713/10000000000 : ℝ)*X 0 1+(279701253/625000000 : ℝ)*X 0 2+(4347901591/10000000000 : ℝ)*X 1 0+(4224091713/10000000000 : ℝ)*X 1 1+(279701253/625000000 : ℝ)*X 1 2+(4347901591/10000000000 : ℝ)*X 2 0+(4224091713/10000000000 : ℝ)*X 2 1+(279701253/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2110337017/10000000000 : ℝ)*X 0 0+(526781011/1000000000 : ℝ)*X 0 1+(1347620629/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312688323/10000000000 : ℝ)*X 1 0+(-2049858351/10000000000 : ℝ)*X 1 1+(1347620629/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656344251/5000000000 : ℝ)*X 2 0+(2695241267/5000000000 : ℝ)*X 2 1+(-512464521/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543488893/1250000000 : ℝ)*X 0 0+(4474586633/10000000000 : ℝ)*X 0 1+(528090907/1250000000 : ℝ)*X 0 2+(543488893/1250000000 : ℝ)*X 1 0+(4474586633/10000000000 : ℝ)*X 1 1+(528090907/1250000000 : ℝ)*X 1 2+(543488893/1250000000 : ℝ)*X 2 0+(4474586633/10000000000 : ℝ)*X 2 1+(528090907/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (767065159122095461937/72750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1067750501/50000000000000 : ℝ)*(base19) + (396935687/20000000000000 : ℝ)*(base23) + (73302843/100000000000000 : ℝ)*(lower2) + (257403483/100000000000000 : ℝ)*(upper3) + (193169529/100000000000000 : ℝ)*(upper5) + (1209279935170353/20000000000000 : ℝ)*(major0) + (1209279935170353/20000000000000 : ℝ)*(major1) + (1209279935170353/20000000000000 : ℝ)*(major2) + (1622130039005981/20000000000000 : ℝ)*(sp0) + (8110709701131749/100000000000000 : ℝ)*(sp1) + (2027677462988579/25000000000000 : ℝ)*(sp2) + (796411276724757/20000000000000 : ℝ)*(sp3) + (30820801423/50000000000000 : ℝ)*(sp4) + (30779985287/100000000000000 : ℝ)*(sp7) + (3982087163609073/100000000000000 : ℝ)*(f.failure) + (8110711836632751/100000000000000 : ℝ)*(f.sum) + (460372563329/218250000000000000000000000 : ℝ)*base66 + (1107406688534326007/174600000000000000000000000000000 : ℝ)*base67 + (947372883499126007/174600000000000000000000000000000 : ℝ)*base69 + (671661702211273993/174600000000000000000000000000000 : ℝ)*base72 + (44158332739/218250000000000000000000000 : ℝ)*base73 + (1571222879811673993/174600000000000000000000000000000 : ℝ)*base76 + (944681748882073993/174600000000000000000000000000000 : ℝ)*base78 + (1756173310134526007/174600000000000000000000000000000 : ℝ)*base79 + (645085839983/174600000000000000000000000 : ℝ)*base81 + (90784299/10000000000000000000000 : ℝ)*base89 + (90784299/10000000000000000000000 : ℝ)*base91 + (90784299/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1370588727982429149162507/121250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149698171/10000000000000 : ℝ)*(base19) + (2181331197/100000000000000 : ℝ)*(base23) + (120908497/100000000000000 : ℝ)*(upper2) + (460334781/100000000000000 : ℝ)*(upper3) + (362089941/100000000000000 : ℝ)*(upper5) + (30385107818441/500000000000 : ℝ)*(major0) + (30385107818441/500000000000 : ℝ)*(major1) + (30385107818441/500000000000 : ℝ)*(major2) + (18677455253/100000000000000 : ℝ)*(sp1) + (49387427081/100000000000000 : ℝ)*(sp2) + (4075894187289831/50000000000000 : ℝ)*(sp4) + (8151768200142699/100000000000000 : ℝ)*(sp5) + (8151736805821383/100000000000000 : ℝ)*(sp6) + (4002254376002581/100000000000000 : ℝ)*(sp7) + (4002254376002581/100000000000000 : ℝ)*(f.failure) + (4075894187289831/50000000000000 : ℝ)*(f.sum) + (376423742791/261900000000000000000000000 : ℝ)*base66 + (88173818714037563/13095000000000000000000000000000 : ℝ)*base68 + (118105761531137437/13095000000000000000000000000000 : ℝ)*base69 + (31536773873492437/13095000000000000000000000000000 : ℝ)*base71 + (406828535291/2619000000000000000000000000 : ℝ)*base73 + (40576009801712437/13095000000000000000000000000000 : ℝ)*base75 + (89115940808132437/13095000000000000000000000000000 : ℝ)*base77 + (12647671991762437/13095000000000000000000000000000 : ℝ)*base79 + (3434037748637/1309500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13055497/10000000000000000000000 : ℝ)*base90 + (13055497/10000000000000000000000 : ℝ)*base92 + (13055497/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1263_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1263_s8_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-527583501/2500000000 : ℝ)*x 0 + (2695383723/5000000000 : ℝ)*x 1 + (131688133/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527583501/2500000000 : ℝ)^1057 ≤ (12835521009883/100000000000000 : ℝ)^801 := by
    have hnat : (527583501 : ℕ)^1057*100000000000000^801 ≤ 12835521009883^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527583501 2500000000 12835521009883 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695383723/5000000000 : ℝ)^1057 ≤ (22123610213741/50000000000000 : ℝ)^801 := by
    have hnat : (2695383723 : ℕ)^1057*50000000000000^801 ≤ 22123610213741^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695383723 5000000000 22123610213741 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131688133/250000000 : ℝ)^1057 ≤ (21458629268559/50000000000000 : ℝ)^801 := by
    have hnat : (131688133 : ℕ)^1057*50000000000000^801 ≤ 21458629268559^801*250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131688133 250000000 21458629268559 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527583501/2500000000 : ℝ), (2695383723/5000000000 : ℝ), (131688133/250000000 : ℝ)] ![(12835521009883/100000000000000 : ℝ), (22123610213741/50000000000000 : ℝ), (21458629268559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527583501/2500000000 : ℝ)|^1057 ≤ (12835521009883/100000000000000 : ℝ)^801
        have hw : |(-527583501/2500000000 : ℝ)|=(527583501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695383723/5000000000 : ℝ)|^1057 ≤ (22123610213741/50000000000000 : ℝ)^801
        have hw : |(2695383723/5000000000 : ℝ)|=(2695383723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131688133/250000000 : ℝ)|^1057 ≤ (21458629268559/50000000000000 : ℝ)^801
        have hw : |(131688133/250000000 : ℝ)|=(131688133/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267209279/500000000 : ℝ)*x 0 + (-2172815669/10000000000 : ℝ)*x 1 + (5267525293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267209279/500000000 : ℝ)^1057 ≤ (10935844869287/25000000000000 : ℝ)^801 := by
    have hnat : (267209279 : ℕ)^1057*25000000000000^801 ≤ 10935844869287^801*500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267209279 500000000 10935844869287 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172815669/10000000000 : ℝ)^1057 ≤ (3334840567569/25000000000000 : ℝ)^801 := by
    have hnat : (2172815669 : ℕ)^1057*25000000000000^801 ≤ 3334840567569^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172815669 10000000000 3334840567569 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267525293/10000000000 : ℝ)^1057 ≤ (10729314561707/25000000000000 : ℝ)^801 := by
    have hnat : (5267525293 : ℕ)^1057*25000000000000^801 ≤ 10729314561707^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267525293 10000000000 10729314561707 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267209279/500000000 : ℝ), (-2172815669/10000000000 : ℝ), (5267525293/10000000000 : ℝ)] ![(10935844869287/25000000000000 : ℝ), (3334840567569/25000000000000 : ℝ), (10729314561707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267209279/500000000 : ℝ)|^1057 ≤ (10935844869287/25000000000000 : ℝ)^801
        have hw : |(267209279/500000000 : ℝ)|=(267209279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172815669/10000000000 : ℝ)|^1057 ≤ (3334840567569/25000000000000 : ℝ)^801
        have hw : |(-2172815669/10000000000 : ℝ)|=(2172815669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267525293/10000000000 : ℝ)|^1057 ≤ (10729314561707/25000000000000 : ℝ)^801
        have hw : |(5267525293/10000000000 : ℝ)|=(5267525293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167005799/312500000 : ℝ)*x 0 + (2633762661/5000000000 : ℝ)*x 1 + (-2172815647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167005799/312500000 : ℝ)^1057 ≤ (43743379347533/100000000000000 : ℝ)^801 := by
    have hnat : (167005799 : ℕ)^1057*100000000000000^801 ≤ 43743379347533^801*312500000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167005799 312500000 43743379347533 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633762661/5000000000 : ℝ)^1057 ≤ (42917258558621/100000000000000 : ℝ)^801 := by
    have hnat : (2633762661 : ℕ)^1057*100000000000000^801 ≤ 42917258558621^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633762661 5000000000 42917258558621 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172815647/10000000000 : ℝ)^1057 ≤ (833710130753/6250000000000 : ℝ)^801 := by
    have hnat : (2172815647 : ℕ)^1057*6250000000000^801 ≤ 833710130753^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172815647 10000000000 833710130753 6250000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167005799/312500000 : ℝ), (2633762661/5000000000 : ℝ), (-2172815647/10000000000 : ℝ)] ![(43743379347533/100000000000000 : ℝ), (42917258558621/100000000000000 : ℝ), (833710130753/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167005799/312500000 : ℝ)|^1057 ≤ (43743379347533/100000000000000 : ℝ)^801
        have hw : |(167005799/312500000 : ℝ)|=(167005799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633762661/5000000000 : ℝ)|^1057 ≤ (42917258558621/100000000000000 : ℝ)^801
        have hw : |(2633762661/5000000000 : ℝ)|=(2633762661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172815647/10000000000 : ℝ)|^1057 ≤ (833710130753/6250000000000 : ℝ)^801
        have hw : |(-2172815647/10000000000 : ℝ)|=(2172815647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4347902903/10000000000 : ℝ)*x 0 + (844829189/2000000000 : ℝ)*x 1 + (4475165507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347902903/10000000000 : ℝ)^1057 ≤ (10411754369/31250000000 : ℝ)^801 := by
    have hnat : (4347902903 : ℕ)^1057*31250000000^801 ≤ 10411754369^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347902903 10000000000 10411754369 31250000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844829189/2000000000 : ℝ)^1057 ≤ (32071914464919/100000000000000 : ℝ)^801 := by
    have hnat : (844829189 : ℕ)^1057*100000000000000^801 ≤ 32071914464919^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844829189 2000000000 32071914464919 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475165507/10000000000 : ℝ)^1057 ≤ (17305235766503/50000000000000 : ℝ)^801 := by
    have hnat : (4475165507 : ℕ)^1057*50000000000000^801 ≤ 17305235766503^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475165507 10000000000 17305235766503 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347902903/10000000000 : ℝ), (844829189/2000000000 : ℝ), (4475165507/10000000000 : ℝ)] ![(10411754369/31250000000 : ℝ), (32071914464919/100000000000000 : ℝ), (17305235766503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347902903/10000000000 : ℝ)|^1057 ≤ (10411754369/31250000000 : ℝ)^801
        have hw : |(4347902903/10000000000 : ℝ)|=(4347902903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844829189/2000000000 : ℝ)|^1057 ≤ (32071914464919/100000000000000 : ℝ)^801
        have hw : |(844829189/2000000000 : ℝ)|=(844829189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475165507/10000000000 : ℝ)|^1057 ≤ (17305235766503/50000000000000 : ℝ)^801
        have hw : |(4475165507/10000000000 : ℝ)|=(4475165507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055169241/5000000000 : ℝ)*x 0 + (2633918011/5000000000 : ℝ)*x 1 + (5390455709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055169241/5000000000 : ℝ)^1057 ≤ (12835556950789/100000000000000 : ℝ)^801 := by
    have hnat : (1055169241 : ℕ)^1057*100000000000000^801 ≤ 12835556950789^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055169241 5000000000 12835556950789 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633918011/5000000000 : ℝ)^1057 ≤ (21460299535781/50000000000000 : ℝ)^801 := by
    have hnat : (2633918011 : ℕ)^1057*50000000000000^801 ≤ 21460299535781^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633918011 5000000000 21460299535781 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390455709/10000000000 : ℝ)^1057 ≤ (22121921981419/50000000000000 : ℝ)^801 := by
    have hnat : (5390455709 : ℕ)^1057*50000000000000^801 ≤ 22121921981419^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390455709 10000000000 22121921981419 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055169241/5000000000 : ℝ), (2633918011/5000000000 : ℝ), (5390455709/10000000000 : ℝ)] ![(12835556950789/100000000000000 : ℝ), (21460299535781/50000000000000 : ℝ), (22121921981419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055169241/5000000000 : ℝ)|^1057 ≤ (12835556950789/100000000000000 : ℝ)^801
        have hw : |(-1055169241/5000000000 : ℝ)|=(1055169241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633918011/5000000000 : ℝ)|^1057 ≤ (21460299535781/50000000000000 : ℝ)^801
        have hw : |(2633918011/5000000000 : ℝ)|=(2633918011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390455709/10000000000 : ℝ)|^1057 ≤ (22121921981419/50000000000000 : ℝ)^801
        have hw : |(5390455709/10000000000 : ℝ)|=(5390455709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212507819/400000000 : ℝ)*x 0 + (-256235711/1250000000 : ℝ)*x 1 + (5390455327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212507819/400000000 : ℝ)^1057 ≤ (21701784132169/50000000000000 : ℝ)^801 := by
    have hnat : (212507819 : ℕ)^1057*50000000000000^801 ≤ 21701784132169^801*400000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212507819 400000000 21701784132169 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256235711/1250000000 : ℝ)^1057 ≤ (1235259189853/10000000000000 : ℝ)^801 := by
    have hnat : (256235711 : ℕ)^1057*10000000000000^801 ≤ 1235259189853^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256235711 1250000000 1235259189853 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390455327/10000000000 : ℝ)^1057 ≤ (5530479978173/12500000000000 : ℝ)^801 := by
    have hnat : (5390455327 : ℕ)^1057*12500000000000^801 ≤ 5530479978173^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390455327 10000000000 5530479978173 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212507819/400000000 : ℝ), (-256235711/1250000000 : ℝ), (5390455327/10000000000 : ℝ)] ![(21701784132169/50000000000000 : ℝ), (1235259189853/10000000000000 : ℝ), (5530479978173/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212507819/400000000 : ℝ)|^1057 ≤ (21701784132169/50000000000000 : ℝ)^801
        have hw : |(212507819/400000000 : ℝ)|=(212507819/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256235711/1250000000 : ℝ)|^1057 ≤ (1235259189853/10000000000000 : ℝ)^801
        have hw : |(-256235711/1250000000 : ℝ)|=(256235711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390455327/10000000000 : ℝ)|^1057 ≤ (5530479978173/12500000000000 : ℝ)^801
        have hw : |(5390455327/10000000000 : ℝ)|=(5390455327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312695177/10000000000 : ℝ)*x 0 + (336903487/625000000 : ℝ)*x 1 + (-1024942729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312695177/10000000000 : ℝ)^1057 ≤ (8680713010329/20000000000000 : ℝ)^801 := by
    have hnat : (5312695177 : ℕ)^1057*20000000000000^801 ≤ 8680713010329^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312695177 10000000000 8680713010329 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336903487/625000000 : ℝ)^1057 ≤ (22121922430907/50000000000000 : ℝ)^801 := by
    have hnat : (336903487 : ℕ)^1057*50000000000000^801 ≤ 22121922430907^801*625000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336903487 625000000 22121922430907 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024942729/5000000000 : ℝ)^1057 ≤ (12352590069593/100000000000000 : ℝ)^801 := by
    have hnat : (1024942729 : ℕ)^1057*100000000000000^801 ≤ 12352590069593^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024942729 5000000000 12352590069593 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312695177/10000000000 : ℝ), (336903487/625000000 : ℝ), (-1024942729/5000000000 : ℝ)] ![(8680713010329/20000000000000 : ℝ), (22121922430907/50000000000000 : ℝ), (12352590069593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312695177/10000000000 : ℝ)|^1057 ≤ (8680713010329/20000000000000 : ℝ)^801
        have hw : |(5312695177/10000000000 : ℝ)|=(5312695177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336903487/625000000 : ℝ)|^1057 ≤ (22121922430907/50000000000000 : ℝ)^801
        have hw : |(336903487/625000000 : ℝ)|=(336903487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024942729/5000000000 : ℝ)|^1057 ≤ (12352590069593/100000000000000 : ℝ)^801
        have hw : |(-1024942729/5000000000 : ℝ)|=(1024942729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s8_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2173956161/5000000000 : ℝ)*x 0 + (2237266077/5000000000 : ℝ)*x 1 + (1056195389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173956161/5000000000 : ℝ)^1057 ≤ (8329427306411/25000000000000 : ℝ)^801 := by
    have hnat : (2173956161 : ℕ)^1057*25000000000000^801 ≤ 8329427306411^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173956161 5000000000 8329427306411 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237266077/5000000000 : ℝ)^1057 ≤ (34604007896943/100000000000000 : ℝ)^801 := by
    have hnat : (2237266077 : ℕ)^1057*100000000000000^801 ≤ 34604007896943^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237266077 5000000000 34604007896943 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056195389/2500000000 : ℝ)^1057 ≤ (16039141432127/50000000000000 : ℝ)^801 := by
    have hnat : (1056195389 : ℕ)^1057*50000000000000^801 ≤ 16039141432127^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056195389 2500000000 16039141432127 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173956161/5000000000 : ℝ), (2237266077/5000000000 : ℝ), (1056195389/2500000000 : ℝ)] ![(8329427306411/25000000000000 : ℝ), (34604007896943/100000000000000 : ℝ), (16039141432127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173956161/5000000000 : ℝ)|^1057 ≤ (8329427306411/25000000000000 : ℝ)^801
        have hw : |(2173956161/5000000000 : ℝ)|=(2173956161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237266077/5000000000 : ℝ)|^1057 ≤ (34604007896943/100000000000000 : ℝ)^801
        have hw : |(2237266077/5000000000 : ℝ)|=(2237266077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056195389/2500000000 : ℝ)|^1057 ≤ (16039141432127/50000000000000 : ℝ)^801
        have hw : |(1056195389/2500000000 : ℝ)|=(1056195389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (719/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11503/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (1657852024273067/12500000000000000000 : ℝ) := by
    have hpowers : (11503/100000 : ℝ)^8455 ≤ (1657852024273067/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11503 : ℕ)^8455*12500000000000000000^2048 ≤ 1657852024273067^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11503 100000 1657852024273067 12500000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11503/100000 : ℝ)) (X := (1657852024273067/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (8455/2048 : ℝ) ≤ (30878364960227217/100000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^8455 ≤ (30878364960227217/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3529 : ℕ)^8455*100000000000000000000^2048 ≤ 30878364960227217^2048*25000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 30878364960227217 100000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (30878364960227217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251657852024273067/6250000000000000000 : ℝ) ≤ (10000642448684001/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (6251657852024273067/6250000000000000000 : ℝ)^2048 ≤ (10000642448684001/10000000000000000 : ℝ)^8455 := by
      have hnat : (6251657852024273067 : ℕ)^2048*10000000000000000^8455 ≤ 10000642448684001^8455*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251657852024273067 6250000000000000000 10000642448684001 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000642448684001/10000000000000000 : ℝ)) (X := (6251657852024273067/6250000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044141181154411753/100000000000000000000 : ℝ) ≤ (1000106902452641/1000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (100044141181154411753/100000000000000000000 : ℝ)^2048 ≤ (1000106902452641/1000000000000000 : ℝ)^8455 := by
      have hnat : (100044141181154411753 : ℕ)^2048*1000000000000000^8455 ≤ 1000106902452641^8455*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044141181154411753 100000000000000000000 1000106902452641 1000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000106902452641/1000000000000000 : ℝ)) (X := (100044141181154411753/100000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030878364960227217/50000000000000000000 : ℝ) ≤ (10001495600368819/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (50030878364960227217/50000000000000000000 : ℝ)^2048 ≤ (10001495600368819/10000000000000000 : ℝ)^8455 := by
      have hnat : (50030878364960227217 : ℕ)^2048*10000000000000000^8455 ≤ 10001495600368819^8455*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030878364960227217 50000000000000000000 10001495600368819 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001495600368819/10000000000000000 : ℝ)) (X := (50030878364960227217/50000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1657852024273067/12500000000000000000 : ℝ) ≤ ((26121864914580833159/26130000000000000000 : ℝ)+2*(426575842409/261300000000000 : ℝ)*(11503/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (26121864914580833159/26130000000000000000 : ℝ)+2*(426575842409/261300000000000 : ℝ)*(11503/100000 : ℝ)=(10000642448684001/10000000000000000 : ℝ) by norm_num, show 1+2*(1657852024273067/12500000000000000000 : ℝ)=(6251657852024273067/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30878364960227217/100000000000000000000 : ℝ)+(1657852024273067/12500000000000000000 : ℝ) ≤ ((26121864914580833159/26130000000000000000 : ℝ)+(426575842409/261300000000000 : ℝ)*((3529/25000 : ℝ)+(11503/100000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (26121864914580833159/26130000000000000000 : ℝ)+(426575842409/261300000000000 : ℝ)*((3529/25000 : ℝ)+(11503/100000 : ℝ))=(1000106902452641/1000000000000000 : ℝ) by norm_num, show 1+(30878364960227217/100000000000000000000 : ℝ)+(1657852024273067/12500000000000000000 : ℝ)=(100044141181154411753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30878364960227217/100000000000000000000 : ℝ) ≤ ((26121864914580833159/26130000000000000000 : ℝ)+2*(426575842409/261300000000000 : ℝ)*(3529/25000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (26121864914580833159/26130000000000000000 : ℝ)+2*(426575842409/261300000000000 : ℝ)*(3529/25000 : ℝ)=(10001495600368819/10000000000000000 : ℝ) by norm_num, show 1+2*(30878364960227217/100000000000000000000 : ℝ)=(50030878364960227217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26121864914580833159/26130000000000000000 : ℝ)*(X 1 0+X 2 0)+(426575842409/261300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (26121864914580833159/26130000000000000000 : ℝ)) (alpha := (426575842409/261300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26121864914580833159/26130000000000000000 : ℝ)*(X 0 1+X 2 1)+(426575842409/261300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (26121864914580833159/26130000000000000000 : ℝ)) (alpha := (426575842409/261300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26121864914580833159/26130000000000000000 : ℝ)*(X 0 2+X 1 2)+(426575842409/261300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (26121864914580833159/26130000000000000000 : ℝ)) (alpha := (426575842409/261300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527583501/2500000000 : ℝ)*X 0 0+(2695383723/5000000000 : ℝ)*X 0 1+(131688133/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267209279/500000000 : ℝ)*X 1 0+(-2172815669/10000000000 : ℝ)*X 1 1+(5267525293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167005799/312500000 : ℝ)*X 2 0+(2633762661/5000000000 : ℝ)*X 2 1+(-2172815647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347902903/10000000000 : ℝ)*X 0 0+(844829189/2000000000 : ℝ)*X 0 1+(4475165507/10000000000 : ℝ)*X 0 2+(4347902903/10000000000 : ℝ)*X 1 0+(844829189/2000000000 : ℝ)*X 1 1+(4475165507/10000000000 : ℝ)*X 1 2+(4347902903/10000000000 : ℝ)*X 2 0+(844829189/2000000000 : ℝ)*X 2 1+(4475165507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1055169241/5000000000 : ℝ)*X 0 0+(2633918011/5000000000 : ℝ)*X 0 1+(5390455709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212507819/400000000 : ℝ)*X 1 0+(-256235711/1250000000 : ℝ)*X 1 1+(5390455327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312695177/10000000000 : ℝ)*X 2 0+(336903487/625000000 : ℝ)*X 2 1+(-1024942729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173956161/5000000000 : ℝ)*X 0 0+(2237266077/5000000000 : ℝ)*X 0 1+(1056195389/2500000000 : ℝ)*X 0 2+(2173956161/5000000000 : ℝ)*X 1 0+(2237266077/5000000000 : ℝ)*X 1 1+(1056195389/2500000000 : ℝ)*X 1 2+(2173956161/5000000000 : ℝ)*X 2 0+(2237266077/5000000000 : ℝ)*X 2 1+(1056195389/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6902268163590806647681047/1046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4891763/390625000000 : ℝ)*(base19) + (1147376403/100000000000000 : ℝ)*(base23) + (46331469/100000000000000 : ℝ)*(lower2) + (145894497/100000000000000 : ℝ)*(upper3) + (14491209/12500000000000 : ℝ)*(upper5) + (378061466919279/6250000000000 : ℝ)*(major0) + (378061466919279/6250000000000 : ℝ)*(major1) + (378061466919279/6250000000000 : ℝ)*(major2) + (8114143341893651/100000000000000 : ℝ)*(sp0) + (8114176649073741/100000000000000 : ℝ)*(sp1) + (4057088376994333/50000000000000 : ℝ)*(sp2) + (3983770498567307/100000000000000 : ℝ)*(sp3) + (34559471417/100000000000000 : ℝ)*(sp4) + (18321710833/100000000000000 : ℝ)*(sp7) + (199189441013907/5000000000000 : ℝ)*(f.failure) + (8114177901365069/100000000000000 : ℝ)*(f.sum) + (758495320831/335000000000000000000000000 : ℝ)*base66 + (4681420560945901/4187500000000000000000000000000 : ℝ)*base68 + (37796069445383401/4187500000000000000000000000000 : ℝ)*base70 + (69554502765929099/4187500000000000000000000000000 : ℝ)*base71 + (516617147549/83750000000000000000000000 : ℝ)*base74 + (48515726656633401/4187500000000000000000000000000 : ℝ)*base76 + (6925651798820901/4187500000000000000000000000000 : ℝ)*base78 + (909035526195901/4187500000000000000000000000000 : ℝ)*base80 + (639912036241/335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1365441/500000000000000000000 : ℝ)*base89 + (1365441/500000000000000000000 : ℝ)*base91 + (1365441/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3626851821199000868289/435500000000000000000000000 : ℝ) := by norm_num
    linear_combination (795907697/100000000000000 : ℝ)*(base19) + (186543967/25000000000000 : ℝ)*(base23) + (5666119/4000000000000 : ℝ)*(lower1) + (4448499/2500000000000 : ℝ)*(lower4) + (123023067/50000000000000 : ℝ)*(upper5) + (303982083861641/5000000000000 : ℝ)*(major0) + (303982083861641/5000000000000 : ℝ)*(major1) + (303982083861641/5000000000000 : ℝ)*(major2) + (1404182463/20000000000000 : ℝ)*(sp0) + (12278998107/100000000000000 : ℝ)*(sp2) + (8155296104223657/100000000000000 : ℝ)*(sp4) + (2038825582307069/25000000000000 : ℝ)*(sp5) + (2038822524990499/25000000000000 : ℝ)*(sp6) + (2001989975864529/50000000000000 : ℝ)*(sp7) + (2001989975864529/50000000000000 : ℝ)*(f.failure) + (8155303125135973/100000000000000 : ℝ)*(f.sum) + (2000545381817/261300000000000000000000000 : ℝ)*base66 + (140212412728453919/130650000000000000000000000000000 : ℝ)*base67 + (936749274638203919/130650000000000000000000000000000 : ℝ)*base69 + (153044956156546081/130650000000000000000000000000000 : ℝ)*base72 + (455724918853/81656250000000000000000000 : ℝ)*base74 + (2788396130147146081/130650000000000000000000000000000 : ℝ)*base76 + (524510912724253919/130650000000000000000000000000000 : ℝ)*base77 + (136631846353846081/130650000000000000000000000000000 : ℝ)*base80 + (2463588137987/2613000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/50000000000000 : ℝ)*base88 + (23627573/5000000000000000000000 : ℝ)*base90 + (23627573/5000000000000000000000 : ℝ)*base92 + (23627573/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1263_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (719/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1263_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (719/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1263_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1263_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1263_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (719/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1263_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

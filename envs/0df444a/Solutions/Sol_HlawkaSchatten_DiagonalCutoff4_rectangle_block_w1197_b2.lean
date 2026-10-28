-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1197_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:01.660999+00:00
-- url     : https://prove2.me/submissions/22f01e69-f4a5-42ef-a087-2de4d9617a38

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
theorem support_rectangle_w1197_s6_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140838759/10000000000 : ℝ)*x 0 + (1348070439/2500000000 : ℝ)*x 1 + (5266347067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140838759/10000000000 : ℝ)^4195 ≤ (6507014425869/50000000000000 : ℝ)^3171 := by
    have hnat : (2140838759 : ℕ)^4195*50000000000000^3171 ≤ 6507014425869^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140838759 10000000000 6507014425869 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348070439/2500000000 : ℝ)^4195 ≤ (22086394864971/50000000000000 : ℝ)^3171 := by
    have hnat : (1348070439 : ℕ)^4195*50000000000000^3171 ≤ 22086394864971^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348070439 2500000000 22086394864971 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266347067/10000000000 : ℝ)^4195 ≤ (42813181404627/100000000000000 : ℝ)^3171 := by
    have hnat : (5266347067 : ℕ)^4195*100000000000000^3171 ≤ 42813181404627^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266347067 10000000000 42813181404627 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140838759/10000000000 : ℝ), (1348070439/2500000000 : ℝ), (5266347067/10000000000 : ℝ)] ![(6507014425869/50000000000000 : ℝ), (22086394864971/50000000000000 : ℝ), (42813181404627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140838759/10000000000 : ℝ)|^4195 ≤ (6507014425869/50000000000000 : ℝ)^3171
        have hw : |(-2140838759/10000000000 : ℝ)|=(2140838759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348070439/2500000000 : ℝ)|^4195 ≤ (22086394864971/50000000000000 : ℝ)^3171
        have hw : |(1348070439/2500000000 : ℝ)|=(1348070439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266347067/10000000000 : ℝ)|^4195 ≤ (42813181404627/100000000000000 : ℝ)^3171
        have hw : |(5266347067/10000000000 : ℝ)|=(5266347067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344593453/10000000000 : ℝ)*x 0 + (-551176253/2500000000 : ℝ)*x 1 + (1053269413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344593453/10000000000 : ℝ)^4195 ≤ (5457090056727/12500000000000 : ℝ)^3171 := by
    have hnat : (5344593453 : ℕ)^4195*12500000000000^3171 ≤ 5457090056727^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344593453 10000000000 5457090056727 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551176253/2500000000 : ℝ)^4195 ≤ (21140778357/156250000000 : ℝ)^3171 := by
    have hnat : (551176253 : ℕ)^4195*156250000000^3171 ≤ 21140778357^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551176253 2500000000 21140778357 156250000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053269413/2000000000 : ℝ)^4195 ≤ (42813181383117/100000000000000 : ℝ)^3171 := by
    have hnat : (1053269413 : ℕ)^4195*100000000000000^3171 ≤ 42813181383117^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053269413 2000000000 42813181383117 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344593453/10000000000 : ℝ), (-551176253/2500000000 : ℝ), (1053269413/2000000000 : ℝ)] ![(5457090056727/12500000000000 : ℝ), (21140778357/156250000000 : ℝ), (42813181383117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344593453/10000000000 : ℝ)|^4195 ≤ (5457090056727/12500000000000 : ℝ)^3171
        have hw : |(5344593453/10000000000 : ℝ)|=(5344593453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551176253/2500000000 : ℝ)|^4195 ≤ (21140778357/156250000000 : ℝ)^3171
        have hw : |(-551176253/2500000000 : ℝ)|=(551176253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053269413/2000000000 : ℝ)|^4195 ≤ (42813181383117/100000000000000 : ℝ)^3171
        have hw : |(1053269413/2000000000 : ℝ)|=(1053269413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344593451/10000000000 : ℝ)*x 0 + (2633173533/5000000000 : ℝ)*x 1 + (-551176253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344593451/10000000000 : ℝ)^4195 ≤ (10914180108051/25000000000000 : ℝ)^3171 := by
    have hnat : (5344593451 : ℕ)^4195*25000000000000^3171 ≤ 10914180108051^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344593451 10000000000 10914180108051 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633173533/5000000000 : ℝ)^4195 ≤ (2675823837117/6250000000000 : ℝ)^3171 := by
    have hnat : (2633173533 : ℕ)^4195*6250000000000^3171 ≤ 2675823837117^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633173533 5000000000 2675823837117 6250000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551176253/2500000000 : ℝ)^4195 ≤ (21140778357/156250000000 : ℝ)^3171 := by
    have hnat : (551176253 : ℕ)^4195*156250000000^3171 ≤ 21140778357^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551176253 2500000000 21140778357 156250000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344593451/10000000000 : ℝ), (2633173533/5000000000 : ℝ), (-551176253/2500000000 : ℝ)] ![(10914180108051/25000000000000 : ℝ), (2675823837117/6250000000000 : ℝ), (21140778357/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344593451/10000000000 : ℝ)|^4195 ≤ (10914180108051/25000000000000 : ℝ)^3171
        have hw : |(5344593451/10000000000 : ℝ)|=(5344593451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633173533/5000000000 : ℝ)|^4195 ≤ (2675823837117/6250000000000 : ℝ)^3171
        have hw : |(2633173533/5000000000 : ℝ)|=(2633173533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-551176253/2500000000 : ℝ)|^4195 ≤ (21140778357/156250000000 : ℝ)^3171
        have hw : |(-551176253/2500000000 : ℝ)|=(551176253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356969607/10000000000 : ℝ)*x 0 + (1058038131/2500000000 : ℝ)*x 1 + (1121350507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356969607/10000000000 : ℝ)^4195 ≤ (3331713479437/10000000000000 : ℝ)^3171 := by
    have hnat : (4356969607 : ℕ)^4195*10000000000000^3171 ≤ 3331713479437^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356969607 10000000000 3331713479437 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058038131/2500000000 : ℝ)^4195 ≤ (16030167430611/50000000000000 : ℝ)^3171 := by
    have hnat : (1058038131 : ℕ)^4195*50000000000000^3171 ≤ 16030167430611^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058038131 2500000000 16030167430611 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121350507/2500000000 : ℝ)^4195 ≤ (34622530323177/100000000000000 : ℝ)^3171 := by
    have hnat : (1121350507 : ℕ)^4195*100000000000000^3171 ≤ 34622530323177^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121350507 2500000000 34622530323177 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356969607/10000000000 : ℝ), (1058038131/2500000000 : ℝ), (1121350507/2500000000 : ℝ)] ![(3331713479437/10000000000000 : ℝ), (16030167430611/50000000000000 : ℝ), (34622530323177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356969607/10000000000 : ℝ)|^4195 ≤ (3331713479437/10000000000000 : ℝ)^3171
        have hw : |(4356969607/10000000000 : ℝ)|=(4356969607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058038131/2500000000 : ℝ)|^4195 ≤ (16030167430611/50000000000000 : ℝ)^3171
        have hw : |(1058038131/2500000000 : ℝ)|=(1058038131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121350507/2500000000 : ℝ)|^4195 ≤ (34622530323177/100000000000000 : ℝ)^3171
        have hw : |(1121350507/2500000000 : ℝ)|=(1121350507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070421789/5000000000 : ℝ)*x 0 + (2633332669/5000000000 : ℝ)*x 1 + (2695981161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070421789/5000000000 : ℝ)^4195 ≤ (6507033803051/50000000000000 : ℝ)^3171 := by
    have hnat : (1070421789 : ℕ)^4195*50000000000000^3171 ≤ 6507033803051^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070421789 5000000000 6507033803051 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633332669/5000000000 : ℝ)^4195 ≤ (42816604390081/100000000000000 : ℝ)^3171 := by
    have hnat : (2633332669 : ℕ)^4195*100000000000000^3171 ≤ 42816604390081^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633332669 5000000000 42816604390081 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695981161/5000000000 : ℝ)^4195 ≤ (22084663992923/50000000000000 : ℝ)^3171 := by
    have hnat : (2695981161 : ℕ)^4195*50000000000000^3171 ≤ 22084663992923^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695981161 5000000000 22084663992923 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070421789/5000000000 : ℝ), (2633332669/5000000000 : ℝ), (2695981161/5000000000 : ℝ)] ![(6507033803051/50000000000000 : ℝ), (42816604390081/100000000000000 : ℝ), (22084663992923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070421789/5000000000 : ℝ)|^4195 ≤ (6507033803051/50000000000000 : ℝ)^3171
        have hw : |(-1070421789/5000000000 : ℝ)|=(1070421789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633332669/5000000000 : ℝ)|^4195 ≤ (42816604390081/100000000000000 : ℝ)^3171
        have hw : |(2633332669/5000000000 : ℝ)|=(2633332669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695981161/5000000000 : ℝ)|^4195 ≤ (22084663992923/50000000000000 : ℝ)^3171
        have hw : |(2695981161/5000000000 : ℝ)|=(2695981161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062512061/2000000000 : ℝ)*x 0 + (-2079089741/10000000000 : ℝ)*x 1 + (2695981173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062512061/2000000000 : ℝ)^4195 ≤ (10827724991749/25000000000000 : ℝ)^3171 := by
    have hnat : (1062512061 : ℕ)^4195*25000000000000^3171 ≤ 10827724991749^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062512061 2000000000 10827724991749 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079089741/10000000000 : ℝ)^4195 ≤ (2503954354779/20000000000000 : ℝ)^3171 := by
    have hnat : (2079089741 : ℕ)^4195*20000000000000^3171 ≤ 2503954354779^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079089741 10000000000 2503954354779 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695981173/5000000000 : ℝ)^4195 ≤ (8833865649187/20000000000000 : ℝ)^3171 := by
    have hnat : (2695981173 : ℕ)^4195*20000000000000^3171 ≤ 8833865649187^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695981173 5000000000 8833865649187 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062512061/2000000000 : ℝ), (-2079089741/10000000000 : ℝ), (2695981173/5000000000 : ℝ)] ![(10827724991749/25000000000000 : ℝ), (2503954354779/20000000000000 : ℝ), (8833865649187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062512061/2000000000 : ℝ)|^4195 ≤ (10827724991749/25000000000000 : ℝ)^3171
        have hw : |(1062512061/2000000000 : ℝ)|=(1062512061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079089741/10000000000 : ℝ)|^4195 ≤ (2503954354779/20000000000000 : ℝ)^3171
        have hw : |(-2079089741/10000000000 : ℝ)|=(2079089741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695981173/5000000000 : ℝ)|^4195 ≤ (8833865649187/20000000000000 : ℝ)^3171
        have hw : |(2695981173/5000000000 : ℝ)|=(2695981173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328140081/2500000000 : ℝ)*x 0 + (5391962329/10000000000 : ℝ)*x 1 + (-1039544869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328140081/2500000000 : ℝ)^4195 ≤ (8662180034383/20000000000000 : ℝ)^3171 := by
    have hnat : (1328140081 : ℕ)^4195*20000000000000^3171 ≤ 8662180034383^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328140081 2500000000 8662180034383 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391962329/10000000000 : ℝ)^4195 ≤ (8833865612341/20000000000000 : ℝ)^3171 := by
    have hnat : (5391962329 : ℕ)^4195*20000000000000^3171 ≤ 8833865612341^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391962329 10000000000 8833865612341 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039544869/5000000000 : ℝ)^4195 ≤ (3129942937499/25000000000000 : ℝ)^3171 := by
    have hnat : (1039544869 : ℕ)^4195*25000000000000^3171 ≤ 3129942937499^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039544869 5000000000 3129942937499 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328140081/2500000000 : ℝ), (5391962329/10000000000 : ℝ), (-1039544869/5000000000 : ℝ)] ![(8662180034383/20000000000000 : ℝ), (8833865612341/20000000000000 : ℝ), (3129942937499/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328140081/2500000000 : ℝ)|^4195 ≤ (8662180034383/20000000000000 : ℝ)^3171
        have hw : |(1328140081/2500000000 : ℝ)|=(1328140081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391962329/10000000000 : ℝ)|^4195 ≤ (8833865612341/20000000000000 : ℝ)^3171
        have hw : |(5391962329/10000000000 : ℝ)|=(5391962329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1039544869/5000000000 : ℝ)|^4195 ≤ (3129942937499/25000000000000 : ℝ)^3171
        have hw : |(-1039544869/5000000000 : ℝ)|=(1039544869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s6_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089244819/2500000000 : ℝ)*x 0 + (896952401/2000000000 : ℝ)*x 1 + (2116397441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089244819/2500000000 : ℝ)^4195 ≤ (16658616304133/50000000000000 : ℝ)^3171 := by
    have hnat : (1089244819 : ℕ)^4195*50000000000000^3171 ≤ 16658616304133^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089244819 2500000000 16658616304133 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896952401/2000000000 : ℝ)^4195 ≤ (34615994824557/100000000000000 : ℝ)^3171 := by
    have hnat : (896952401 : ℕ)^4195*100000000000000^3171 ≤ 34615994824557^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896952401 2000000000 34615994824557 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116397441/5000000000 : ℝ)^4195 ≤ (6413354510797/20000000000000 : ℝ)^3171 := by
    have hnat : (2116397441 : ℕ)^4195*20000000000000^3171 ≤ 6413354510797^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116397441 5000000000 6413354510797 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089244819/2500000000 : ℝ), (896952401/2000000000 : ℝ), (2116397441/5000000000 : ℝ)] ![(16658616304133/50000000000000 : ℝ), (34615994824557/100000000000000 : ℝ), (6413354510797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089244819/2500000000 : ℝ)|^4195 ≤ (16658616304133/50000000000000 : ℝ)^3171
        have hw : |(1089244819/2500000000 : ℝ)|=(1089244819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896952401/2000000000 : ℝ)|^4195 ≤ (34615994824557/100000000000000 : ℝ)^3171
        have hw : |(896952401/2000000000 : ℝ)|=(896952401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116397441/5000000000 : ℝ)|^4195 ≤ (6413354510797/20000000000000 : ℝ)^3171
        have hw : |(2116397441/5000000000 : ℝ)|=(2116397441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5709/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7043/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (8389/2048 : ℝ) ≤ (13671276958207231/100000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^8389 ≤ (13671276958207231/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11393 : ℕ)^8389*100000000000000000000^2048 ≤ 13671276958207231^2048*100000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 13671276958207231 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (13671276958207231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14111/100000 : ℝ) ^ (8389/2048 : ℝ) ≤ (8210430783049423/25000000000000000000 : ℝ) := by
    have hpowers : (14111/100000 : ℝ)^8389 ≤ (8210430783049423/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14111 : ℕ)^8389*25000000000000000000^2048 ≤ 8210430783049423^2048*100000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14111 100000 8210430783049423 25000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14111/100000 : ℝ)) (X := (8210430783049423/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013671276958207231/50000000000000000000 : ℝ) ≤ (5000333721329821/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (50013671276958207231/50000000000000000000 : ℝ)^2048 ≤ (5000333721329821/5000000000000000 : ℝ)^8389 := by
      have hnat : (50013671276958207231 : ℕ)^2048*5000000000000000^8389 ≤ 5000333721329821^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013671276958207231 50000000000000000000 5000333721329821 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333721329821/5000000000000000 : ℝ)) (X := (50013671276958207231/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046513000090404923/100000000000000000000 : ℝ) ≤ (2000227063734213/2000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (100046513000090404923/100000000000000000000 : ℝ)^2048 ≤ (2000227063734213/2000000000000000 : ℝ)^8389 := by
      have hnat : (100046513000090404923 : ℕ)^2048*2000000000000000^8389 ≤ 2000227063734213^8389*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046513000090404923 100000000000000000000 2000227063734213 2000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000227063734213/2000000000000000 : ℝ)) (X := (100046513000090404923/100000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508210430783049423/12500000000000000000 : ℝ) ≤ (1250200399335311/1250000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (12508210430783049423/12500000000000000000 : ℝ)^2048 ≤ (1250200399335311/1250000000000000 : ℝ)^8389 := by
      have hnat : (12508210430783049423 : ℕ)^2048*1250000000000000^8389 ≤ 1250200399335311^8389*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508210430783049423 12500000000000000000 1250200399335311 1250000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250200399335311/1250000000000000 : ℝ)) (X := (12508210430783049423/12500000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13671276958207231/100000000000000000000 : ℝ) ≤ ((13585576543176311239/13590000000000000000 : ℝ)+2*(467876011423/271800000000000 : ℝ)*(11393/100000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (13585576543176311239/13590000000000000000 : ℝ)+2*(467876011423/271800000000000 : ℝ)*(11393/100000 : ℝ)=(5000333721329821/5000000000000000 : ℝ) by norm_num, show 1+2*(13671276958207231/100000000000000000000 : ℝ)=(50013671276958207231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8210430783049423/25000000000000000000 : ℝ)+(13671276958207231/100000000000000000000 : ℝ) ≤ ((13585576543176311239/13590000000000000000 : ℝ)+(467876011423/271800000000000 : ℝ)*((14111/100000 : ℝ)+(11393/100000 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (13585576543176311239/13590000000000000000 : ℝ)+(467876011423/271800000000000 : ℝ)*((14111/100000 : ℝ)+(11393/100000 : ℝ))=(2000227063734213/2000000000000000 : ℝ) by norm_num, show 1+(8210430783049423/25000000000000000000 : ℝ)+(13671276958207231/100000000000000000000 : ℝ)=(100046513000090404923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8210430783049423/25000000000000000000 : ℝ) ≤ ((13585576543176311239/13590000000000000000 : ℝ)+2*(467876011423/271800000000000 : ℝ)*(14111/100000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (13585576543176311239/13590000000000000000 : ℝ)+2*(467876011423/271800000000000 : ℝ)*(14111/100000 : ℝ)=(1250200399335311/1250000000000000 : ℝ) by norm_num, show 1+2*(8210430783049423/25000000000000000000 : ℝ)=(12508210430783049423/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13585576543176311239/13590000000000000000 : ℝ)*(X 1 0+X 2 0)+(467876011423/271800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (13585576543176311239/13590000000000000000 : ℝ)) (alpha := (467876011423/271800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13585576543176311239/13590000000000000000 : ℝ)*(X 0 1+X 2 1)+(467876011423/271800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (13585576543176311239/13590000000000000000 : ℝ)) (alpha := (467876011423/271800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13585576543176311239/13590000000000000000 : ℝ)*(X 0 2+X 1 2)+(467876011423/271800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (13585576543176311239/13590000000000000000 : ℝ)) (alpha := (467876011423/271800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2140838759/10000000000 : ℝ)*X 0 0+(1348070439/2500000000 : ℝ)*X 0 1+(5266347067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344593453/10000000000 : ℝ)*X 1 0+(-551176253/2500000000 : ℝ)*X 1 1+(1053269413/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344593451/10000000000 : ℝ)*X 2 0+(2633173533/5000000000 : ℝ)*X 2 1+(-551176253/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356969607/10000000000 : ℝ)*X 0 0+(1058038131/2500000000 : ℝ)*X 0 1+(1121350507/2500000000 : ℝ)*X 0 2+(4356969607/10000000000 : ℝ)*X 1 0+(1058038131/2500000000 : ℝ)*X 1 1+(1121350507/2500000000 : ℝ)*X 1 2+(4356969607/10000000000 : ℝ)*X 2 0+(1058038131/2500000000 : ℝ)*X 2 1+(1121350507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070421789/5000000000 : ℝ)*X 0 0+(2633332669/5000000000 : ℝ)*X 0 1+(2695981161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062512061/2000000000 : ℝ)*X 1 0+(-2079089741/10000000000 : ℝ)*X 1 1+(2695981173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328140081/2500000000 : ℝ)*X 2 0+(5391962329/10000000000 : ℝ)*X 2 1+(-1039544869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089244819/2500000000 : ℝ)*X 0 0+(896952401/2000000000 : ℝ)*X 0 1+(2116397441/5000000000 : ℝ)*X 0 2+(1089244819/2500000000 : ℝ)*X 1 0+(896952401/2000000000 : ℝ)*X 1 1+(2116397441/5000000000 : ℝ)*X 1 2+(1089244819/2500000000 : ℝ)*X 2 0+(896952401/2000000000 : ℝ)*X 2 1+(2116397441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309864949888073801670967087/45300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1327587519/100000000000000 : ℝ)*(base19) + (307952337/25000000000000 : ℝ)*(base23) + (49601399/100000000000000 : ℝ)*(lower2) + (171176231/100000000000000 : ℝ)*(upper3) + (6331747/6250000000000 : ℝ)*(upper5) + (1188941073404167/20000000000000 : ℝ)*(major0) + (1188941073404167/20000000000000 : ℝ)*(major1) + (1188941073404167/20000000000000 : ℝ)*(major2) + (992582748975973/12500000000000 : ℝ)*(sp0) + (496293558701999/6250000000000 : ℝ)*(sp1) + (1588139407002031/20000000000000 : ℝ)*(sp2) + (3948692636652109/100000000000000 : ℝ)*(sp3) + (36275011719/100000000000000 : ℝ)*(sp4) + (9801280261/50000000000000 : ℝ)*(sp7) + (3948712239212631/100000000000000 : ℝ)*(f.failure) + (7940698266819503/100000000000000 : ℝ)*(f.sum) + (1115421028199/543600000000000000000000000 : ℝ)*base65 + (219614601186660971/90600000000000000000000000000000 : ℝ)*base67 + (726175323456660971/90600000000000000000000000000000 : ℝ)*base69 + (807542018684339029/90600000000000000000000000000000 : ℝ)*base72 + (5738291225483/2718000000000000000000000000 : ℝ)*base74 + (541359847648260971/90600000000000000000000000000000 : ℝ)*base75 + (952220628946139029/90600000000000000000000000000000 : ℝ)*base78 + (406126433524260971/90600000000000000000000000000000 : ℝ)*base79 + (2363543075713/2718000000000000000000000000 : ℝ)*base81 + (49630919/10000000000000000000000 : ℝ)*base90 + (49630919/10000000000000000000000 : ℝ)*base92 + (49630919/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1653989911734976221093/188750000000000000000000000 : ℝ) := by norm_num
    linear_combination (393685491/25000000000000 : ℝ)*(base19) + (1727740461/100000000000000 : ℝ)*(base23) + (179373849/100000000000000 : ℝ)*(upper3) + (54667311/100000000000000 : ℝ)*(lower4) + (173678661/100000000000000 : ℝ)*(upper5) + (93357878945127/1562500000000 : ℝ)*(major0) + (93357878945127/1562500000000 : ℝ)*(major1) + (93357878945127/1562500000000 : ℝ)*(major2) + (9002529943/20000000000000 : ℝ)*(sp1) + (303669587/625000000000 : ℝ)*(sp2) + (498814791260169/6250000000000 : ℝ)*(sp4) + (498811879548189/6250000000000 : ℝ)*(sp5) + (7980986345288323/100000000000000 : ℝ)*(sp6) + (793754310543639/20000000000000 : ℝ)*(sp7) + (793754310543639/20000000000000 : ℝ)*(f.failure) + (498814791260169/6250000000000 : ℝ)*(f.sum) + (2322855247649/566250000000000000000000000 : ℝ)*base66 + (1626304474133101/294921875000000000000000000000 : ℝ)*base68 + (14297903674330433/2359375000000000000000000000000 : ℝ)*base70 + (386956964593173/589843750000000000000000000000 : ℝ)*base71 + (14086953062891/2265000000000000000000000000 : ℝ)*base74 + (15871042257016779/1179687500000000000000000000000 : ℝ)*base76 + (5383378016075817/2359375000000000000000000000000 : ℝ)*base77 + (9159410077482067/2359375000000000000000000000000 : ℝ)*base79 + (44479586077/283125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12466311/2000000000000000000000 : ℝ)*base90 + (12466311/2000000000000000000000 : ℝ)*base92 + (12466311/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1197_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1197_s7_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140856213/10000000000 : ℝ)*x 0 + (269601981/500000000 : ℝ)*x 1 + (5266578003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140856213/10000000000 : ℝ)^4195 ≤ (813385576051/6250000000000 : ℝ)^3171 := by
    have hnat : (2140856213 : ℕ)^4195*6250000000000^3171 ≤ 813385576051^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140856213 10000000000 813385576051 6250000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269601981/500000000 : ℝ)^4195 ≤ (8834033133471/20000000000000 : ℝ)^3171 := by
    have hnat : (269601981 : ℕ)^4195*20000000000000^3171 ≤ 8834033133471^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269601981 500000000 8834033133471 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266578003/10000000000 : ℝ)^4195 ≤ (42815665100761/100000000000000 : ℝ)^3171 := by
    have hnat : (5266578003 : ℕ)^4195*100000000000000^3171 ≤ 42815665100761^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266578003 10000000000 42815665100761 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140856213/10000000000 : ℝ), (269601981/500000000 : ℝ), (5266578003/10000000000 : ℝ)] ![(813385576051/6250000000000 : ℝ), (8834033133471/20000000000000 : ℝ), (42815665100761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140856213/10000000000 : ℝ)|^4195 ≤ (813385576051/6250000000000 : ℝ)^3171
        have hw : |(-2140856213/10000000000 : ℝ)|=(2140856213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269601981/500000000 : ℝ)|^4195 ≤ (8834033133471/20000000000000 : ℝ)^3171
        have hw : |(269601981/500000000 : ℝ)|=(269601981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266578003/10000000000 : ℝ)|^4195 ≤ (42815665100761/100000000000000 : ℝ)^3171
        have hw : |(5266578003/10000000000 : ℝ)|=(5266578003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344533219/10000000000 : ℝ)*x 0 + (-551119737/2500000000 : ℝ)*x 1 + (1053315647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344533219/10000000000 : ℝ)^4195 ≤ (43656069555617/100000000000000 : ℝ)^3171 := by
    have hnat : (5344533219 : ℕ)^4195*100000000000000^3171 ≤ 43656069555617^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344533219 10000000000 43656069555617 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551119737/2500000000 : ℝ)^4195 ≤ (13528262834393/100000000000000 : ℝ)^3171 := by
    have hnat : (551119737 : ℕ)^4195*100000000000000^3171 ≤ 13528262834393^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551119737 2500000000 13528262834393 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053315647/2000000000 : ℝ)^4195 ≤ (21407833797959/50000000000000 : ℝ)^3171 := by
    have hnat : (1053315647 : ℕ)^4195*50000000000000^3171 ≤ 21407833797959^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053315647 2000000000 21407833797959 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344533219/10000000000 : ℝ), (-551119737/2500000000 : ℝ), (1053315647/2000000000 : ℝ)] ![(43656069555617/100000000000000 : ℝ), (13528262834393/100000000000000 : ℝ), (21407833797959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344533219/10000000000 : ℝ)|^4195 ≤ (43656069555617/100000000000000 : ℝ)^3171
        have hw : |(5344533219/10000000000 : ℝ)|=(5344533219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551119737/2500000000 : ℝ)|^4195 ≤ (13528262834393/100000000000000 : ℝ)^3171
        have hw : |(-551119737/2500000000 : ℝ)|=(551119737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053315647/2000000000 : ℝ)|^4195 ≤ (21407833797959/50000000000000 : ℝ)^3171
        have hw : |(1053315647/2000000000 : ℝ)|=(1053315647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068906653/2000000000 : ℝ)*x 0 + (2633289017/5000000000 : ℝ)*x 1 + (-2204479153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068906653/2000000000 : ℝ)^4195 ≤ (436560700527/1000000000000 : ℝ)^3171 := by
    have hnat : (1068906653 : ℕ)^4195*1000000000000^3171 ≤ 436560700527^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068906653 2000000000 436560700527 1000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633289017/5000000000 : ℝ)^4195 ≤ (8563133086833/20000000000000 : ℝ)^3171 := by
    have hnat : (2633289017 : ℕ)^4195*20000000000000^3171 ≤ 8563133086833^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633289017 5000000000 8563133086833 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204479153/10000000000 : ℝ)^4195 ≤ (1352826449867/10000000000000 : ℝ)^3171 := by
    have hnat : (2204479153 : ℕ)^4195*10000000000000^3171 ≤ 1352826449867^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204479153 10000000000 1352826449867 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068906653/2000000000 : ℝ), (2633289017/5000000000 : ℝ), (-2204479153/10000000000 : ℝ)] ![(436560700527/1000000000000 : ℝ), (8563133086833/20000000000000 : ℝ), (1352826449867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068906653/2000000000 : ℝ)|^4195 ≤ (436560700527/1000000000000 : ℝ)^3171
        have hw : |(1068906653/2000000000 : ℝ)|=(1068906653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633289017/5000000000 : ℝ)|^4195 ≤ (8563133086833/20000000000000 : ℝ)^3171
        have hw : |(2633289017/5000000000 : ℝ)|=(2633289017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204479153/10000000000 : ℝ)|^4195 ≤ (1352826449867/10000000000000 : ℝ)^3171
        have hw : |(-2204479153/10000000000 : ℝ)|=(2204479153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178490747/5000000000 : ℝ)*x 0 + (4232626953/10000000000 : ℝ)*x 1 + (4484924629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178490747/5000000000 : ℝ)^4195 ≤ (33317255046089/100000000000000 : ℝ)^3171 := by
    have hnat : (2178490747 : ℕ)^4195*100000000000000^3171 ≤ 33317255046089^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178490747 5000000000 33317255046089 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232626953/10000000000 : ℝ)^4195 ≤ (8016272386021/25000000000000 : ℝ)^3171 := by
    have hnat : (4232626953 : ℕ)^4195*25000000000000^3171 ≤ 8016272386021^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232626953 10000000000 8016272386021 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484924629/10000000000 : ℝ)^4195 ≤ (17308827703269/50000000000000 : ℝ)^3171 := by
    have hnat : (4484924629 : ℕ)^4195*50000000000000^3171 ≤ 17308827703269^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484924629 10000000000 17308827703269 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178490747/5000000000 : ℝ), (4232626953/10000000000 : ℝ), (4484924629/10000000000 : ℝ)] ![(33317255046089/100000000000000 : ℝ), (8016272386021/25000000000000 : ℝ), (17308827703269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178490747/5000000000 : ℝ)|^4195 ≤ (33317255046089/100000000000000 : ℝ)^3171
        have hw : |(2178490747/5000000000 : ℝ)|=(2178490747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232626953/10000000000 : ℝ)|^4195 ≤ (8016272386021/25000000000000 : ℝ)^3171
        have hw : |(4232626953/10000000000 : ℝ)|=(4232626953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484924629/10000000000 : ℝ)|^4195 ≤ (17308827703269/50000000000000 : ℝ)^3171
        have hw : |(4484924629/10000000000 : ℝ)|=(4484924629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070430523/5000000000 : ℝ)*x 0 + (658361761/1250000000 : ℝ)*x 1 + (168491323/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070430523/5000000000 : ℝ)^4195 ≤ (13014208083871/100000000000000 : ℝ)^3171 := by
    have hnat : (1070430523 : ℕ)^4195*100000000000000^3171 ≤ 13014208083871^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070430523 5000000000 13014208083871 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658361761/1250000000 : ℝ)^4195 ≤ (21409532311913/50000000000000 : ℝ)^3171 := by
    have hnat : (658361761 : ℕ)^4195*50000000000000^3171 ≤ 21409532311913^3171*1250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658361761 1250000000 21409532311913 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168491323/312500000 : ℝ)^4195 ≤ (8833345454541/20000000000000 : ℝ)^3171 := by
    have hnat : (168491323 : ℕ)^4195*20000000000000^3171 ≤ 8833345454541^3171*312500000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168491323 312500000 8833345454541 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070430523/5000000000 : ℝ), (658361761/1250000000 : ℝ), (168491323/312500000 : ℝ)] ![(13014208083871/100000000000000 : ℝ), (21409532311913/50000000000000 : ℝ), (8833345454541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070430523/5000000000 : ℝ)|^4195 ≤ (13014208083871/100000000000000 : ℝ)^3171
        have hw : |(-1070430523/5000000000 : ℝ)|=(1070430523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658361761/1250000000 : ℝ)|^4195 ≤ (21409532311913/50000000000000 : ℝ)^3171
        have hw : |(658361761/1250000000 : ℝ)|=(658361761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168491323/312500000 : ℝ)|^4195 ≤ (8833345454541/20000000000000 : ℝ)^3171
        have hw : |(168491323/312500000 : ℝ)|=(168491323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656310241/5000000000 : ℝ)*x 0 + (-1039667253/5000000000 : ℝ)*x 1 + (5391722523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656310241/5000000000 : ℝ)^4195 ≤ (21655774495221/50000000000000 : ℝ)^3171 := by
    have hnat : (2656310241 : ℕ)^4195*50000000000000^3171 ≤ 21655774495221^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656310241 5000000000 21655774495221 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039667253/5000000000 : ℝ)^4195 ≤ (6260860846223/50000000000000 : ℝ)^3171 := by
    have hnat : (1039667253 : ℕ)^4195*50000000000000^3171 ≤ 6260860846223^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039667253 5000000000 6260860846223 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391722523/10000000000 : ℝ)^4195 ≤ (22083364649599/50000000000000 : ℝ)^3171 := by
    have hnat : (5391722523 : ℕ)^4195*50000000000000^3171 ≤ 22083364649599^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391722523 10000000000 22083364649599 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656310241/5000000000 : ℝ), (-1039667253/5000000000 : ℝ), (5391722523/10000000000 : ℝ)] ![(21655774495221/50000000000000 : ℝ), (6260860846223/50000000000000 : ℝ), (22083364649599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656310241/5000000000 : ℝ)|^4195 ≤ (21655774495221/50000000000000 : ℝ)^3171
        have hw : |(2656310241/5000000000 : ℝ)|=(2656310241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039667253/5000000000 : ℝ)|^4195 ≤ (6260860846223/50000000000000 : ℝ)^3171
        have hw : |(-1039667253/5000000000 : ℝ)|=(1039667253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391722523/10000000000 : ℝ)|^4195 ≤ (22083364649599/50000000000000 : ℝ)^3171
        have hw : |(5391722523/10000000000 : ℝ)|=(5391722523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212504809/400000000 : ℝ)*x 0 + (5391722723/10000000000 : ℝ)*x 1 + (-1039667291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212504809/400000000 : ℝ)^4195 ≤ (4331154621863/10000000000000 : ℝ)^3171 := by
    have hnat : (212504809 : ℕ)^4195*10000000000000^3171 ≤ 4331154621863^3171*400000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212504809 400000000 4331154621863 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391722723/10000000000 : ℝ)^4195 ≤ (44166731466569/100000000000000 : ℝ)^3171 := by
    have hnat : (5391722723 : ℕ)^4195*100000000000000^3171 ≤ 44166731466569^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391722723 10000000000 44166731466569 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039667291/5000000000 : ℝ)^4195 ≤ (12521722297911/100000000000000 : ℝ)^3171 := by
    have hnat : (1039667291 : ℕ)^4195*100000000000000^3171 ≤ 12521722297911^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039667291 5000000000 12521722297911 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212504809/400000000 : ℝ), (5391722723/10000000000 : ℝ), (-1039667291/5000000000 : ℝ)] ![(4331154621863/10000000000000 : ℝ), (44166731466569/100000000000000 : ℝ), (12521722297911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212504809/400000000 : ℝ)|^4195 ≤ (4331154621863/10000000000000 : ℝ)^3171
        have hw : |(212504809/400000000 : ℝ)|=(212504809/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391722723/10000000000 : ℝ)|^4195 ≤ (44166731466569/100000000000000 : ℝ)^3171
        have hw : |(5391722723/10000000000 : ℝ)|=(5391722723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1039667291/5000000000 : ℝ)|^4195 ≤ (12521722297911/100000000000000 : ℝ)^3171
        have hw : |(-1039667291/5000000000 : ℝ)|=(1039667291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s7_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356991323/10000000000 : ℝ)*x 0 + (1121072311/2500000000 : ℝ)*x 1 + (4233264377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356991323/10000000000 : ℝ)^4195 ≤ (33317354478671/100000000000000 : ℝ)^3171 := by
    have hnat : (4356991323 : ℕ)^4195*100000000000000^3171 ≤ 33317354478671^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356991323 10000000000 33317354478671 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121072311/2500000000 : ℝ)^4195 ≤ (17305583745049/50000000000000 : ℝ)^3171 := by
    have hnat : (1121072311 : ℕ)^4195*50000000000000^3171 ≤ 17305583745049^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121072311 2500000000 17305583745049 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233264377/10000000000 : ℝ)^4195 ≤ (16035739009237/50000000000000 : ℝ)^3171 := by
    have hnat : (4233264377 : ℕ)^4195*50000000000000^3171 ≤ 16035739009237^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233264377 10000000000 16035739009237 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356991323/10000000000 : ℝ), (1121072311/2500000000 : ℝ), (4233264377/10000000000 : ℝ)] ![(33317354478671/100000000000000 : ℝ), (17305583745049/50000000000000 : ℝ), (16035739009237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356991323/10000000000 : ℝ)|^4195 ≤ (33317354478671/100000000000000 : ℝ)^3171
        have hw : |(4356991323/10000000000 : ℝ)|=(4356991323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121072311/2500000000 : ℝ)|^4195 ≤ (17305583745049/50000000000000 : ℝ)^3171
        have hw : |(1121072311/2500000000 : ℝ)|=(1121072311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233264377/10000000000 : ℝ)|^4195 ≤ (16035739009237/50000000000000 : ℝ)^3171
        have hw : |(4233264377/10000000000 : ℝ)|=(4233264377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11423/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5709/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5709/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5709/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5709/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5709/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5709/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5709/50000 : ℝ) ^ (8389/2048 : ℝ) ≤ (3448644468548999/25000000000000000000 : ℝ) := by
    have hpowers : (5709/50000 : ℝ)^8389 ≤ (3448644468548999/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5709 : ℕ)^8389*25000000000000000000^2048 ≤ 3448644468548999^2048*50000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5709 50000 3448644468548999 25000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5709/50000 : ℝ)) (X := (3448644468548999/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7043/50000 : ℝ) ^ (8389/2048 : ℝ) ≤ (32604040695243577/100000000000000000000 : ℝ) := by
    have hpowers : (7043/50000 : ℝ)^8389 ≤ (32604040695243577/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7043 : ℕ)^8389*100000000000000000000^2048 ≤ 32604040695243577^2048*50000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7043 50000 32604040695243577 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7043/50000 : ℝ)) (X := (32604040695243577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503448644468548999/12500000000000000000 : ℝ) ≤ (10000673461681307/10000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (12503448644468548999/12500000000000000000 : ℝ)^2048 ≤ (10000673461681307/10000000000000000 : ℝ)^8389 := by
      have hnat : (12503448644468548999 : ℕ)^2048*10000000000000000^8389 ≤ 10000673461681307^8389*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503448644468548999 12500000000000000000 10000673461681307 10000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000673461681307/10000000000000000 : ℝ)) (X := (12503448644468548999/12500000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046398618569439573/100000000000000000000 : ℝ) ≤ (1250141565908011/1250000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (100046398618569439573/100000000000000000000 : ℝ)^2048 ≤ (1250141565908011/1250000000000000 : ℝ)^8389 := by
      have hnat : (100046398618569439573 : ℕ)^2048*1250000000000000^8389 ≤ 1250141565908011^8389*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046398618569439573 100000000000000000000 1250141565908011 1250000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250141565908011/1250000000000000 : ℝ)) (X := (100046398618569439573/100000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032604040695243577/50000000000000000000 : ℝ) ≤ (10001591592846869/10000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (50032604040695243577/50000000000000000000 : ℝ)^2048 ≤ (10001591592846869/10000000000000000 : ℝ)^8389 := by
      have hnat : (50032604040695243577 : ℕ)^2048*10000000000000000^8389 ≤ 10001591592846869^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032604040695243577 50000000000000000000 10001591592846869 10000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001591592846869/10000000000000000 : ℝ)) (X := (50032604040695243577/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3448644468548999/25000000000000000000 : ℝ) ≤ ((5209240932444793/5210937500000000 : ℝ)+2*(459065582781/266800000000000 : ℝ)*(5709/50000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (5209240932444793/5210937500000000 : ℝ)+2*(459065582781/266800000000000 : ℝ)*(5709/50000 : ℝ)=(10000673461681307/10000000000000000 : ℝ) by norm_num, show 1+2*(3448644468548999/25000000000000000000 : ℝ)=(12503448644468548999/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32604040695243577/100000000000000000000 : ℝ)+(3448644468548999/25000000000000000000 : ℝ) ≤ ((5209240932444793/5210937500000000 : ℝ)+(459065582781/266800000000000 : ℝ)*((7043/50000 : ℝ)+(5709/50000 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (5209240932444793/5210937500000000 : ℝ)+(459065582781/266800000000000 : ℝ)*((7043/50000 : ℝ)+(5709/50000 : ℝ))=(1250141565908011/1250000000000000 : ℝ) by norm_num, show 1+(32604040695243577/100000000000000000000 : ℝ)+(3448644468548999/25000000000000000000 : ℝ)=(100046398618569439573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32604040695243577/100000000000000000000 : ℝ) ≤ ((5209240932444793/5210937500000000 : ℝ)+2*(459065582781/266800000000000 : ℝ)*(7043/50000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (5209240932444793/5210937500000000 : ℝ)+2*(459065582781/266800000000000 : ℝ)*(7043/50000 : ℝ)=(10001591592846869/10000000000000000 : ℝ) by norm_num, show 1+2*(32604040695243577/100000000000000000000 : ℝ)=(50032604040695243577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5209240932444793/5210937500000000 : ℝ)*(X 1 0+X 2 0)+(459065582781/266800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (5709/50000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (5209240932444793/5210937500000000 : ℝ)) (alpha := (459065582781/266800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5209240932444793/5210937500000000 : ℝ)*(X 0 1+X 2 1)+(459065582781/266800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (5709/50000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (5209240932444793/5210937500000000 : ℝ)) (alpha := (459065582781/266800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5209240932444793/5210937500000000 : ℝ)*(X 0 2+X 1 2)+(459065582781/266800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (5709/50000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (5209240932444793/5210937500000000 : ℝ)) (alpha := (459065582781/266800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2140856213/10000000000 : ℝ)*X 0 0+(269601981/500000000 : ℝ)*X 0 1+(5266578003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344533219/10000000000 : ℝ)*X 1 0+(-551119737/2500000000 : ℝ)*X 1 1+(1053315647/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068906653/2000000000 : ℝ)*X 2 0+(2633289017/5000000000 : ℝ)*X 2 1+(-2204479153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178490747/5000000000 : ℝ)*X 0 0+(4232626953/10000000000 : ℝ)*X 0 1+(4484924629/10000000000 : ℝ)*X 0 2+(2178490747/5000000000 : ℝ)*X 1 0+(4232626953/10000000000 : ℝ)*X 1 1+(4484924629/10000000000 : ℝ)*X 1 2+(2178490747/5000000000 : ℝ)*X 2 0+(4232626953/10000000000 : ℝ)*X 2 1+(4484924629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070430523/5000000000 : ℝ)*X 0 0+(658361761/1250000000 : ℝ)*X 0 1+(168491323/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656310241/5000000000 : ℝ)*X 1 0+(-1039667253/5000000000 : ℝ)*X 1 1+(5391722523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212504809/400000000 : ℝ)*X 2 0+(5391722723/10000000000 : ℝ)*X 2 1+(-1039667291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356991323/10000000000 : ℝ)*X 0 0+(1121072311/2500000000 : ℝ)*X 0 1+(4233264377/10000000000 : ℝ)*X 0 2+(4356991323/10000000000 : ℝ)*X 1 0+(1121072311/2500000000 : ℝ)*X 1 1+(4233264377/10000000000 : ℝ)*X 1 2+(4356991323/10000000000 : ℝ)*X 2 0+(1121072311/2500000000 : ℝ)*X 2 1+(4233264377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1613764789384519278005733/260546875000000000000000000000 : ℝ) := by norm_num
    linear_combination (101649569/10000000000000 : ℝ)*(base19) + (1178319403/100000000000000 : ℝ)*(base23) + (52629729/100000000000000 : ℝ)*(upper2) + (254154613/100000000000000 : ℝ)*(upper3) + (1403733/50000000000000 : ℝ)*(upper4) + (5967124204322527/100000000000000 : ℝ)*(major0) + (5967124204322527/100000000000000 : ℝ)*(major1) + (5967124204322527/100000000000000 : ℝ)*(major2) + (3985305777499079/50000000000000 : ℝ)*(sp0) + (7970643453666119/100000000000000 : ℝ)*(sp1) + (7970643291842407/100000000000000 : ℝ)*(sp2) + (247724081594899/6250000000000 : ℝ)*(sp3) + (8228790913/25000000000000 : ℝ)*(sp4) + (1842650619/10000000000000 : ℝ)*(sp7) + (1981801866012287/50000000000000 : ℝ)*(f.failure) + (797064447016181/10000000000000 : ℝ)*(f.sum) + (33731210544787/13340000000000000000000000000 : ℝ)*base65 + (222827701475596973/16675000000000000000000000000000 : ℝ)*base68 + (25235439117796973/16675000000000000000000000000000 : ℝ)*base70 + (154595107637078027/16675000000000000000000000000000 : ℝ)*base71 + (48371714802413/13340000000000000000000000000 : ℝ)*base74 + (93107198354621973/16675000000000000000000000000000 : ℝ)*base76 + (129194412777871973/16675000000000000000000000000000 : ℝ)*base78 + (96305477003553027/16675000000000000000000000000000 : ℝ)*base79 + (28965996128287/13340000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1326063/5000000000000000000000 : ℝ)*base90 + (1326063/5000000000000000000000 : ℝ)*base92 + (1326063/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9171337691832351773309211/1042187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2196433789/100000000000000 : ℝ)*(base19) + (226300207/12500000000000 : ℝ)*(base23) + (329120747/100000000000000 : ℝ)*(upper3) + (1297973/20000000000000 : ℝ)*(lower4) + (195361561/100000000000000 : ℝ)*(upper5) + (1499333266061599/25000000000000 : ℝ)*(major0) + (1499333266061599/25000000000000 : ℝ)*(major1) + (1499333266061599/25000000000000 : ℝ)*(major2) + (2079755621/3125000000000 : ℝ)*(sp1) + (64768097913/100000000000000 : ℝ)*(sp2) + (2002749041047887/25000000000000 : ℝ)*(sp4) + (4005463707788943/50000000000000 : ℝ)*(sp5) + (8010929585691979/100000000000000 : ℝ)*(sp6) + (1991834835482549/50000000000000 : ℝ)*(sp7) + (1991834835482549/50000000000000 : ℝ)*(f.failure) + (2002749041047887/25000000000000 : ℝ)*(f.sum) + (416815435591/3335000000000000000000000000 : ℝ)*base66 + (21761329746459901/4168750000000000000000000000000 : ℝ)*base68 + (57266681437002599/4168750000000000000000000000000 : ℝ)*base69 + (11429080945497401/4168750000000000000000000000000 : ℝ)*base72 + (15794271968081/3335000000000000000000000000 : ℝ)*base74 + (49124294903315099/4168750000000000000000000000000 : ℝ)*base75 + (50049307241747401/4168750000000000000000000000000 : ℝ)*base78 + (21592135337366151/4168750000000000000000000000000 : ℝ)*base80 + (6892669324677/1667500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (48207099/5000000000000000000000 : ℝ)*base89 + (48207099/5000000000000000000000 : ℝ)*base91 + (48207099/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1197_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1197_s8_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070429803/5000000000 : ℝ)*x 0 + (539199153/1000000000 : ℝ)*x 1 + (2633311961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070429803/5000000000 : ℝ)^4195 ≤ (13014196503367/100000000000000 : ℝ)^3171 := by
    have hnat : (1070429803 : ℕ)^4195*100000000000000^3171 ≤ 13014196503367^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070429803 5000000000 13014196503367 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539199153/1000000000 : ℝ)^4195 ≤ (44169644513651/100000000000000 : ℝ)^3171 := by
    have hnat : (539199153 : ℕ)^4195*100000000000000^3171 ≤ 44169644513651^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539199153 1000000000 44169644513651 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633311961/5000000000 : ℝ)^4195 ≤ (1338004967491/3125000000000 : ℝ)^3171 := by
    have hnat : (2633311961 : ℕ)^4195*3125000000000^3171 ≤ 1338004967491^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633311961 5000000000 1338004967491 3125000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070429803/5000000000 : ℝ), (539199153/1000000000 : ℝ), (2633311961/5000000000 : ℝ)] ![(13014196503367/100000000000000 : ℝ), (44169644513651/100000000000000 : ℝ), (1338004967491/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070429803/5000000000 : ℝ)|^4195 ≤ (13014196503367/100000000000000 : ℝ)^3171
        have hw : |(-1070429803/5000000000 : ℝ)|=(1070429803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539199153/1000000000 : ℝ)|^4195 ≤ (44169644513651/100000000000000 : ℝ)^3171
        have hw : |(539199153/1000000000 : ℝ)|=(539199153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633311961/5000000000 : ℝ)|^4195 ≤ (1338004967491/3125000000000 : ℝ)^3171
        have hw : |(2633311961/5000000000 : ℝ)|=(2633311961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267226067/500000000 : ℝ)*x 0 + (-275554279/1250000000 : ℝ)*x 1 + (1316655981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267226067/500000000 : ℝ)^4195 ≤ (4365594118953/10000000000000 : ℝ)^3171 := by
    have hnat : (267226067 : ℕ)^4195*10000000000000^3171 ≤ 4365594118953^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267226067 500000000 4365594118953 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275554279/1250000000 : ℝ)^4195 ≤ (541115992483/4000000000000 : ℝ)^3171 := by
    have hnat : (275554279 : ℕ)^4195*4000000000000^3171 ≤ 541115992483^3171*1250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275554279 1250000000 541115992483 4000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316655981/2500000000 : ℝ)^4195 ≤ (21408079490611/50000000000000 : ℝ)^3171 := by
    have hnat : (1316655981 : ℕ)^4195*50000000000000^3171 ≤ 21408079490611^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316655981 2500000000 21408079490611 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267226067/500000000 : ℝ), (-275554279/1250000000 : ℝ), (1316655981/2500000000 : ℝ)] ![(4365594118953/10000000000000 : ℝ), (541115992483/4000000000000 : ℝ), (21408079490611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267226067/500000000 : ℝ)|^4195 ≤ (4365594118953/10000000000000 : ℝ)^3171
        have hw : |(267226067/500000000 : ℝ)|=(267226067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275554279/1250000000 : ℝ)|^4195 ≤ (541115992483/4000000000000 : ℝ)^3171
        have hw : |(-275554279/1250000000 : ℝ)|=(275554279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316655981/2500000000 : ℝ)|^4195 ≤ (21408079490611/50000000000000 : ℝ)^3171
        have hw : |(1316655981/2500000000 : ℝ)|=(1316655981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344521371/10000000000 : ℝ)*x 0 + (2633311943/5000000000 : ℝ)*x 1 + (-1102217121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344521371/10000000000 : ℝ)^4195 ≤ (43655941524521/100000000000000 : ℝ)^3171 := by
    have hnat : (5344521371 : ℕ)^4195*100000000000000^3171 ≤ 43655941524521^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344521371 10000000000 43655941524521 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633311943/5000000000 : ℝ)^4195 ≤ (10704039643133/25000000000000 : ℝ)^3171 := by
    have hnat : (2633311943 : ℕ)^4195*25000000000000^3171 ≤ 10704039643133^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633311943 5000000000 10704039643133 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102217121/5000000000 : ℝ)^4195 ≤ (13527899893259/100000000000000 : ℝ)^3171 := by
    have hnat : (1102217121 : ℕ)^4195*100000000000000^3171 ≤ 13527899893259^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102217121 5000000000 13527899893259 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344521371/10000000000 : ℝ), (2633311943/5000000000 : ℝ), (-1102217121/5000000000 : ℝ)] ![(43655941524521/100000000000000 : ℝ), (10704039643133/25000000000000 : ℝ), (13527899893259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344521371/10000000000 : ℝ)|^4195 ≤ (43655941524521/100000000000000 : ℝ)^3171
        have hw : |(5344521371/10000000000 : ℝ)|=(5344521371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633311943/5000000000 : ℝ)|^4195 ≤ (10704039643133/25000000000000 : ℝ)^3171
        have hw : |(2633311943/5000000000 : ℝ)|=(2633311943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102217121/5000000000 : ℝ)|^4195 ≤ (13527899893259/100000000000000 : ℝ)^3171
        have hw : |(-1102217121/5000000000 : ℝ)|=(1102217121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356983959/10000000000 : ℝ)*x 0 + (4232720813/10000000000 : ℝ)*x 1 + (280301879/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356983959/10000000000 : ℝ)^4195 ≤ (33317279982629/100000000000000 : ℝ)^3171 := by
    have hnat : (4356983959 : ℕ)^4195*100000000000000^3171 ≤ 33317279982629^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356983959 10000000000 33317279982629 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232720813/10000000000 : ℝ)^4195 ≤ (16033015110289/50000000000000 : ℝ)^3171 := by
    have hnat : (4232720813 : ℕ)^4195*50000000000000^3171 ≤ 16033015110289^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232720813 10000000000 16033015110289 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280301879/625000000 : ℝ)^4195 ≤ (34616689784491/100000000000000 : ℝ)^3171 := by
    have hnat : (280301879 : ℕ)^4195*100000000000000^3171 ≤ 34616689784491^3171*625000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280301879 625000000 34616689784491 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356983959/10000000000 : ℝ), (4232720813/10000000000 : ℝ), (280301879/625000000 : ℝ)] ![(33317279982629/100000000000000 : ℝ), (16033015110289/50000000000000 : ℝ), (34616689784491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356983959/10000000000 : ℝ)|^4195 ≤ (33317279982629/100000000000000 : ℝ)^3171
        have hw : |(4356983959/10000000000 : ℝ)|=(4356983959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232720813/10000000000 : ℝ)|^4195 ≤ (16033015110289/50000000000000 : ℝ)^3171
        have hw : |(4232720813/10000000000 : ℝ)|=(4232720813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280301879/625000000 : ℝ)|^4195 ≤ (34616689784491/100000000000000 : ℝ)^3171
        have hw : |(280301879/625000000 : ℝ)|=(280301879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140864279/10000000000 : ℝ)*x 0 + (5266939281/10000000000 : ℝ)*x 1 + (1078335017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140864279/10000000000 : ℝ)^4195 ≤ (6507117041859/50000000000000 : ℝ)^3171 := by
    have hnat : (2140864279 : ℕ)^4195*50000000000000^3171 ≤ 6507117041859^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140864279 10000000000 6507117041859 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266939281/10000000000 : ℝ)^4195 ≤ (8563910136811/20000000000000 : ℝ)^3171 := by
    have hnat : (5266939281 : ℕ)^4195*20000000000000^3171 ≤ 8563910136811^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266939281 10000000000 8563910136811 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078335017/2000000000 : ℝ)^4195 ≤ (11041553805251/25000000000000 : ℝ)^3171 := by
    have hnat : (1078335017 : ℕ)^4195*25000000000000^3171 ≤ 11041553805251^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078335017 2000000000 11041553805251 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140864279/10000000000 : ℝ), (5266939281/10000000000 : ℝ), (1078335017/2000000000 : ℝ)] ![(6507117041859/50000000000000 : ℝ), (8563910136811/20000000000000 : ℝ), (11041553805251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140864279/10000000000 : ℝ)|^4195 ≤ (6507117041859/50000000000000 : ℝ)^3171
        have hw : |(-2140864279/10000000000 : ℝ)|=(2140864279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266939281/10000000000 : ℝ)|^4195 ≤ (8563910136811/20000000000000 : ℝ)^3171
        have hw : |(5266939281/10000000000 : ℝ)|=(5266939281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078335017/2000000000 : ℝ)|^4195 ≤ (11041553805251/25000000000000 : ℝ)^3171
        have hw : |(1078335017/2000000000 : ℝ)|=(1078335017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312632241/10000000000 : ℝ)*x 0 + (-2079383201/10000000000 : ℝ)*x 1 + (2695837511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312632241/10000000000 : ℝ)^4195 ≤ (43311675814367/100000000000000 : ℝ)^3171 := by
    have hnat : (5312632241 : ℕ)^4195*100000000000000^3171 ≤ 43311675814367^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312632241 10000000000 43311675814367 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079383201/10000000000 : ℝ)^4195 ≤ (12522109629641/100000000000000 : ℝ)^3171 := by
    have hnat : (2079383201 : ℕ)^4195*100000000000000^3171 ≤ 12522109629641^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079383201 10000000000 12522109629641 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695837511/5000000000 : ℝ)^4195 ≤ (44166214538283/100000000000000 : ℝ)^3171 := by
    have hnat : (2695837511 : ℕ)^4195*100000000000000^3171 ≤ 44166214538283^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695837511 5000000000 44166214538283 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312632241/10000000000 : ℝ), (-2079383201/10000000000 : ℝ), (2695837511/5000000000 : ℝ)] ![(43311675814367/100000000000000 : ℝ), (12522109629641/100000000000000 : ℝ), (44166214538283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312632241/10000000000 : ℝ)|^4195 ≤ (43311675814367/100000000000000 : ℝ)^3171
        have hw : |(5312632241/10000000000 : ℝ)|=(5312632241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079383201/10000000000 : ℝ)|^4195 ≤ (12522109629641/100000000000000 : ℝ)^3171
        have hw : |(-2079383201/10000000000 : ℝ)|=(2079383201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695837511/5000000000 : ℝ)|^4195 ≤ (44166214538283/100000000000000 : ℝ)^3171
        have hw : |(2695837511/5000000000 : ℝ)|=(2695837511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656316207/5000000000 : ℝ)*x 0 + (2695837459/5000000000 : ℝ)*x 1 + (-2079383109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656316207/5000000000 : ℝ)^4195 ≤ (43311677680219/100000000000000 : ℝ)^3171 := by
    have hnat : (2656316207 : ℕ)^4195*100000000000000^3171 ≤ 43311677680219^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656316207 5000000000 43311677680219 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695837459/5000000000 : ℝ)^4195 ≤ (44166213411253/100000000000000 : ℝ)^3171 := by
    have hnat : (2695837459 : ℕ)^4195*100000000000000^3171 ≤ 44166213411253^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695837459 5000000000 44166213411253 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079383109/10000000000 : ℝ)^4195 ≤ (195657951511/1562500000000 : ℝ)^3171 := by
    have hnat : (2079383109 : ℕ)^4195*1562500000000^3171 ≤ 195657951511^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079383109 10000000000 195657951511 1562500000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656316207/5000000000 : ℝ), (2695837459/5000000000 : ℝ), (-2079383109/10000000000 : ℝ)] ![(43311677680219/100000000000000 : ℝ), (44166213411253/100000000000000 : ℝ), (195657951511/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656316207/5000000000 : ℝ)|^4195 ≤ (43311677680219/100000000000000 : ℝ)^3171
        have hw : |(2656316207/5000000000 : ℝ)|=(2656316207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695837459/5000000000 : ℝ)|^4195 ≤ (44166213411253/100000000000000 : ℝ)^3171
        have hw : |(2695837459/5000000000 : ℝ)|=(2695837459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079383109/10000000000 : ℝ)|^4195 ≤ (195657951511/1562500000000 : ℝ)^3171
        have hw : |(-2079383109/10000000000 : ℝ)|=(2079383109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s8_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356993339/10000000000 : ℝ)*x 0 + (4484195791/10000000000 : ℝ)*x 1 + (4233357549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356993339/10000000000 : ℝ)^4195 ≤ (33317374873031/100000000000000 : ℝ)^3171 := by
    have hnat : (4356993339 : ℕ)^4195*100000000000000^3171 ≤ 33317374873031^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356993339 10000000000 33317374873031 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484195791/10000000000 : ℝ)^4195 ≤ (1384408530661/4000000000000 : ℝ)^3171 := by
    have hnat : (4484195791 : ℕ)^4195*4000000000000^3171 ≤ 1384408530661^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484195791 10000000000 1384408530661 4000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233357549/10000000000 : ℝ)^4195 ≤ (8018102961283/25000000000000 : ℝ)^3171 := by
    have hnat : (4233357549 : ℕ)^4195*25000000000000^3171 ≤ 8018102961283^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233357549 10000000000 8018102961283 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356993339/10000000000 : ℝ), (4484195791/10000000000 : ℝ), (4233357549/10000000000 : ℝ)] ![(33317374873031/100000000000000 : ℝ), (1384408530661/4000000000000 : ℝ), (8018102961283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356993339/10000000000 : ℝ)|^4195 ≤ (33317374873031/100000000000000 : ℝ)^3171
        have hw : |(4356993339/10000000000 : ℝ)|=(4356993339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484195791/10000000000 : ℝ)|^4195 ≤ (1384408530661/4000000000000 : ℝ)^3171
        have hw : |(4484195791/10000000000 : ℝ)|=(4484195791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233357549/10000000000 : ℝ)|^4195 ≤ (8018102961283/25000000000000 : ℝ)^3171
        have hw : |(4233357549/10000000000 : ℝ)|=(4233357549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (357/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11423/100000 : ℝ) ^ (8389/2048 : ℝ) ≤ (2763867716110011/20000000000000000000 : ℝ) := by
    have hpowers : (11423/100000 : ℝ)^8389 ≤ (2763867716110011/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11423 : ℕ)^8389*20000000000000000000^2048 ≤ 2763867716110011^2048*100000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11423 100000 2763867716110011 20000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11423/100000 : ℝ)) (X := (2763867716110011/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (8389/2048 : ℝ) ≤ (8139165166324201/25000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^8389 ≤ (8139165166324201/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14081 : ℕ)^8389*25000000000000000000^2048 ≤ 8139165166324201^2048*100000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 8139165166324201 25000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (8139165166324201/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002763867716110011/10000000000000000000 : ℝ) ≤ (10000674670391397/10000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (10002763867716110011/10000000000000000000 : ℝ)^2048 ≤ (10000674670391397/10000000000000000 : ℝ)^8389 := by
      have hnat : (10002763867716110011 : ℕ)^2048*10000000000000000^8389 ≤ 10000674670391397^8389*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002763867716110011 10000000000000000000 10000674670391397 10000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674670391397/10000000000000000 : ℝ)) (X := (10002763867716110011/10000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046375999245846859/100000000000000000000 : ℝ) ≤ (10001131975253851/10000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (100046375999245846859/100000000000000000000 : ℝ)^2048 ≤ (10001131975253851/10000000000000000 : ℝ)^8389 := by
      have hnat : (100046375999245846859 : ℕ)^2048*10000000000000000^8389 ≤ 10001131975253851^8389*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046375999245846859 100000000000000000000 10001131975253851 10000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001131975253851/10000000000000000 : ℝ)) (X := (100046375999245846859/100000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508139165166324201/12500000000000000000 : ℝ) ≤ (2000317856023261/2000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (12508139165166324201/12500000000000000000 : ℝ)^2048 ≤ (2000317856023261/2000000000000000 : ℝ)^8389 := by
      have hnat : (12508139165166324201 : ℕ)^2048*2000000000000000^8389 ≤ 2000317856023261^8389*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508139165166324201 12500000000000000000 2000317856023261 2000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000317856023261/2000000000000000 : ℝ)) (X := (12508139165166324201/12500000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2763867716110011/20000000000000000000 : ℝ) ≤ ((13285672843506354571/13290000000000000000 : ℝ)+2*(228652431227/132900000000000 : ℝ)*(11423/100000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (13285672843506354571/13290000000000000000 : ℝ)+2*(228652431227/132900000000000 : ℝ)*(11423/100000 : ℝ)=(10000674670391397/10000000000000000 : ℝ) by norm_num, show 1+2*(2763867716110011/20000000000000000000 : ℝ)=(10002763867716110011/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8139165166324201/25000000000000000000 : ℝ)+(2763867716110011/20000000000000000000 : ℝ) ≤ ((13285672843506354571/13290000000000000000 : ℝ)+(228652431227/132900000000000 : ℝ)*((14081/100000 : ℝ)+(11423/100000 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (13285672843506354571/13290000000000000000 : ℝ)+(228652431227/132900000000000 : ℝ)*((14081/100000 : ℝ)+(11423/100000 : ℝ))=(10001131975253851/10000000000000000 : ℝ) by norm_num, show 1+(8139165166324201/25000000000000000000 : ℝ)+(2763867716110011/20000000000000000000 : ℝ)=(100046375999245846859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8139165166324201/25000000000000000000 : ℝ) ≤ ((13285672843506354571/13290000000000000000 : ℝ)+2*(228652431227/132900000000000 : ℝ)*(14081/100000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (13285672843506354571/13290000000000000000 : ℝ)+2*(228652431227/132900000000000 : ℝ)*(14081/100000 : ℝ)=(2000317856023261/2000000000000000 : ℝ) by norm_num, show 1+2*(8139165166324201/25000000000000000000 : ℝ)=(12508139165166324201/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13285672843506354571/13290000000000000000 : ℝ)*(X 1 0+X 2 0)+(228652431227/132900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13285672843506354571/13290000000000000000 : ℝ)) (alpha := (228652431227/132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13285672843506354571/13290000000000000000 : ℝ)*(X 0 1+X 2 1)+(228652431227/132900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13285672843506354571/13290000000000000000 : ℝ)) (alpha := (228652431227/132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13285672843506354571/13290000000000000000 : ℝ)*(X 0 2+X 1 2)+(228652431227/132900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13285672843506354571/13290000000000000000 : ℝ)) (alpha := (228652431227/132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1070429803/5000000000 : ℝ)*X 0 0+(539199153/1000000000 : ℝ)*X 0 1+(2633311961/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267226067/500000000 : ℝ)*X 1 0+(-275554279/1250000000 : ℝ)*X 1 1+(1316655981/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344521371/10000000000 : ℝ)*X 2 0+(2633311943/5000000000 : ℝ)*X 2 1+(-1102217121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356983959/10000000000 : ℝ)*X 0 0+(4232720813/10000000000 : ℝ)*X 0 1+(280301879/625000000 : ℝ)*X 0 2+(4356983959/10000000000 : ℝ)*X 1 0+(4232720813/10000000000 : ℝ)*X 1 1+(280301879/625000000 : ℝ)*X 1 2+(4356983959/10000000000 : ℝ)*X 2 0+(4232720813/10000000000 : ℝ)*X 2 1+(280301879/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140864279/10000000000 : ℝ)*X 0 0+(5266939281/10000000000 : ℝ)*X 0 1+(1078335017/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312632241/10000000000 : ℝ)*X 1 0+(-2079383201/10000000000 : ℝ)*X 1 1+(2695837511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656316207/5000000000 : ℝ)*X 2 0+(2695837459/5000000000 : ℝ)*X 2 1+(-2079383109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356993339/10000000000 : ℝ)*X 0 0+(4484195791/10000000000 : ℝ)*X 0 1+(4233357549/10000000000 : ℝ)*X 0 2+(4356993339/10000000000 : ℝ)*X 1 0+(4484195791/10000000000 : ℝ)*X 1 1+(4233357549/10000000000 : ℝ)*X 1 2+(4356993339/10000000000 : ℝ)*X 2 0+(4484195791/10000000000 : ℝ)*X 2 1+(4233357549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1570444504859510766823/276875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1117912009/100000000000000 : ℝ)*(base19) + (569754637/50000000000000 : ℝ)*(base23) + (13184771/100000000000000 : ℝ)*(lower2) + (25910047/20000000000000 : ℝ)*(upper3) + (104180019/100000000000000 : ℝ)*(upper5) + (5971587590279437/100000000000000 : ℝ)*(major0) + (5971587590279437/100000000000000 : ℝ)*(major1) + (5971587590279437/100000000000000 : ℝ)*(major2) + (7976574416658671/100000000000000 : ℝ)*(sp0) + (1994151345301461/25000000000000 : ℝ)*(sp1) + (398830267980429/5000000000000 : ℝ)*(sp2) + (1983275464754753/50000000000000 : ℝ)*(sp3) + (32082459183/100000000000000 : ℝ)*(sp4) + (1756286369/10000000000000 : ℝ)*(sp7) + (991642123093299/25000000000000 : ℝ)*(f.failure) + (3988303249558927/50000000000000 : ℝ)*(f.sum) + (46096634466023/3322500000000000000000000000 : ℝ)*base66 + (2116861628565614491/443000000000000000000000000000000 : ℝ)*base68 + (3350172049264385509/443000000000000000000000000000000 : ℝ)*base69 + (3520589040594614491/443000000000000000000000000000000 : ℝ)*base72 + (10453242738001/6645000000000000000000000000 : ℝ)*base74 + (10672462062187385509/443000000000000000000000000000000 : ℝ)*base75 + (11412302774054614491/443000000000000000000000000000000 : ℝ)*base78 + (11136095674073385509/443000000000000000000000000000000 : ℝ)*base79 + (7136986122269/6645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (21280349/2500000000000000000000 : ℝ)*base89 + (21280349/2500000000000000000000 : ℝ)*base91 + (21280349/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139138798404330856878468177/13843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24016683/1562500000000 : ℝ)*(base19) + (5931531/312500000000 : ℝ)*(base23) + (577664513/100000000000000 : ℝ)*(lower1) + (80159733/100000000000000 : ℝ)*(upper3) + (37430731/100000000000000 : ℝ)*(lower4) + (100957153/50000000000000 : ℝ)*(upper5) + (375109842589413/6250000000000 : ℝ)*(major0) + (375109842589413/6250000000000 : ℝ)*(major1) + (375109842589413/6250000000000 : ℝ)*(major2) + (614422953/12500000000000 : ℝ)*(sp2) + (100211326014383/1250000000000 : ℝ)*(sp4) + (501056534005183/6250000000000 : ℝ)*(sp5) + (1002112408459637/12500000000000 : ℝ)*(sp6) + (996652136672157/25000000000000 : ℝ)*(sp7) + (996652136672157/25000000000000 : ℝ)*(f.failure) + (100211326014383/1250000000000 : ℝ)*(f.sum) + (927632240823/553750000000000000000000000 : ℝ)*base65 + (912115004419368941/27687500000000000000000000000000 : ℝ)*base67 + (298842179625131059/27687500000000000000000000000000 : ℝ)*base70 + (828079698501631059/27687500000000000000000000000000 : ℝ)*base72 + (3185818157843/553750000000000000000000000 : ℝ)*base73 + (61803566181868941/27687500000000000000000000000000 : ℝ)*base75 + (36990306885868941/27687500000000000000000000000000 : ℝ)*base77 + (77513216898368941/27687500000000000000000000000000 : ℝ)*base79 + (4478848728543/553750000000000000000000000 : ℝ)*base81 + (4899693/2500000000000000000000 : ℝ)*base90 + (4899693/2500000000000000000000 : ℝ)*base92 + (4899693/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1197_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1197_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1197_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1197_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1197_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1197_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:27:45.888724+00:00
-- url     : https://prove2.me/submissions/94e88f8a-3a9d-4040-a08d-6969c7819636

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
theorem support_rectangle_w1133_s3_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-135456101/625000000 : ℝ)*x 0 + (1086022279/2000000000 : ℝ)*x 1 + (81737971/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135456101/625000000 : ℝ)^4163 ≤ (82255110477/625000000000 : ℝ)^3139 := by
    have hnat : (135456101 : ℕ)^4163*625000000000^3139 ≤ 82255110477^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135456101 625000000 82255110477 625000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086022279/2000000000 : ℝ)^4163 ≤ (44493690824263/100000000000000 : ℝ)^3139 := by
    have hnat : (1086022279 : ℕ)^4163*100000000000000^3139 ≤ 44493690824263^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086022279 2000000000 44493690824263 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81737971/156250000 : ℝ)^4163 ≤ (846909829699/2000000000000 : ℝ)^3139 := by
    have hnat : (81737971 : ℕ)^4163*2000000000000^3139 ≤ 846909829699^3139*156250000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81737971 156250000 846909829699 2000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135456101/625000000 : ℝ), (1086022279/2000000000 : ℝ), (81737971/156250000 : ℝ)] ![(82255110477/625000000000 : ℝ), (44493690824263/100000000000000 : ℝ), (846909829699/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135456101/625000000 : ℝ)|^4163 ≤ (82255110477/625000000000 : ℝ)^3139
        have hw : |(-135456101/625000000 : ℝ)|=(135456101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086022279/2000000000 : ℝ)|^4163 ≤ (44493690824263/100000000000000 : ℝ)^3139
        have hw : |(1086022279/2000000000 : ℝ)|=(1086022279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81737971/156250000 : ℝ)|^4163 ≤ (846909829699/2000000000000 : ℝ)^3139
        have hw : |(81737971/156250000 : ℝ)|=(81737971/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354010519/10000000000 : ℝ)*x 0 + (-2268979133/10000000000 : ℝ)*x 1 + (81737969/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354010519/10000000000 : ℝ)^4163 ≤ (5458576035047/12500000000000 : ℝ)^3139 := by
    have hnat : (5354010519 : ℕ)^4163*12500000000000^3139 ≤ 5458576035047^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354010519 10000000000 5458576035047 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268979133/10000000000 : ℝ)^4163 ≤ (13985901589691/100000000000000 : ℝ)^3139 := by
    have hnat : (2268979133 : ℕ)^4163*100000000000000^3139 ≤ 13985901589691^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268979133 10000000000 13985901589691 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81737969/156250000 : ℝ)^4163 ≤ (21172745055409/50000000000000 : ℝ)^3139 := by
    have hnat : (81737969 : ℕ)^4163*50000000000000^3139 ≤ 21172745055409^3139*156250000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81737969 156250000 21172745055409 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354010519/10000000000 : ℝ), (-2268979133/10000000000 : ℝ), (81737969/156250000 : ℝ)] ![(5458576035047/12500000000000 : ℝ), (13985901589691/100000000000000 : ℝ), (21172745055409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354010519/10000000000 : ℝ)|^4163 ≤ (5458576035047/12500000000000 : ℝ)^3139
        have hw : |(5354010519/10000000000 : ℝ)|=(5354010519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2268979133/10000000000 : ℝ)|^4163 ≤ (13985901589691/100000000000000 : ℝ)^3139
        have hw : |(-2268979133/10000000000 : ℝ)|=(2268979133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81737969/156250000 : ℝ)|^4163 ≤ (21172745055409/50000000000000 : ℝ)^3139
        have hw : |(81737969/156250000 : ℝ)|=(81737969/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334625663/625000000 : ℝ)*x 0 + (5231230111/10000000000 : ℝ)*x 1 + (-2268978891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334625663/625000000 : ℝ)^4163 ≤ (21834304621543/50000000000000 : ℝ)^3139 := by
    have hnat : (334625663 : ℕ)^4163*50000000000000^3139 ≤ 21834304621543^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334625663 625000000 21834304621543 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231230111/10000000000 : ℝ)^4163 ≤ (21172745565341/50000000000000 : ℝ)^3139 := by
    have hnat : (5231230111 : ℕ)^4163*50000000000000^3139 ≤ 21172745565341^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231230111 10000000000 21172745565341 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268978891/10000000000 : ℝ)^4163 ≤ (13985899611399/100000000000000 : ℝ)^3139 := by
    have hnat : (2268978891 : ℕ)^4163*100000000000000^3139 ≤ 13985899611399^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268978891 10000000000 13985899611399 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334625663/625000000 : ℝ), (5231230111/10000000000 : ℝ), (-2268978891/10000000000 : ℝ)] ![(21834304621543/50000000000000 : ℝ), (21172745565341/50000000000000 : ℝ), (13985899611399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334625663/625000000 : ℝ)|^4163 ≤ (21834304621543/50000000000000 : ℝ)^3139
        have hw : |(334625663/625000000 : ℝ)|=(334625663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231230111/10000000000 : ℝ)|^4163 ≤ (21172745565341/50000000000000 : ℝ)^3139
        have hw : |(5231230111/10000000000 : ℝ)|=(5231230111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2268978891/10000000000 : ℝ)|^4163 ≤ (13985899611399/100000000000000 : ℝ)^3139
        have hw : |(-2268978891/10000000000 : ℝ)|=(2268978891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363626689/10000000000 : ℝ)*x 0 + (2085295743/5000000000 : ℝ)*x 1 + (4565561857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363626689/10000000000 : ℝ)^4163 ≤ (33293480250909/100000000000000 : ℝ)^3139 := by
    have hnat : (4363626689 : ℕ)^4163*100000000000000^3139 ≤ 33293480250909^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363626689 10000000000 33293480250909 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085295743/5000000000 : ℝ)^4163 ≤ (31354442603007/100000000000000 : ℝ)^3139 := by
    have hnat : (2085295743 : ℕ)^4163*100000000000000^3139 ≤ 31354442603007^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085295743 5000000000 31354442603007 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4565561857/10000000000 : ℝ)^4163 ≤ (7070415427497/20000000000000 : ℝ)^3139 := by
    have hnat : (4565561857 : ℕ)^4163*20000000000000^3139 ≤ 7070415427497^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565561857 10000000000 7070415427497 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363626689/10000000000 : ℝ), (2085295743/5000000000 : ℝ), (4565561857/10000000000 : ℝ)] ![(33293480250909/100000000000000 : ℝ), (31354442603007/100000000000000 : ℝ), (7070415427497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363626689/10000000000 : ℝ)|^4163 ≤ (33293480250909/100000000000000 : ℝ)^3139
        have hw : |(4363626689/10000000000 : ℝ)|=(4363626689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085295743/5000000000 : ℝ)|^4163 ≤ (31354442603007/100000000000000 : ℝ)^3139
        have hw : |(2085295743/5000000000 : ℝ)|=(2085295743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4565561857/10000000000 : ℝ)|^4163 ≤ (7070415427497/20000000000000 : ℝ)^3139
        have hw : |(4565561857/10000000000 : ℝ)|=(4565561857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167316133/10000000000 : ℝ)*x 0 + (5232006549/10000000000 : ℝ)*x 1 + (84833291/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167316133/10000000000 : ℝ)^4163 ≤ (6580483400693/50000000000000 : ℝ)^3139 := by
    have hnat : (2167316133 : ℕ)^4163*50000000000000^3139 ≤ 6580483400693^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167316133 10000000000 6580483400693 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232006549/10000000000 : ℝ)^4163 ≤ (42353826709089/100000000000000 : ℝ)^3139 := by
    have hnat : (5232006549 : ℕ)^4163*100000000000000^3139 ≤ 42353826709089^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232006549 10000000000 42353826709089 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84833291/156250000 : ℝ)^4163 ≤ (44485206480099/100000000000000 : ℝ)^3139 := by
    have hnat : (84833291 : ℕ)^4163*100000000000000^3139 ≤ 44485206480099^3139*156250000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84833291 156250000 44485206480099 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167316133/10000000000 : ℝ), (5232006549/10000000000 : ℝ), (84833291/156250000 : ℝ)] ![(6580483400693/50000000000000 : ℝ), (42353826709089/100000000000000 : ℝ), (44485206480099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167316133/10000000000 : ℝ)|^4163 ≤ (6580483400693/50000000000000 : ℝ)^3139
        have hw : |(-2167316133/10000000000 : ℝ)|=(2167316133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232006549/10000000000 : ℝ)|^4163 ≤ (42353826709089/100000000000000 : ℝ)^3139
        have hw : |(5232006549/10000000000 : ℝ)|=(5232006549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84833291/156250000 : ℝ)|^4163 ≤ (44485206480099/100000000000000 : ℝ)^3139
        have hw : |(84833291/156250000 : ℝ)|=(84833291/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303658013/10000000000 : ℝ)*x 0 + (-41417579/200000000 : ℝ)*x 1 + (2714665207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303658013/10000000000 : ℝ)^4163 ≤ (8624956901279/20000000000000 : ℝ)^3139 := by
    have hnat : (5303658013 : ℕ)^4163*20000000000000^3139 ≤ 8624956901279^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303658013 10000000000 8624956901279 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41417579/200000000 : ℝ)^4163 ≤ (3097502822279/25000000000000 : ℝ)^3139 := by
    have hnat : (41417579 : ℕ)^4163*25000000000000^3139 ≤ 3097502822279^3139*200000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41417579 200000000 3097502822279 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714665207/5000000000 : ℝ)^4163 ≤ (22242602099081/50000000000000 : ℝ)^3139 := by
    have hnat : (2714665207 : ℕ)^4163*50000000000000^3139 ≤ 22242602099081^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714665207 5000000000 22242602099081 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303658013/10000000000 : ℝ), (-41417579/200000000 : ℝ), (2714665207/5000000000 : ℝ)] ![(8624956901279/20000000000000 : ℝ), (3097502822279/25000000000000 : ℝ), (22242602099081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303658013/10000000000 : ℝ)|^4163 ≤ (8624956901279/20000000000000 : ℝ)^3139
        have hw : |(5303658013/10000000000 : ℝ)|=(5303658013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41417579/200000000 : ℝ)|^4163 ≤ (3097502822279/25000000000000 : ℝ)^3139
        have hw : |(-41417579/200000000 : ℝ)|=(41417579/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714665207/5000000000 : ℝ)|^4163 ≤ (22242602099081/50000000000000 : ℝ)^3139
        have hw : |(2714665207/5000000000 : ℝ)|=(2714665207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651829293/5000000000 : ℝ)*x 0 + (5429330039/10000000000 : ℝ)*x 1 + (-517719671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651829293/5000000000 : ℝ)^4163 ≤ (43124790685437/100000000000000 : ℝ)^3139 := by
    have hnat : (2651829293 : ℕ)^4163*100000000000000^3139 ≤ 43124790685437^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651829293 5000000000 43124790685437 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429330039/10000000000 : ℝ)^4163 ≤ (22242600061637/50000000000000 : ℝ)^3139 := by
    have hnat : (5429330039 : ℕ)^4163*50000000000000^3139 ≤ 22242600061637^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429330039 10000000000 22242600061637 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517719671/2500000000 : ℝ)^4163 ≤ (12390009178479/100000000000000 : ℝ)^3139 := by
    have hnat : (517719671 : ℕ)^4163*100000000000000^3139 ≤ 12390009178479^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517719671 2500000000 12390009178479 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651829293/5000000000 : ℝ), (5429330039/10000000000 : ℝ), (-517719671/2500000000 : ℝ)] ![(43124790685437/100000000000000 : ℝ), (22242600061637/50000000000000 : ℝ), (12390009178479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651829293/5000000000 : ℝ)|^4163 ≤ (43124790685437/100000000000000 : ℝ)^3139
        have hw : |(2651829293/5000000000 : ℝ)|=(2651829293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429330039/10000000000 : ℝ)|^4163 ≤ (22242600061637/50000000000000 : ℝ)^3139
        have hw : |(5429330039/10000000000 : ℝ)|=(5429330039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517719671/2500000000 : ℝ)|^4163 ≤ (12390009178479/100000000000000 : ℝ)^3139
        have hw : |(-517719671/2500000000 : ℝ)|=(517719671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s3_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872732651/2000000000 : ℝ)*x 0 + (1141005019/2500000000 : ℝ)*x 1 + (4172142163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872732651/2000000000 : ℝ)^4163 ≤ (33293850253487/100000000000000 : ℝ)^3139 := by
    have hnat : (872732651 : ℕ)^4163*100000000000000^3139 ≤ 33293850253487^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872732651 2000000000 33293850253487 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141005019/2500000000 : ℝ)^4163 ≤ (2208515323863/6250000000000 : ℝ)^3139 := by
    have hnat : (1141005019 : ℕ)^4163*6250000000000^3139 ≤ 2208515323863^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141005019 2500000000 2208515323863 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172142163/10000000000 : ℝ)^4163 ≤ (31369904550997/100000000000000 : ℝ)^3139 := by
    have hnat : (4172142163 : ℕ)^4163*100000000000000^3139 ≤ 31369904550997^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172142163 10000000000 31369904550997 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872732651/2000000000 : ℝ), (1141005019/2500000000 : ℝ), (4172142163/10000000000 : ℝ)] ![(33293850253487/100000000000000 : ℝ), (2208515323863/6250000000000 : ℝ), (31369904550997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872732651/2000000000 : ℝ)|^4163 ≤ (33293850253487/100000000000000 : ℝ)^3139
        have hw : |(872732651/2000000000 : ℝ)|=(872732651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141005019/2500000000 : ℝ)|^4163 ≤ (2208515323863/6250000000000 : ℝ)^3139
        have hw : |(1141005019/2500000000 : ℝ)|=(1141005019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172142163/10000000000 : ℝ)|^4163 ≤ (31369904550997/100000000000000 : ℝ)^3139
        have hw : |(4172142163/10000000000 : ℝ)|=(4172142163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (663/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (463/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9029/100000 : ℝ) ^ (8325/2048 : ℝ) ≤ (5685077409466001/100000000000000000000 : ℝ) := by
    have hpowers : (9029/100000 : ℝ)^8325 ≤ (5685077409466001/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9029 : ℕ)^8325*100000000000000000000^2048 ≤ 5685077409466001^2048*100000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9029 100000 5685077409466001 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9029/100000 : ℝ)) (X := (5685077409466001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16529/100000 : ℝ) ^ (8325/2048 : ℝ) ≤ (33203828080866697/50000000000000000000 : ℝ) := by
    have hpowers : (16529/100000 : ℝ)^8325 ≤ (33203828080866697/50000000000000000000 : ℝ)^2048 := by
      have hnat : (16529 : ℕ)^8325*50000000000000000000^2048 ≤ 33203828080866697^2048*100000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16529 100000 33203828080866697 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16529/100000 : ℝ)) (X := (33203828080866697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005685077409466001/50000000000000000000 : ℝ) ≤ (10000279700648343/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50005685077409466001/50000000000000000000 : ℝ)^2048 ≤ (10000279700648343/10000000000000000 : ℝ)^8325 := by
      have hnat : (50005685077409466001 : ℕ)^2048*10000000000000000^8325 ≤ 10000279700648343^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005685077409466001 50000000000000000000 10000279700648343 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279700648343/10000000000000000 : ℝ)) (X := (50005685077409466001/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20014418546714239879/20000000000000000000 : ℝ) ≤ (5000886521363083/5000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (20014418546714239879/20000000000000000000 : ℝ)^2048 ≤ (5000886521363083/5000000000000000 : ℝ)^8325 := by
      have hnat : (20014418546714239879 : ℕ)^2048*5000000000000000^8325 ≤ 5000886521363083^8325*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20014418546714239879 20000000000000000000 5000886521363083 5000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000886521363083/5000000000000000 : ℝ)) (X := (20014418546714239879/20000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25033203828080866697/25000000000000000000 : ℝ) ≤ (10003266384803989/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25033203828080866697/25000000000000000000 : ℝ)^2048 ≤ (10003266384803989/10000000000000000 : ℝ)^8325 := by
      have hnat : (25033203828080866697 : ℕ)^2048*10000000000000000^8325 ≤ 10003266384803989^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033203828080866697 25000000000000000000 10003266384803989 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003266384803989/10000000000000000 : ℝ)) (X := (25033203828080866697/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5685077409466001/100000000000000000000 : ℝ) ≤ ((37487565491810622383/37500000000000000000 : ℝ)+2*(1493342077823/750000000000000 : ℝ)*(9029/100000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (37487565491810622383/37500000000000000000 : ℝ)+2*(1493342077823/750000000000000 : ℝ)*(9029/100000 : ℝ)=(10000279700648343/10000000000000000 : ℝ) by norm_num, show 1+2*(5685077409466001/100000000000000000000 : ℝ)=(50005685077409466001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33203828080866697/50000000000000000000 : ℝ)+(5685077409466001/100000000000000000000 : ℝ) ≤ ((37487565491810622383/37500000000000000000 : ℝ)+(1493342077823/750000000000000 : ℝ)*((16529/100000 : ℝ)+(9029/100000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (37487565491810622383/37500000000000000000 : ℝ)+(1493342077823/750000000000000 : ℝ)*((16529/100000 : ℝ)+(9029/100000 : ℝ))=(5000886521363083/5000000000000000 : ℝ) by norm_num, show 1+(33203828080866697/50000000000000000000 : ℝ)+(5685077409466001/100000000000000000000 : ℝ)=(20014418546714239879/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33203828080866697/50000000000000000000 : ℝ) ≤ ((37487565491810622383/37500000000000000000 : ℝ)+2*(1493342077823/750000000000000 : ℝ)*(16529/100000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (37487565491810622383/37500000000000000000 : ℝ)+2*(1493342077823/750000000000000 : ℝ)*(16529/100000 : ℝ)=(10003266384803989/10000000000000000 : ℝ) by norm_num, show 1+2*(33203828080866697/50000000000000000000 : ℝ)=(25033203828080866697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37487565491810622383/37500000000000000000 : ℝ)*(X 1 0+X 2 0)+(1493342077823/750000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (9029/100000 : ℝ)) (hi := (16529/100000 : ℝ)) (c := (37487565491810622383/37500000000000000000 : ℝ)) (alpha := (1493342077823/750000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37487565491810622383/37500000000000000000 : ℝ)*(X 0 1+X 2 1)+(1493342077823/750000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (9029/100000 : ℝ)) (hi := (16529/100000 : ℝ)) (c := (37487565491810622383/37500000000000000000 : ℝ)) (alpha := (1493342077823/750000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37487565491810622383/37500000000000000000 : ℝ)*(X 0 2+X 1 2)+(1493342077823/750000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (9029/100000 : ℝ)) (hi := (16529/100000 : ℝ)) (c := (37487565491810622383/37500000000000000000 : ℝ)) (alpha := (1493342077823/750000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135456101/625000000 : ℝ)*X 0 0+(1086022279/2000000000 : ℝ)*X 0 1+(81737971/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354010519/10000000000 : ℝ)*X 1 0+(-2268979133/10000000000 : ℝ)*X 1 1+(81737969/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334625663/625000000 : ℝ)*X 2 0+(5231230111/10000000000 : ℝ)*X 2 1+(-2268978891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363626689/10000000000 : ℝ)*X 0 0+(2085295743/5000000000 : ℝ)*X 0 1+(4565561857/10000000000 : ℝ)*X 0 2+(4363626689/10000000000 : ℝ)*X 1 0+(2085295743/5000000000 : ℝ)*X 1 1+(4565561857/10000000000 : ℝ)*X 1 2+(4363626689/10000000000 : ℝ)*X 2 0+(2085295743/5000000000 : ℝ)*X 2 1+(4565561857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167316133/10000000000 : ℝ)*X 0 0+(5232006549/10000000000 : ℝ)*X 0 1+(84833291/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303658013/10000000000 : ℝ)*X 1 0+(-41417579/200000000 : ℝ)*X 1 1+(2714665207/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651829293/5000000000 : ℝ)*X 2 0+(5429330039/10000000000 : ℝ)*X 2 1+(-517719671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872732651/2000000000 : ℝ)*X 0 0+(1141005019/2500000000 : ℝ)*X 0 1+(4172142163/10000000000 : ℝ)*X 0 2+(872732651/2000000000 : ℝ)*X 1 0+(1141005019/2500000000 : ℝ)*X 1 1+(4172142163/10000000000 : ℝ)*X 1 2+(872732651/2000000000 : ℝ)*X 2 0+(1141005019/2500000000 : ℝ)*X 2 1+(4172142163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18663251361609674967051/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399569167/25000000000000 : ℝ)*(base19) + (377495799/25000000000000 : ℝ)*(base23) + (92023227/100000000000000 : ℝ)*(lower2) + (14381673/20000000000000 : ℝ)*(upper3) + (8416929/4000000000000 : ℝ)*(upper5) + (472502748494477/12500000000000 : ℝ)*(major0) + (472502748494477/12500000000000 : ℝ)*(major1) + (472502748494477/12500000000000 : ℝ)*(major2) + (5028150723313129/100000000000000 : ℝ)*(sp0) + (5028180720733903/100000000000000 : ℝ)*(sp1) + (314261300564211/6250000000000 : ℝ)*(sp2) + (2531848887863913/100000000000000 : ℝ)*(sp3) + (15797848721/50000000000000 : ℝ)*(sp4) + (628498123/5000000000000 : ℝ)*(sp7) + (2531861457826373/100000000000000 : ℝ)*(f.failure) + (5028182319010571/100000000000000 : ℝ)*(f.sum) + (41740583510983/9375000000000000000000000000 : ℝ)*base66 + (257354649126792897/156250000000000000000000000000000 : ℝ)*base67 + (1275762149935707103/156250000000000000000000000000000 : ℝ)*base70 + (520329223658042897/156250000000000000000000000000000 : ℝ)*base71 + (14333675435983/9375000000000000000000000000 : ℝ)*base74 + (1152736590064292897/156250000000000000000000000000000 : ℝ)*base75 + (292870612435707103/156250000000000000000000000000000 : ℝ)*base78 + (1188265057591957103/156250000000000000000000000000000 : ℝ)*base80 + (12172755054733/9375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (41632899/10000000000000000000000 : ℝ)*base90 + (41632899/10000000000000000000000 : ℝ)*base92 + (41632899/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137902459457707007721203563/78125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13478121/4000000000000 : ℝ)*(base19) + (245445693/25000000000000 : ℝ)*(base23) + (1786683/20000000000000 : ℝ)*(lower4) + (4362531/10000000000000 : ℝ)*(upper5) + (952453665195461/25000000000000 : ℝ)*(major0) + (952453665195461/25000000000000 : ℝ)*(major1) + (952453665195461/25000000000000 : ℝ)*(major2) + (473550033/50000000000000 : ℝ)*(sp0) + (3349217221/100000000000000 : ℝ)*(sp1) + (184764087/1562500000000 : ℝ)*(sp2) + (1266952926005217/25000000000000 : ℝ)*(sp4) + (158369030154709/3125000000000 : ℝ)*(sp5) + (5067799844436593/100000000000000 : ℝ)*(sp6) + (1275908305802183/50000000000000 : ℝ)*(sp7) + (1275908305802183/50000000000000 : ℝ)*(f.failure) + (2533906325560467/50000000000000 : ℝ)*(f.sum) + (10724681830153/9375000000000000000000000000 : ℝ)*base65 + (2136028431349415479/312500000000000000000000000000000 : ℝ)*base68 + (2318924173849415479/312500000000000000000000000000000 : ℝ)*base70 + (2176345167286915479/312500000000000000000000000000000 : ℝ)*base72 + (3643844677111/4687500000000000000000000000 : ℝ)*base74 + (2242948933849415479/312500000000000000000000000000000 : ℝ)*base76 + (2243176479474415479/312500000000000000000000000000000 : ℝ)*base78 + (383373264588084521/312500000000000000000000000000000 : ℝ)*base79 + (16593446869847/9375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12433071/5000000000000000000000 : ℝ)*base89 + (12433071/5000000000000000000000 : ℝ)*base91 + (12433071/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1133_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (463/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1133_s4_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170371913/10000000000 : ℝ)*x 0 + (5402323747/10000000000 : ℝ)*x 1 + (5257007111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170371913/10000000000 : ℝ)^4163 ≤ (3296395488637/25000000000000 : ℝ)^3139 := by
    have hnat : (2170371913 : ℕ)^4163*25000000000000^3139 ≤ 3296395488637^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170371913 10000000000 3296395488637 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402323747/10000000000 : ℝ)^4163 ≤ (44191978180639/100000000000000 : ℝ)^3139 := by
    have hnat : (5402323747 : ℕ)^4163*100000000000000^3139 ≤ 44191978180639^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402323747 10000000000 44191978180639 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257007111/10000000000 : ℝ)^4163 ≤ (2663902489961/6250000000000 : ℝ)^3139 := by
    have hnat : (5257007111 : ℕ)^4163*6250000000000^3139 ≤ 2663902489961^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257007111 10000000000 2663902489961 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170371913/10000000000 : ℝ), (5402323747/10000000000 : ℝ), (5257007111/10000000000 : ℝ)] ![(3296395488637/25000000000000 : ℝ), (44191978180639/100000000000000 : ℝ), (2663902489961/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170371913/10000000000 : ℝ)|^4163 ≤ (3296395488637/25000000000000 : ℝ)^3139
        have hw : |(-2170371913/10000000000 : ℝ)|=(2170371913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402323747/10000000000 : ℝ)|^4163 ≤ (44191978180639/100000000000000 : ℝ)^3139
        have hw : |(5402323747/10000000000 : ℝ)|=(5402323747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257007111/10000000000 : ℝ)|^4163 ≤ (2663902489961/6250000000000 : ℝ)^3139
        have hw : |(5257007111/10000000000 : ℝ)|=(5257007111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347077361/10000000000 : ℝ)*x 0 + (-448845631/2000000000 : ℝ)*x 1 + (5257007349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347077361/10000000000 : ℝ)^4163 ≤ (21796814216109/50000000000000 : ℝ)^3139 := by
    have hnat : (5347077361 : ℕ)^4163*50000000000000^3139 ≤ 21796814216109^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347077361 10000000000 21796814216109 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448845631/2000000000 : ℝ)^4163 ≤ (13783929151953/100000000000000 : ℝ)^3139 := by
    have hnat : (448845631 : ℕ)^4163*100000000000000^3139 ≤ 13783929151953^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448845631 2000000000 13783929151953 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257007349/10000000000 : ℝ)^4163 ≤ (42622442398503/100000000000000 : ℝ)^3139 := by
    have hnat : (5257007349 : ℕ)^4163*100000000000000^3139 ≤ 42622442398503^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257007349 10000000000 42622442398503 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347077361/10000000000 : ℝ), (-448845631/2000000000 : ℝ), (5257007349/10000000000 : ℝ)] ![(21796814216109/50000000000000 : ℝ), (13783929151953/100000000000000 : ℝ), (42622442398503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347077361/10000000000 : ℝ)|^4163 ≤ (21796814216109/50000000000000 : ℝ)^3139
        have hw : |(5347077361/10000000000 : ℝ)|=(5347077361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448845631/2000000000 : ℝ)|^4163 ≤ (13783929151953/100000000000000 : ℝ)^3139
        have hw : |(-448845631/2000000000 : ℝ)|=(448845631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257007349/10000000000 : ℝ)|^4163 ≤ (42622442398503/100000000000000 : ℝ)^3139
        have hw : |(5257007349/10000000000 : ℝ)|=(5257007349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347077981/10000000000 : ℝ)*x 0 + (2628503251/5000000000 : ℝ)*x 1 + (-44884569/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347077981/10000000000 : ℝ)^4163 ≤ (43593635135899/100000000000000 : ℝ)^3139 := by
    have hnat : (5347077981 : ℕ)^4163*100000000000000^3139 ≤ 43593635135899^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347077981 10000000000 43593635135899 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628503251/5000000000 : ℝ)^4163 ≤ (42622433291023/100000000000000 : ℝ)^3139 := by
    have hnat : (2628503251 : ℕ)^4163*100000000000000^3139 ≤ 42622433291023^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628503251 5000000000 42622433291023 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44884569/200000000 : ℝ)^4163 ≤ (6891965777447/50000000000000 : ℝ)^3139 := by
    have hnat : (44884569 : ℕ)^4163*50000000000000^3139 ≤ 6891965777447^3139*200000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44884569 200000000 6891965777447 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347077981/10000000000 : ℝ), (2628503251/5000000000 : ℝ), (-44884569/200000000 : ℝ)] ![(43593635135899/100000000000000 : ℝ), (42622433291023/100000000000000 : ℝ), (6891965777447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347077981/10000000000 : ℝ)|^4163 ≤ (43593635135899/100000000000000 : ℝ)^3139
        have hw : |(5347077981/10000000000 : ℝ)|=(5347077981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628503251/5000000000 : ℝ)|^4163 ≤ (42622433291023/100000000000000 : ℝ)^3139
        have hw : |(2628503251/5000000000 : ℝ)|=(2628503251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44884569/200000000 : ℝ)|^4163 ≤ (6891965777447/50000000000000 : ℝ)^3139
        have hw : |(-44884569/200000000 : ℝ)|=(44884569/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182730843/5000000000 : ℝ)*x 0 + (4223540693/10000000000 : ℝ)*x 1 + (902427219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182730843/5000000000 : ℝ)^4163 ≤ (16656024696611/50000000000000 : ℝ)^3139 := by
    have hnat : (2182730843 : ℕ)^4163*50000000000000^3139 ≤ 16656024696611^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182730843 5000000000 16656024696611 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223540693/10000000000 : ℝ)^4163 ≤ (15941731157039/50000000000000 : ℝ)^3139 := by
    have hnat : (4223540693 : ℕ)^4163*50000000000000^3139 ≤ 15941731157039^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223540693 10000000000 15941731157039 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902427219/2000000000 : ℝ)^4163 ≤ (17402244137341/50000000000000 : ℝ)^3139 := by
    have hnat : (902427219 : ℕ)^4163*50000000000000^3139 ≤ 17402244137341^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902427219 2000000000 17402244137341 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182730843/5000000000 : ℝ), (4223540693/10000000000 : ℝ), (902427219/2000000000 : ℝ)] ![(16656024696611/50000000000000 : ℝ), (15941731157039/50000000000000 : ℝ), (17402244137341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182730843/5000000000 : ℝ)|^4163 ≤ (16656024696611/50000000000000 : ℝ)^3139
        have hw : |(2182730843/5000000000 : ℝ)|=(2182730843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223540693/10000000000 : ℝ)|^4163 ≤ (15941731157039/50000000000000 : ℝ)^3139
        have hw : |(4223540693/10000000000 : ℝ)|=(4223540693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902427219/2000000000 : ℝ)|^4163 ≤ (17402244137341/50000000000000 : ℝ)^3139
        have hw : |(902427219/2000000000 : ℝ)|=(902427219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170379949/10000000000 : ℝ)*x 0 + (657177713/1250000000 : ℝ)*x 1 + (168809589/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170379949/10000000000 : ℝ)^4163 ≤ (412051459427/3125000000000 : ℝ)^3139 := by
    have hnat : (2170379949 : ℕ)^4163*3125000000000^3139 ≤ 412051459427^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170379949 10000000000 412051459427 3125000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657177713/1250000000 : ℝ)^4163 ≤ (42626897863239/100000000000000 : ℝ)^3139 := by
    have hnat : (657177713 : ℕ)^4163*100000000000000^3139 ≤ 42626897863239^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657177713 1250000000 42626897863239 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168809589/312500000 : ℝ)^4163 ≤ (44187455422981/100000000000000 : ℝ)^3139 := by
    have hnat : (168809589 : ℕ)^4163*100000000000000^3139 ≤ 44187455422981^3139*312500000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168809589 312500000 44187455422981 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170379949/10000000000 : ℝ), (657177713/1250000000 : ℝ), (168809589/312500000 : ℝ)] ![(412051459427/3125000000000 : ℝ), (42626897863239/100000000000000 : ℝ), (44187455422981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170379949/10000000000 : ℝ)|^4163 ≤ (412051459427/3125000000000 : ℝ)^3139
        have hw : |(-2170379949/10000000000 : ℝ)|=(2170379949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657177713/1250000000 : ℝ)|^4163 ≤ (42626897863239/100000000000000 : ℝ)^3139
        have hw : |(657177713/1250000000 : ℝ)|=(657177713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168809589/312500000 : ℝ)|^4163 ≤ (44187455422981/100000000000000 : ℝ)^3139
        have hw : |(168809589/312500000 : ℝ)|=(168809589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655143903/5000000000 : ℝ)*x 0 + (-209932791/1000000000 : ℝ)*x 1 + (5401907001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655143903/5000000000 : ℝ)^4163 ≤ (1079907314199/2500000000000 : ℝ)^3139 := by
    have hnat : (2655143903 : ℕ)^4163*2500000000000^3139 ≤ 1079907314199^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655143903 5000000000 1079907314199 2500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209932791/1000000000 : ℝ)^4163 ≤ (12616250329177/100000000000000 : ℝ)^3139 := by
    have hnat : (209932791 : ℕ)^4163*100000000000000^3139 ≤ 12616250329177^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209932791 1000000000 12616250329177 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401907001/10000000000 : ℝ)^4163 ≤ (5523432135349/12500000000000 : ℝ)^3139 := by
    have hnat : (5401907001 : ℕ)^4163*12500000000000^3139 ≤ 5523432135349^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401907001 10000000000 5523432135349 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655143903/5000000000 : ℝ), (-209932791/1000000000 : ℝ), (5401907001/10000000000 : ℝ)] ![(1079907314199/2500000000000 : ℝ), (12616250329177/100000000000000 : ℝ), (5523432135349/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655143903/5000000000 : ℝ)|^4163 ≤ (1079907314199/2500000000000 : ℝ)^3139
        have hw : |(2655143903/5000000000 : ℝ)|=(2655143903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209932791/1000000000 : ℝ)|^4163 ≤ (12616250329177/100000000000000 : ℝ)^3139
        have hw : |(-209932791/1000000000 : ℝ)|=(209932791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401907001/10000000000 : ℝ)|^4163 ≤ (5523432135349/12500000000000 : ℝ)^3139
        have hw : |(5401907001/10000000000 : ℝ)|=(5401907001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531028801/1000000000 : ℝ)*x 0 + (1350476701/2500000000 : ℝ)*x 1 + (-2099327903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531028801/1000000000 : ℝ)^4163 ≤ (1727851790749/4000000000000 : ℝ)^3139 := by
    have hnat : (531028801 : ℕ)^4163*4000000000000^3139 ≤ 1727851790749^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531028801 1000000000 1727851790749 4000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350476701/2500000000 : ℝ)^4163 ≤ (883749098913/2000000000000 : ℝ)^3139 := by
    have hnat : (1350476701 : ℕ)^4163*2000000000000^3139 ≤ 883749098913^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350476701 2500000000 883749098913 2000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099327903/10000000000 : ℝ)^4163 ≤ (6308125136693/50000000000000 : ℝ)^3139 := by
    have hnat : (2099327903 : ℕ)^4163*50000000000000^3139 ≤ 6308125136693^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099327903 10000000000 6308125136693 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531028801/1000000000 : ℝ), (1350476701/2500000000 : ℝ), (-2099327903/10000000000 : ℝ)] ![(1727851790749/4000000000000 : ℝ), (883749098913/2000000000000 : ℝ), (6308125136693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531028801/1000000000 : ℝ)|^4163 ≤ (1727851790749/4000000000000 : ℝ)^3139
        have hw : |(531028801/1000000000 : ℝ)|=(531028801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350476701/2500000000 : ℝ)|^4163 ≤ (883749098913/2000000000000 : ℝ)^3139
        have hw : |(1350476701/2500000000 : ℝ)|=(1350476701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099327903/10000000000 : ℝ)|^4163 ≤ (6308125136693/50000000000000 : ℝ)^3139
        have hw : |(-2099327903/10000000000 : ℝ)|=(2099327903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s4_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365475963/10000000000 : ℝ)*x 0 + (2255655407/5000000000 : ℝ)*x 1 + (4224369479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365475963/10000000000 : ℝ)^4163 ≤ (33312193878453/100000000000000 : ℝ)^3139 := by
    have hnat : (4365475963 : ℕ)^4163*100000000000000^3139 ≤ 33312193878453^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365475963 10000000000 33312193878453 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255655407/5000000000 : ℝ)^4163 ≤ (34796046047261/100000000000000 : ℝ)^3139 := by
    have hnat : (2255655407 : ℕ)^4163*100000000000000^3139 ≤ 34796046047261^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255655407 5000000000 34796046047261 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224369479/10000000000 : ℝ)^4163 ≤ (7972940015297/25000000000000 : ℝ)^3139 := by
    have hnat : (4224369479 : ℕ)^4163*25000000000000^3139 ≤ 7972940015297^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224369479 10000000000 7972940015297 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365475963/10000000000 : ℝ), (2255655407/5000000000 : ℝ), (4224369479/10000000000 : ℝ)] ![(33312193878453/100000000000000 : ℝ), (34796046047261/100000000000000 : ℝ), (7972940015297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365475963/10000000000 : ℝ)|^4163 ≤ (33312193878453/100000000000000 : ℝ)^3139
        have hw : |(4365475963/10000000000 : ℝ)|=(4365475963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255655407/5000000000 : ℝ)|^4163 ≤ (34796046047261/100000000000000 : ℝ)^3139
        have hw : |(2255655407/5000000000 : ℝ)|=(2255655407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224369479/10000000000 : ℝ)|^4163 ≤ (7972940015297/25000000000000 : ℝ)^3139
        have hw : |(4224369479/10000000000 : ℝ)|=(4224369479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (463/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5579/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (463/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (663/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (463/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (663/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (463/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (663/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (463/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (663/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (463/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (663/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (463/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (663/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (663/6250 : ℝ) ^ (8325/2048 : ℝ) ≤ (1368255892861849/12500000000000000000 : ℝ) := by
    have hpowers : (663/6250 : ℝ)^8325 ≤ (1368255892861849/12500000000000000000 : ℝ)^2048 := by
      have hnat : (663 : ℕ)^8325*12500000000000000000^2048 ≤ 1368255892861849^2048*6250^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        663 6250 1368255892861849 12500000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (663/6250 : ℝ)) (X := (1368255892861849/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (463/3125 : ℝ) ^ (8325/2048 : ℝ) ≤ (21283349887646883/50000000000000000000 : ℝ) := by
    have hpowers : (463/3125 : ℝ)^8325 ≤ (21283349887646883/50000000000000000000 : ℝ)^2048 := by
      have hnat : (463 : ℕ)^8325*50000000000000000000^2048 ≤ 21283349887646883^2048*3125^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        463 3125 21283349887646883 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (463/3125 : ℝ)) (X := (21283349887646883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251368255892861849/6250000000000000000 : ℝ) ≤ (10000538514224911/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (6251368255892861849/6250000000000000000 : ℝ)^2048 ≤ (10000538514224911/10000000000000000 : ℝ)^8325 := by
      have hnat : (6251368255892861849 : ℕ)^2048*10000000000000000^8325 ≤ 10000538514224911^8325*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251368255892861849 6250000000000000000 10000538514224911 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538514224911/10000000000000000 : ℝ)) (X := (6251368255892861849/6250000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026756373459094279/50000000000000000000 : ℝ) ≤ (2500329045053843/2500000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50026756373459094279/50000000000000000000 : ℝ)^2048 ≤ (2500329045053843/2500000000000000 : ℝ)^8325 := by
      have hnat : (50026756373459094279 : ℕ)^2048*2500000000000000^8325 ≤ 2500329045053843^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026756373459094279 50000000000000000000 2500329045053843 2500000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500329045053843/2500000000000000 : ℝ)) (X := (50026756373459094279/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021283349887646883/25000000000000000000 : ℝ) ≤ (10002093846205833/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25021283349887646883/25000000000000000000 : ℝ)^2048 ≤ (10002093846205833/10000000000000000 : ℝ)^8325 := by
      have hnat : (25021283349887646883 : ℕ)^2048*10000000000000000^8325 ≤ 10002093846205833^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021283349887646883 25000000000000000000 10002093846205833 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002093846205833/10000000000000000 : ℝ)) (X := (25021283349887646883/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1368255892861849/12500000000000000000 : ℝ) ≤ ((2629110444137800307/2630000000000000000 : ℝ)+2*(777665990461/420800000000000 : ℝ)*(663/6250 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (2629110444137800307/2630000000000000000 : ℝ)+2*(777665990461/420800000000000 : ℝ)*(663/6250 : ℝ)=(10000538514224911/10000000000000000 : ℝ) by norm_num, show 1+2*(1368255892861849/12500000000000000000 : ℝ)=(6251368255892861849/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21283349887646883/50000000000000000000 : ℝ)+(1368255892861849/12500000000000000000 : ℝ) ≤ ((2629110444137800307/2630000000000000000 : ℝ)+(777665990461/420800000000000 : ℝ)*((463/3125 : ℝ)+(663/6250 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (2629110444137800307/2630000000000000000 : ℝ)+(777665990461/420800000000000 : ℝ)*((463/3125 : ℝ)+(663/6250 : ℝ))=(2500329045053843/2500000000000000 : ℝ) by norm_num, show 1+(21283349887646883/50000000000000000000 : ℝ)+(1368255892861849/12500000000000000000 : ℝ)=(50026756373459094279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21283349887646883/50000000000000000000 : ℝ) ≤ ((2629110444137800307/2630000000000000000 : ℝ)+2*(777665990461/420800000000000 : ℝ)*(463/3125 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (2629110444137800307/2630000000000000000 : ℝ)+2*(777665990461/420800000000000 : ℝ)*(463/3125 : ℝ)=(10002093846205833/10000000000000000 : ℝ) by norm_num, show 1+2*(21283349887646883/50000000000000000000 : ℝ)=(25021283349887646883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2629110444137800307/2630000000000000000 : ℝ)*(X 1 0+X 2 0)+(777665990461/420800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (463/3125 : ℝ)) (c := (2629110444137800307/2630000000000000000 : ℝ)) (alpha := (777665990461/420800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2629110444137800307/2630000000000000000 : ℝ)*(X 0 1+X 2 1)+(777665990461/420800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (463/3125 : ℝ)) (c := (2629110444137800307/2630000000000000000 : ℝ)) (alpha := (777665990461/420800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2629110444137800307/2630000000000000000 : ℝ)*(X 0 2+X 1 2)+(777665990461/420800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (463/3125 : ℝ)) (c := (2629110444137800307/2630000000000000000 : ℝ)) (alpha := (777665990461/420800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2170371913/10000000000 : ℝ)*X 0 0+(5402323747/10000000000 : ℝ)*X 0 1+(5257007111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347077361/10000000000 : ℝ)*X 1 0+(-448845631/2000000000 : ℝ)*X 1 1+(5257007349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347077981/10000000000 : ℝ)*X 2 0+(2628503251/5000000000 : ℝ)*X 2 1+(-44884569/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182730843/5000000000 : ℝ)*X 0 0+(4223540693/10000000000 : ℝ)*X 0 1+(902427219/2000000000 : ℝ)*X 0 2+(2182730843/5000000000 : ℝ)*X 1 0+(4223540693/10000000000 : ℝ)*X 1 1+(902427219/2000000000 : ℝ)*X 1 2+(2182730843/5000000000 : ℝ)*X 2 0+(4223540693/10000000000 : ℝ)*X 2 1+(902427219/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2170379949/10000000000 : ℝ)*X 0 0+(657177713/1250000000 : ℝ)*X 0 1+(168809589/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655143903/5000000000 : ℝ)*X 1 0+(-209932791/1000000000 : ℝ)*X 1 1+(5401907001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531028801/1000000000 : ℝ)*X 2 0+(1350476701/2500000000 : ℝ)*X 2 1+(-2099327903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365475963/10000000000 : ℝ)*X 0 0+(2255655407/5000000000 : ℝ)*X 0 1+(4224369479/10000000000 : ℝ)*X 0 2+(4365475963/10000000000 : ℝ)*X 1 0+(2255655407/5000000000 : ℝ)*X 1 1+(4224369479/10000000000 : ℝ)*X 1 2+(4365475963/10000000000 : ℝ)*X 2 0+(2255655407/5000000000 : ℝ)*X 2 1+(4224369479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (263683542958530293671293/21040000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7518519/781250000000 : ℝ)*(base23) + (116738891/50000000000000 : ℝ)*(lower2) + (81890089/50000000000000 : ℝ)*(upper3) + (337330937/100000000000000 : ℝ)*(lower4) + (164896811/100000000000000 : ℝ)*(upper5) + (5173300448112469/100000000000000 : ℝ)*(major0) + (5173300448112469/100000000000000 : ℝ)*(major1) + (5173300448112469/100000000000000 : ℝ)*(major2) + (688152010167701/10000000000000 : ℝ)*(sp0) + (688152010167701/10000000000000 : ℝ)*(sp1) + (6881514811922733/100000000000000 : ℝ)*(sp2) + (216566762313839/6250000000000 : ℝ)*(sp3) + (865476769/20000000000000 : ℝ)*(sp6) + (12179776893/100000000000000 : ℝ)*(sp7) + (1732540188399159/50000000000000 : ℝ)*(f.failure) + (688152010167701/10000000000000 : ℝ)*(f.sum) + (1415963554942511/21040000000000000000000000000 : ℝ)*base66 + (1984470316614465767/263000000000000000000000000000000 : ℝ)*base68 + (2301961035006534233/263000000000000000000000000000000 : ℝ)*base69 + (13811546186841465767/263000000000000000000000000000000 : ℝ)*base72 + (132345901846849/21040000000000000000000000000 : ℝ)*base73 + (1197590271066534233/263000000000000000000000000000000 : ℝ)*base75 + (1872808626039534233/263000000000000000000000000000000 : ℝ)*base77 + (585529889002465767/263000000000000000000000000000000 : ℝ)*base80 + (120978916490529/21040000000000000000000000000 : ℝ)*base81 + (1066783/5000000000000000000000 : ℝ)*base89 + (1066783/5000000000000000000000 : ℝ)*base91 + (1066783/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128699522828941422670815699/131500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6435623/1250000000000 : ℝ)*(base19) + (945673207/100000000000000 : ℝ)*(base23) + (48140809/50000000000000 : ℝ)*(upper2) + (62766901/100000000000000 : ℝ)*(upper3) + (62153331/20000000000000 : ℝ)*(upper5) + (5203083066690781/100000000000000 : ℝ)*(major0) + (5203083066690781/100000000000000 : ℝ)*(major1) + (5203083066690781/100000000000000 : ℝ)*(major2) + (9657001967/50000000000000 : ℝ)*(sp1) + (3390172189/20000000000000 : ℝ)*(sp2) + (3460568652262087/50000000000000 : ℝ)*(sp4) + (2162849211147/31250000000 : ℝ)*(sp5) + (3460559703995011/50000000000000 : ℝ)*(sp6) + (435628599529241/12500000000000 : ℝ)*(sp7) + (435628599529241/12500000000000 : ℝ)*(f.failure) + (3460568652262087/50000000000000 : ℝ)*(f.sum) + (110941638920521/21040000000000000000000000000 : ℝ)*base65 + (3147516066052126017/263000000000000000000000000000000 : ℝ)*base67 + (369800228764126017/263000000000000000000000000000000 : ℝ)*base69 + (605647354997873983/263000000000000000000000000000000 : ℝ)*base72 + (166866251713161/21040000000000000000000000000 : ℝ)*base73 + (2034790683682126017/263000000000000000000000000000000 : ℝ)*base75 + (57873322269126017/263000000000000000000000000000000 : ℝ)*base77 + (3266659850013873983/263000000000000000000000000000000 : ℝ)*base80 + (45281503748201/21040000000000000000000000000 : ℝ)*base81 + (4175983/1250000000000000000000 : ℝ)*base90 + (4175983/1250000000000000000000 : ℝ)*base92 + (4175983/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (463/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1133_s5_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-434205991/2000000000 : ℝ)*x 0 + (269757393/500000000 : ℝ)*x 1 + (1315937757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434205991/2000000000 : ℝ)^4163 ≤ (2638176829007/20000000000000 : ℝ)^3139 := by
    have hnat : (434205991 : ℕ)^4163*20000000000000^3139 ≤ 2638176829007^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434205991 2000000000 2638176829007 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269757393/500000000 : ℝ)^4163 ≤ (11028536491383/25000000000000 : ℝ)^3139 := by
    have hnat : (269757393 : ℕ)^4163*25000000000000^3139 ≤ 11028536491383^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269757393 500000000 11028536491383 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315937757/2500000000 : ℝ)^4163 ≤ (10673742468779/25000000000000 : ℝ)^3139 := by
    have hnat : (1315937757 : ℕ)^4163*25000000000000^3139 ≤ 10673742468779^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315937757 2500000000 10673742468779 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434205991/2000000000 : ℝ), (269757393/500000000 : ℝ), (1315937757/2500000000 : ℝ)] ![(2638176829007/20000000000000 : ℝ), (11028536491383/25000000000000 : ℝ), (10673742468779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434205991/2000000000 : ℝ)|^4163 ≤ (2638176829007/20000000000000 : ℝ)^3139
        have hw : |(-434205991/2000000000 : ℝ)|=(434205991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269757393/500000000 : ℝ)|^4163 ≤ (11028536491383/25000000000000 : ℝ)^3139
        have hw : |(269757393/500000000 : ℝ)|=(269757393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315937757/2500000000 : ℝ)|^4163 ≤ (10673742468779/25000000000000 : ℝ)^3139
        have hw : |(1315937757/2500000000 : ℝ)|=(1315937757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345279483/10000000000 : ℝ)*x 0 + (-447541497/2000000000 : ℝ)*x 1 + (2631875521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345279483/10000000000 : ℝ)^4163 ≤ (21787095071413/50000000000000 : ℝ)^3139 := by
    have hnat : (5345279483 : ℕ)^4163*50000000000000^3139 ≤ 21787095071413^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345279483 10000000000 21787095071413 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447541497/2000000000 : ℝ)^4163 ≤ (13730839810381/100000000000000 : ℝ)^3139 := by
    have hnat : (447541497 : ℕ)^4163*100000000000000^3139 ≤ 13730839810381^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447541497 2000000000 13730839810381 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631875521/5000000000 : ℝ)^4163 ≤ (10673742506429/25000000000000 : ℝ)^3139 := by
    have hnat : (2631875521 : ℕ)^4163*25000000000000^3139 ≤ 10673742506429^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631875521 5000000000 10673742506429 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345279483/10000000000 : ℝ), (-447541497/2000000000 : ℝ), (2631875521/5000000000 : ℝ)] ![(21787095071413/50000000000000 : ℝ), (13730839810381/100000000000000 : ℝ), (10673742506429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345279483/10000000000 : ℝ)|^4163 ≤ (21787095071413/50000000000000 : ℝ)^3139
        have hw : |(5345279483/10000000000 : ℝ)|=(5345279483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447541497/2000000000 : ℝ)|^4163 ≤ (13730839810381/100000000000000 : ℝ)^3139
        have hw : |(-447541497/2000000000 : ℝ)|=(447541497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631875521/5000000000 : ℝ)|^4163 ≤ (10673742506429/25000000000000 : ℝ)^3139
        have hw : |(2631875521/5000000000 : ℝ)|=(2631875521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345279753/10000000000 : ℝ)*x 0 + (5263750817/10000000000 : ℝ)*x 1 + (-89508297/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345279753/10000000000 : ℝ)^4163 ≤ (871483861237/2000000000000 : ℝ)^3139 := by
    have hnat : (5345279753 : ℕ)^4163*2000000000000^3139 ≤ 871483861237^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345279753 10000000000 871483861237 2000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263750817/10000000000 : ℝ)^4163 ≤ (21347483802681/50000000000000 : ℝ)^3139 := by
    have hnat : (5263750817 : ℕ)^4163*50000000000000^3139 ≤ 21347483802681^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263750817 10000000000 21347483802681 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89508297/400000000 : ℝ)^4163 ≤ (13730839322111/100000000000000 : ℝ)^3139 := by
    have hnat : (89508297 : ℕ)^4163*100000000000000^3139 ≤ 13730839322111^3139*400000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89508297 400000000 13730839322111 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345279753/10000000000 : ℝ), (5263750817/10000000000 : ℝ), (-89508297/400000000 : ℝ)] ![(871483861237/2000000000000 : ℝ), (21347483802681/50000000000000 : ℝ), (13730839322111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345279753/10000000000 : ℝ)|^4163 ≤ (871483861237/2000000000000 : ℝ)^3139
        have hw : |(5345279753/10000000000 : ℝ)|=(5345279753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263750817/10000000000 : ℝ)|^4163 ≤ (21347483802681/50000000000000 : ℝ)^3139
        have hw : |(5263750817/10000000000 : ℝ)|=(5263750817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89508297/400000000 : ℝ)|^4163 ≤ (13730839322111/100000000000000 : ℝ)^3139
        have hw : |(-89508297/400000000 : ℝ)|=(89508297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365844793/10000000000 : ℝ)*x 0 + (4237313987/10000000000 : ℝ)*x 1 + (281141467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365844793/10000000000 : ℝ)^4163 ≤ (16657963271461/50000000000000 : ℝ)^3139 := by
    have hnat : (4365844793 : ℕ)^4163*50000000000000^3139 ≤ 16657963271461^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365844793 10000000000 16657963271461 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237313987/10000000000 : ℝ)^4163 ≤ (32021428444247/100000000000000 : ℝ)^3139 := by
    have hnat : (4237313987 : ℕ)^4163*100000000000000^3139 ≤ 32021428444247^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237313987 10000000000 32021428444247 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281141467/625000000 : ℝ)^4163 ≤ (34662645001099/100000000000000 : ℝ)^3139 := by
    have hnat : (281141467 : ℕ)^4163*100000000000000^3139 ≤ 34662645001099^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281141467 625000000 34662645001099 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365844793/10000000000 : ℝ), (4237313987/10000000000 : ℝ), (281141467/625000000 : ℝ)] ![(16657963271461/50000000000000 : ℝ), (32021428444247/100000000000000 : ℝ), (34662645001099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365844793/10000000000 : ℝ)|^4163 ≤ (16657963271461/50000000000000 : ℝ)^3139
        have hw : |(4365844793/10000000000 : ℝ)|=(4365844793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237313987/10000000000 : ℝ)|^4163 ≤ (32021428444247/100000000000000 : ℝ)^3139
        have hw : |(4237313987/10000000000 : ℝ)|=(4237313987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281141467/625000000 : ℝ)|^4163 ≤ (34662645001099/100000000000000 : ℝ)^3139
        have hw : |(281141467/625000000 : ℝ)|=(281141467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171035459/10000000000 : ℝ)*x 0 + (329005669/625000000 : ℝ)*x 1 + (674350851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171035459/10000000000 : ℝ)^4163 ≤ (13190928495869/100000000000000 : ℝ)^3139 := by
    have hnat : (2171035459 : ℕ)^4163*100000000000000^3139 ≤ 13190928495869^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171035459 10000000000 13190928495869 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329005669/625000000 : ℝ)^4163 ≤ (42698623852889/100000000000000 : ℝ)^3139 := by
    have hnat : (329005669 : ℕ)^4163*100000000000000^3139 ≤ 42698623852889^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329005669 625000000 42698623852889 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674350851/1250000000 : ℝ)^4163 ≤ (11027611908709/25000000000000 : ℝ)^3139 := by
    have hnat : (674350851 : ℕ)^4163*25000000000000^3139 ≤ 11027611908709^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674350851 1250000000 11027611908709 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171035459/10000000000 : ℝ), (329005669/625000000 : ℝ), (674350851/1250000000 : ℝ)] ![(13190928495869/100000000000000 : ℝ), (42698623852889/100000000000000 : ℝ), (11027611908709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171035459/10000000000 : ℝ)|^4163 ≤ (13190928495869/100000000000000 : ℝ)^3139
        have hw : |(-2171035459/10000000000 : ℝ)|=(2171035459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329005669/625000000 : ℝ)|^4163 ≤ (42698623852889/100000000000000 : ℝ)^3139
        have hw : |(329005669/625000000 : ℝ)|=(329005669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674350851/1250000000 : ℝ)|^4163 ≤ (11027611908709/25000000000000 : ℝ)^3139
        have hw : |(674350851/1250000000 : ℝ)|=(674350851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062402479/2000000000 : ℝ)*x 0 + (-2106651561/10000000000 : ℝ)*x 1 + (5394806797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062402479/2000000000 : ℝ)^4163 ≤ (43214898529739/100000000000000 : ℝ)^3139 := by
    have hnat : (1062402479 : ℕ)^4163*100000000000000^3139 ≤ 43214898529739^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062402479 2000000000 43214898529739 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106651561/10000000000 : ℝ)^4163 ≤ (12674653928299/100000000000000 : ℝ)^3139 := by
    have hnat : (2106651561 : ℕ)^4163*100000000000000^3139 ≤ 12674653928299^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106651561 10000000000 12674653928299 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394806797/10000000000 : ℝ)^4163 ≤ (8822089503111/20000000000000 : ℝ)^3139 := by
    have hnat : (5394806797 : ℕ)^4163*20000000000000^3139 ≤ 8822089503111^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394806797 10000000000 8822089503111 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062402479/2000000000 : ℝ), (-2106651561/10000000000 : ℝ), (5394806797/10000000000 : ℝ)] ![(43214898529739/100000000000000 : ℝ), (12674653928299/100000000000000 : ℝ), (8822089503111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062402479/2000000000 : ℝ)|^4163 ≤ (43214898529739/100000000000000 : ℝ)^3139
        have hw : |(1062402479/2000000000 : ℝ)|=(1062402479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106651561/10000000000 : ℝ)|^4163 ≤ (12674653928299/100000000000000 : ℝ)^3139
        have hw : |(-2106651561/10000000000 : ℝ)|=(2106651561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394806797/10000000000 : ℝ)|^4163 ≤ (8822089503111/20000000000000 : ℝ)^3139
        have hw : |(5394806797/10000000000 : ℝ)|=(5394806797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531201239/1000000000 : ℝ)*x 0 + (5394806799/10000000000 : ℝ)*x 1 + (-2106651567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531201239/1000000000 : ℝ)^4163 ≤ (43214898475793/100000000000000 : ℝ)^3139 := by
    have hnat : (531201239 : ℕ)^4163*100000000000000^3139 ≤ 43214898475793^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531201239 1000000000 43214898475793 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394806799/10000000000 : ℝ)^4163 ≤ (22055223768621/50000000000000 : ℝ)^3139 := by
    have hnat : (5394806799 : ℕ)^4163*50000000000000^3139 ≤ 22055223768621^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394806799 10000000000 22055223768621 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106651567/10000000000 : ℝ)^4163 ≤ (6337326988087/50000000000000 : ℝ)^3139 := by
    have hnat : (2106651567 : ℕ)^4163*50000000000000^3139 ≤ 6337326988087^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106651567 10000000000 6337326988087 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531201239/1000000000 : ℝ), (5394806799/10000000000 : ℝ), (-2106651567/10000000000 : ℝ)] ![(43214898475793/100000000000000 : ℝ), (22055223768621/50000000000000 : ℝ), (6337326988087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531201239/1000000000 : ℝ)|^4163 ≤ (43214898475793/100000000000000 : ℝ)^3139
        have hw : |(531201239/1000000000 : ℝ)|=(531201239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394806799/10000000000 : ℝ)|^4163 ≤ (22055223768621/50000000000000 : ℝ)^3139
        have hw : |(5394806799/10000000000 : ℝ)|=(5394806799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106651567/10000000000 : ℝ)|^4163 ≤ (6337326988087/50000000000000 : ℝ)^3139
        have hw : |(-2106651567/10000000000 : ℝ)|=(2106651567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s5_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873171071/2000000000 : ℝ)*x 0 + (1124397169/2500000000 : ℝ)*x 1 + (4237991367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873171071/2000000000 : ℝ)^4163 ≤ (26028151121/78125000000 : ℝ)^3139 := by
    have hnat : (873171071 : ℕ)^4163*78125000000^3139 ≤ 26028151121^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873171071 2000000000 26028151121 78125000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124397169/2500000000 : ℝ)^4163 ≤ (17327874528139/50000000000000 : ℝ)^3139 := by
    have hnat : (1124397169 : ℕ)^4163*50000000000000^3139 ≤ 17327874528139^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124397169 2500000000 17327874528139 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237991367/10000000000 : ℝ)^4163 ≤ (6405643498337/20000000000000 : ℝ)^3139 := by
    have hnat : (4237991367 : ℕ)^4163*20000000000000^3139 ≤ 6405643498337^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237991367 10000000000 6405643498337 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873171071/2000000000 : ℝ), (1124397169/2500000000 : ℝ), (4237991367/10000000000 : ℝ)] ![(26028151121/78125000000 : ℝ), (17327874528139/50000000000000 : ℝ), (6405643498337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873171071/2000000000 : ℝ)|^4163 ≤ (26028151121/78125000000 : ℝ)^3139
        have hw : |(873171071/2000000000 : ℝ)|=(873171071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124397169/2500000000 : ℝ)|^4163 ≤ (17327874528139/50000000000000 : ℝ)^3139
        have hw : |(1124397169/2500000000 : ℝ)|=(1124397169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237991367/10000000000 : ℝ)|^4163 ≤ (6405643498337/20000000000000 : ℝ)^3139
        have hw : |(4237991367/10000000000 : ℝ)|=(4237991367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (5579/50000 : ℝ) ^ (8325/2048 : ℝ) ≤ (13442942685147011/100000000000000000000 : ℝ) := by
    have hpowers : (5579/50000 : ℝ)^8325 ≤ (13442942685147011/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5579 : ℕ)^8325*100000000000000000000^2048 ≤ 13442942685147011^2048*50000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5579 50000 13442942685147011 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5579/50000 : ℝ)) (X := (13442942685147011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8325/2048 : ℝ) ≤ (3617826449714351/10000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8325 ≤ (3617826449714351/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8325*10000000000000000000^2048 ≤ 3617826449714351^2048*20000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 3617826449714351 10000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (3617826449714351/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013442942685147011/50000000000000000000 : ℝ) ≤ (1000066134189859/1000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50013442942685147011/50000000000000000000 : ℝ)^2048 ≤ (1000066134189859/1000000000000000 : ℝ)^8325 := by
      have hnat : (50013442942685147011 : ℕ)^2048*1000000000000000^8325 ≤ 1000066134189859^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013442942685147011 50000000000000000000 1000066134189859 1000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066134189859/1000000000000000 : ℝ)) (X := (50013442942685147011/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049621207182290521/100000000000000000000 : ℝ) ≤ (10001220483206377/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (100049621207182290521/100000000000000000000 : ℝ)^2048 ≤ (10001220483206377/10000000000000000 : ℝ)^8325 := by
      have hnat : (100049621207182290521 : ℕ)^2048*10000000000000000^8325 ≤ 10001220483206377^8325*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049621207182290521 100000000000000000000 10001220483206377 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001220483206377/10000000000000000 : ℝ)) (X := (100049621207182290521/100000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003617826449714351/5000000000000000000 : ℝ) ≤ (2500444906128541/2500000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (5003617826449714351/5000000000000000000 : ℝ)^2048 ≤ (2500444906128541/2500000000000000 : ℝ)^8325 := by
      have hnat : (5003617826449714351 : ℕ)^2048*2500000000000000^8325 ≤ 2500444906128541^8325*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003617826449714351 5000000000000000000 2500444906128541 2500000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500444906128541/2500000000000000 : ℝ)) (X := (5003617826449714351/5000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13442942685147011/100000000000000000000 : ℝ) ≤ ((15379778575798693369/15385000000000000000 : ℝ)+2*(559141307787/307700000000000 : ℝ)*(5579/50000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (15379778575798693369/15385000000000000000 : ℝ)+2*(559141307787/307700000000000 : ℝ)*(5579/50000 : ℝ)=(1000066134189859/1000000000000000 : ℝ) by norm_num, show 1+2*(13442942685147011/100000000000000000000 : ℝ)=(50013442942685147011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3617826449714351/10000000000000000000 : ℝ)+(13442942685147011/100000000000000000000 : ℝ) ≤ ((15379778575798693369/15385000000000000000 : ℝ)+(559141307787/307700000000000 : ℝ)*((2847/20000 : ℝ)+(5579/50000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (15379778575798693369/15385000000000000000 : ℝ)+(559141307787/307700000000000 : ℝ)*((2847/20000 : ℝ)+(5579/50000 : ℝ))=(10001220483206377/10000000000000000 : ℝ) by norm_num, show 1+(3617826449714351/10000000000000000000 : ℝ)+(13442942685147011/100000000000000000000 : ℝ)=(100049621207182290521/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3617826449714351/10000000000000000000 : ℝ) ≤ ((15379778575798693369/15385000000000000000 : ℝ)+2*(559141307787/307700000000000 : ℝ)*(2847/20000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (15379778575798693369/15385000000000000000 : ℝ)+2*(559141307787/307700000000000 : ℝ)*(2847/20000 : ℝ)=(2500444906128541/2500000000000000 : ℝ) by norm_num, show 1+2*(3617826449714351/10000000000000000000 : ℝ)=(5003617826449714351/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15379778575798693369/15385000000000000000 : ℝ)*(X 1 0+X 2 0)+(559141307787/307700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15379778575798693369/15385000000000000000 : ℝ)) (alpha := (559141307787/307700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15379778575798693369/15385000000000000000 : ℝ)*(X 0 1+X 2 1)+(559141307787/307700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15379778575798693369/15385000000000000000 : ℝ)) (alpha := (559141307787/307700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15379778575798693369/15385000000000000000 : ℝ)*(X 0 2+X 1 2)+(559141307787/307700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15379778575798693369/15385000000000000000 : ℝ)) (alpha := (559141307787/307700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-434205991/2000000000 : ℝ)*X 0 0+(269757393/500000000 : ℝ)*X 0 1+(1315937757/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345279483/10000000000 : ℝ)*X 1 0+(-447541497/2000000000 : ℝ)*X 1 1+(2631875521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345279753/10000000000 : ℝ)*X 2 0+(5263750817/10000000000 : ℝ)*X 2 1+(-89508297/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365844793/10000000000 : ℝ)*X 0 0+(4237313987/10000000000 : ℝ)*X 0 1+(281141467/625000000 : ℝ)*X 0 2+(4365844793/10000000000 : ℝ)*X 1 0+(4237313987/10000000000 : ℝ)*X 1 1+(281141467/625000000 : ℝ)*X 1 2+(4365844793/10000000000 : ℝ)*X 2 0+(4237313987/10000000000 : ℝ)*X 2 1+(281141467/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2171035459/10000000000 : ℝ)*X 0 0+(329005669/625000000 : ℝ)*X 0 1+(674350851/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062402479/2000000000 : ℝ)*X 1 0+(-2106651561/10000000000 : ℝ)*X 1 1+(5394806797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531201239/1000000000 : ℝ)*X 2 0+(5394806799/10000000000 : ℝ)*X 2 1+(-2106651567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873171071/2000000000 : ℝ)*X 0 0+(1124397169/2500000000 : ℝ)*X 0 1+(4237991367/10000000000 : ℝ)*X 0 2+(873171071/2000000000 : ℝ)*X 1 0+(1124397169/2500000000 : ℝ)*X 1 1+(4237991367/10000000000 : ℝ)*X 1 2+(873171071/2000000000 : ℝ)*X 2 0+(1124397169/2500000000 : ℝ)*X 2 1+(4237991367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298443919552400172747633069/45250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201927807/20000000000000 : ℝ)*(base19) + (523220057/50000000000000 : ℝ)*(base23) + (185814487/100000000000000 : ℝ)*(lower2) + (137665717/100000000000000 : ℝ)*(upper3) + (566847/1250000000000 : ℝ)*(upper5) + (5721385272215961/100000000000000 : ℝ)*(major0) + (5721385272215961/100000000000000 : ℝ)*(major1) + (5721385272215961/100000000000000 : ℝ)*(major2) + (761055554055263/10000000000000 : ℝ)*(sp0) + (3805290663541271/50000000000000 : ℝ)*(sp1) + (7610581290281463/100000000000000 : ℝ)*(sp2) + (3832170805890379/100000000000000 : ℝ)*(sp3) + (6699042237/25000000000000 : ℝ)*(sp4) + (17181971761/100000000000000 : ℝ)*(sp7) + (191609399393107/5000000000000 : ℝ)*(f.failure) + (3805291168360789/50000000000000 : ℝ)*(f.sum) + (2923662571229/905000000000000000000000000 : ℝ)*base66 + (1457883814936088977/90500000000000000000000000000000 : ℝ)*base67 + (170110195932911023/90500000000000000000000000000000 : ℝ)*base70 + (1533123543212588977/90500000000000000000000000000000 : ℝ)*base71 + (1284043660481/226250000000000000000000000 : ℝ)*base74 + (1419675507897088977/90500000000000000000000000000000 : ℝ)*base75 + (805851929983911023/90500000000000000000000000000000 : ℝ)*base78 + (3441275110786588977/90500000000000000000000000000000 : ℝ)*base79 + (69224484371/905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (741659/500000000000000000000 : ℝ)*base89 + (741659/500000000000000000000 : ℝ)*base91 + (741659/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2213182052763161421734954961/384625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1124255863/100000000000000 : ℝ)*(base19) + (599525931/50000000000000 : ℝ)*(base23) + (115594883/100000000000000 : ℝ)*(upper3) + (38398317/100000000000000 : ℝ)*(lower4) + (11818323/10000000000000 : ℝ)*(upper5) + (5751142800662477/100000000000000 : ℝ)*(major0) + (5751142800662477/100000000000000 : ℝ)*(major1) + (5751142800662477/100000000000000 : ℝ)*(major2) + (30043051609/100000000000000 : ℝ)*(sp1) + (31593419673/100000000000000 : ℝ)*(sp2) + (3825082903805639/50000000000000 : ℝ)*(sp4) + (3825067320151903/50000000000000 : ℝ)*(sp5) + (7650133015139743/100000000000000 : ℝ)*(sp6) + (77042392038187/2000000000000 : ℝ)*(sp7) + (77042392038187/2000000000000 : ℝ)*(f.failure) + (3825082903805639/50000000000000 : ℝ)*(f.sum) + (33544450468919/15385000000000000000000000000 : ℝ)*base65 + (9728203814594965013/1538500000000000000000000000000000 : ℝ)*base67 + (7514638073757965013/1538500000000000000000000000000000 : ℝ)*base69 + (2490788337577465013/1538500000000000000000000000000000 : ℝ)*base71 + (23556830068417/7692500000000000000000000000 : ℝ)*base73 + (17183625429321965013/1538500000000000000000000000000000 : ℝ)*base75 + (14520807508230465013/1538500000000000000000000000000000 : ℝ)*base77 + (5785685232166034987/1538500000000000000000000000000000 : ℝ)*base80 + (79811461022959/15385000000000000000000000000 : ℝ)*base81 + (2042381/200000000000000000000 : ℝ)*base90 + (2042381/200000000000000000000 : ℝ)*base92 + (2042381/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1133_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1133_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1133_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1133_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

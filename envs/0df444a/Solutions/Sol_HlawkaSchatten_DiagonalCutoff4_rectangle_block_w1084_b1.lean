-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:17.364544+00:00
-- url     : https://prove2.me/submissions/c5ecf779-448b-4a0c-991c-6e9aab13d853

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
theorem support_rectangle_w1084_s3_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190438013/10000000000 : ℝ)*x 0 + (1358865059/2500000000 : ℝ)*x 1 + (5226301927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190438013/10000000000 : ℝ)^8277 ≤ (3323897610997/25000000000000 : ℝ)^6229 := by
    have hnat : (2190438013 : ℕ)^8277*25000000000000^6229 ≤ 3323897610997^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190438013 10000000000 3323897610997 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358865059/2500000000 : ℝ)^8277 ≤ (8896436189031/20000000000000 : ℝ)^6229 := by
    have hnat : (1358865059 : ℕ)^8277*20000000000000^6229 ≤ 8896436189031^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358865059 2500000000 8896436189031 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226301927/10000000000 : ℝ)^8277 ≤ (4222222859127/10000000000000 : ℝ)^6229 := by
    have hnat : (5226301927 : ℕ)^8277*10000000000000^6229 ≤ 4222222859127^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226301927 10000000000 4222222859127 10000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190438013/10000000000 : ℝ), (1358865059/2500000000 : ℝ), (5226301927/10000000000 : ℝ)] ![(3323897610997/25000000000000 : ℝ), (8896436189031/20000000000000 : ℝ), (4222222859127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190438013/10000000000 : ℝ)|^8277 ≤ (3323897610997/25000000000000 : ℝ)^6229
        have hw : |(-2190438013/10000000000 : ℝ)|=(2190438013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358865059/2500000000 : ℝ)|^8277 ≤ (8896436189031/20000000000000 : ℝ)^6229
        have hw : |(1358865059/2500000000 : ℝ)|=(1358865059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226301927/10000000000 : ℝ)|^8277 ≤ (4222222859127/10000000000000 : ℝ)^6229
        have hw : |(5226301927/10000000000 : ℝ)|=(5226301927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355229013/10000000000 : ℝ)*x 0 + (-2297496139/10000000000 : ℝ)*x 1 + (52263019/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355229013/10000000000 : ℝ)^8277 ≤ (43611840513721/100000000000000 : ℝ)^6229 := by
    have hnat : (5355229013 : ℕ)^8277*100000000000000^6229 ≤ 43611840513721^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355229013 10000000000 43611840513721 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297496139/10000000000 : ℝ)^8277 ≤ (14165931173491/100000000000000 : ℝ)^6229 := by
    have hnat : (2297496139 : ℕ)^8277*100000000000000^6229 ≤ 14165931173491^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297496139 10000000000 14165931173491 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52263019/100000000 : ℝ)^8277 ≤ (1688889132057/4000000000000 : ℝ)^6229 := by
    have hnat : (52263019 : ℕ)^8277*4000000000000^6229 ≤ 1688889132057^6229*100000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52263019 100000000 1688889132057 4000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355229013/10000000000 : ℝ), (-2297496139/10000000000 : ℝ), (52263019/100000000 : ℝ)] ![(43611840513721/100000000000000 : ℝ), (14165931173491/100000000000000 : ℝ), (1688889132057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355229013/10000000000 : ℝ)|^8277 ≤ (43611840513721/100000000000000 : ℝ)^6229
        have hw : |(5355229013/10000000000 : ℝ)|=(5355229013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2297496139/10000000000 : ℝ)|^8277 ≤ (14165931173491/100000000000000 : ℝ)^6229
        have hw : |(-2297496139/10000000000 : ℝ)|=(2297496139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52263019/100000000 : ℝ)|^8277 ≤ (1688889132057/4000000000000 : ℝ)^6229
        have hw : |(52263019/100000000 : ℝ)|=(52263019/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355228933/10000000000 : ℝ)*x 0 + (2613151161/5000000000 : ℝ)*x 1 + (-574373923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355228933/10000000000 : ℝ)^8277 ≤ (21805919824007/50000000000000 : ℝ)^6229 := by
    have hnat : (5355228933 : ℕ)^8277*50000000000000^6229 ≤ 21805919824007^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355228933 10000000000 21805919824007 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613151161/5000000000 : ℝ)^8277 ≤ (42222232831587/100000000000000 : ℝ)^6229 := by
    have hnat : (2613151161 : ℕ)^8277*100000000000000^6229 ≤ 42222232831587^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613151161 5000000000 42222232831587 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574373923/2500000000 : ℝ)^8277 ≤ (14165927511203/100000000000000 : ℝ)^6229 := by
    have hnat : (574373923 : ℕ)^8277*100000000000000^6229 ≤ 14165927511203^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574373923 2500000000 14165927511203 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355228933/10000000000 : ℝ), (2613151161/5000000000 : ℝ), (-574373923/2500000000 : ℝ)] ![(21805919824007/50000000000000 : ℝ), (42222232831587/100000000000000 : ℝ), (14165927511203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355228933/10000000000 : ℝ)|^8277 ≤ (21805919824007/50000000000000 : ℝ)^6229
        have hw : |(5355228933/10000000000 : ℝ)|=(5355228933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613151161/5000000000 : ℝ)|^8277 ≤ (42222232831587/100000000000000 : ℝ)^6229
        have hw : |(2613151161/5000000000 : ℝ)|=(2613151161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-574373923/2500000000 : ℝ)|^8277 ≤ (14165927511203/100000000000000 : ℝ)^6229
        have hw : |(-574373923/2500000000 : ℝ)|=(574373923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370246821/10000000000 : ℝ)*x 0 + (2084714741/5000000000 : ℝ)*x 1 + (4580814871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370246821/10000000000 : ℝ)^8277 ≤ (33289695394709/100000000000000 : ℝ)^6229 := by
    have hnat : (4370246821 : ℕ)^8277*100000000000000^6229 ≤ 33289695394709^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370246821 10000000000 33289695394709 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084714741/5000000000 : ℝ)^8277 ≤ (15636287271049/50000000000000 : ℝ)^6229 := by
    have hnat : (2084714741 : ℕ)^8277*50000000000000^6229 ≤ 15636287271049^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084714741 5000000000 15636287271049 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4580814871/10000000000 : ℝ)^8277 ≤ (17718865026779/50000000000000 : ℝ)^6229 := by
    have hnat : (4580814871 : ℕ)^8277*50000000000000^6229 ≤ 17718865026779^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580814871 10000000000 17718865026779 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370246821/10000000000 : ℝ), (2084714741/5000000000 : ℝ), (4580814871/10000000000 : ℝ)] ![(33289695394709/100000000000000 : ℝ), (15636287271049/50000000000000 : ℝ), (17718865026779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370246821/10000000000 : ℝ)|^8277 ≤ (33289695394709/100000000000000 : ℝ)^6229
        have hw : |(4370246821/10000000000 : ℝ)|=(4370246821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084714741/5000000000 : ℝ)|^8277 ≤ (15636287271049/50000000000000 : ℝ)^6229
        have hw : |(2084714741/5000000000 : ℝ)|=(2084714741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4580814871/10000000000 : ℝ)|^8277 ≤ (17718865026779/50000000000000 : ℝ)^6229
        have hw : |(4580814871/10000000000 : ℝ)|=(4580814871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095229677/5000000000 : ℝ)*x 0 + (5227148139/10000000000 : ℝ)*x 1 + (2717304499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095229677/5000000000 : ℝ)^8277 ≤ (830985160631/6250000000000 : ℝ)^6229 := by
    have hnat : (1095229677 : ℕ)^8277*6250000000000^6229 ≤ 830985160631^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095229677 5000000000 830985160631 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227148139/10000000000 : ℝ)^8277 ≤ (1689252516113/4000000000000 : ℝ)^6229 := by
    have hnat : (5227148139 : ℕ)^8277*4000000000000^6229 ≤ 1689252516113^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227148139 10000000000 1689252516113 4000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717304499/5000000000 : ℝ)^8277 ≤ (8894584900159/20000000000000 : ℝ)^6229 := by
    have hnat : (2717304499 : ℕ)^8277*20000000000000^6229 ≤ 8894584900159^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717304499 5000000000 8894584900159 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095229677/5000000000 : ℝ), (5227148139/10000000000 : ℝ), (2717304499/5000000000 : ℝ)] ![(830985160631/6250000000000 : ℝ), (1689252516113/4000000000000 : ℝ), (8894584900159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095229677/5000000000 : ℝ)|^8277 ≤ (830985160631/6250000000000 : ℝ)^6229
        have hw : |(-1095229677/5000000000 : ℝ)|=(1095229677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227148139/10000000000 : ℝ)|^8277 ≤ (1689252516113/4000000000000 : ℝ)^6229
        have hw : |(5227148139/10000000000 : ℝ)|=(5227148139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717304499/5000000000 : ℝ)|^8277 ≤ (8894584900159/20000000000000 : ℝ)^6229
        have hw : |(2717304499/5000000000 : ℝ)|=(2717304499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060493847/2000000000 : ℝ)*x 0 + (-261148611/1250000000 : ℝ)*x 1 + (2717304649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060493847/2000000000 : ℝ)^8277 ≤ (43041835809133/100000000000000 : ℝ)^6229 := by
    have hnat : (1060493847 : ℕ)^8277*100000000000000^6229 ≤ 43041835809133^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060493847 2000000000 43041835809133 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261148611/1250000000 : ℝ)^8277 ≤ (2497047283147/20000000000000 : ℝ)^6229 := by
    have hnat : (261148611 : ℕ)^8277*20000000000000^6229 ≤ 2497047283147^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261148611 1250000000 2497047283147 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717304649/5000000000 : ℝ)^8277 ≤ (2223646388147/5000000000000 : ℝ)^6229 := by
    have hnat : (2717304649 : ℕ)^8277*5000000000000^6229 ≤ 2223646388147^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717304649 5000000000 2223646388147 5000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060493847/2000000000 : ℝ), (-261148611/1250000000 : ℝ), (2717304649/5000000000 : ℝ)] ![(43041835809133/100000000000000 : ℝ), (2497047283147/20000000000000 : ℝ), (2223646388147/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060493847/2000000000 : ℝ)|^8277 ≤ (43041835809133/100000000000000 : ℝ)^6229
        have hw : |(1060493847/2000000000 : ℝ)|=(1060493847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261148611/1250000000 : ℝ)|^8277 ≤ (2497047283147/20000000000000 : ℝ)^6229
        have hw : |(-261148611/1250000000 : ℝ)|=(261148611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717304649/5000000000 : ℝ)|^8277 ≤ (2223646388147/5000000000000 : ℝ)^6229
        have hw : |(2717304649/5000000000 : ℝ)|=(2717304649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325617351/2500000000 : ℝ)*x 0 + (5434609029/10000000000 : ℝ)*x 1 + (-2089189027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325617351/2500000000 : ℝ)^8277 ≤ (10760459407999/25000000000000 : ℝ)^6229 := by
    have hnat : (1325617351 : ℕ)^8277*25000000000000^6229 ≤ 10760459407999^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325617351 2500000000 10760459407999 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434609029/10000000000 : ℝ)^8277 ≤ (11118231209471/25000000000000 : ℝ)^6229 := by
    have hnat : (5434609029 : ℕ)^8277*25000000000000^6229 ≤ 11118231209471^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434609029 10000000000 11118231209471 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089189027/10000000000 : ℝ)^8277 ≤ (1248523751953/10000000000000 : ℝ)^6229 := by
    have hnat : (2089189027 : ℕ)^8277*10000000000000^6229 ≤ 1248523751953^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089189027 10000000000 1248523751953 10000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325617351/2500000000 : ℝ), (5434609029/10000000000 : ℝ), (-2089189027/10000000000 : ℝ)] ![(10760459407999/25000000000000 : ℝ), (11118231209471/25000000000000 : ℝ), (1248523751953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325617351/2500000000 : ℝ)|^8277 ≤ (10760459407999/25000000000000 : ℝ)^6229
        have hw : |(1325617351/2500000000 : ℝ)|=(1325617351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434609029/10000000000 : ℝ)|^8277 ≤ (11118231209471/25000000000000 : ℝ)^6229
        have hw : |(5434609029/10000000000 : ℝ)|=(5434609029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089189027/10000000000 : ℝ)|^8277 ≤ (1248523751953/10000000000000 : ℝ)^6229
        have hw : |(-2089189027/10000000000 : ℝ)|=(2089189027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s3_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370288313/10000000000 : ℝ)*x 0 + (286196967/625000000 : ℝ)*x 1 + (1042775699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370288313/10000000000 : ℝ)^8277 ≤ (16645057684897/50000000000000 : ℝ)^6229 := by
    have hnat : (4370288313 : ℕ)^8277*50000000000000^6229 ≤ 16645057684897^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370288313 10000000000 16645057684897 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286196967/625000000 : ℝ)^8277 ≤ (8855157984111/25000000000000 : ℝ)^6229 := by
    have hnat : (286196967 : ℕ)^8277*25000000000000^6229 ≤ 8855157984111^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286196967 625000000 8855157984111 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042775699/2500000000 : ℝ)^8277 ≤ (31289252686191/100000000000000 : ℝ)^6229 := by
    have hnat : (1042775699 : ℕ)^8277*100000000000000^6229 ≤ 31289252686191^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042775699 2500000000 31289252686191 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370288313/10000000000 : ℝ), (286196967/625000000 : ℝ), (1042775699/2500000000 : ℝ)] ![(16645057684897/50000000000000 : ℝ), (8855157984111/25000000000000 : ℝ), (31289252686191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370288313/10000000000 : ℝ)|^8277 ≤ (16645057684897/50000000000000 : ℝ)^6229
        have hw : |(4370288313/10000000000 : ℝ)|=(4370288313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(286196967/625000000 : ℝ)|^8277 ≤ (8855157984111/25000000000000 : ℝ)^6229
        have hw : |(286196967/625000000 : ℝ)|=(286196967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042775699/2500000000 : ℝ)|^8277 ≤ (31289252686191/100000000000000 : ℝ)^6229
        have hw : |(1042775699/2500000000 : ℝ)|=(1042775699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2091/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (93/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8799/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8799/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8799/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8799/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8799/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8799/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8799/100000 : ℝ) ^ (2069/512 : ℝ) ≤ (2712742353118321/50000000000000000000 : ℝ) := by
    have hpowers : (8799/100000 : ℝ)^2069 ≤ (2712742353118321/50000000000000000000 : ℝ)^512 := by
      have hnat : (8799 : ℕ)^2069*50000000000000000000^512 ≤ 2712742353118321^512*100000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8799 100000 2712742353118321 50000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8799/100000 : ℝ)) (X := (2712742353118321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8341/50000 : ℝ) ^ (2069/512 : ℝ) ≤ (71960220900339191/100000000000000000000 : ℝ) := by
    have hpowers : (8341/50000 : ℝ)^2069 ≤ (71960220900339191/100000000000000000000 : ℝ)^512 := by
      have hnat : (8341 : ℕ)^2069*100000000000000000000^512 ≤ 71960220900339191^512*50000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8341 50000 71960220900339191 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8341/50000 : ℝ)) (X := (71960220900339191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002712742353118321/25000000000000000000 : ℝ) ≤ (10000268509885023/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (25002712742353118321/25000000000000000000 : ℝ)^512 ≤ (10000268509885023/10000000000000000 : ℝ)^2069 := by
      have hnat : (25002712742353118321 : ℕ)^512*10000000000000000^2069 ≤ 10000268509885023^2069*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002712742353118321 25000000000000000000 10000268509885023 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000268509885023/10000000000000000 : ℝ)) (X := (25002712742353118321/25000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077385705606575833/100000000000000000000 : ℝ) ≤ (5000957224494231/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (100077385705606575833/100000000000000000000 : ℝ)^512 ≤ (5000957224494231/5000000000000000 : ℝ)^2069 := by
      have hnat : (100077385705606575833 : ℕ)^512*5000000000000000^2069 ≤ 5000957224494231^2069*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077385705606575833 100000000000000000000 5000957224494231 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000957224494231/5000000000000000 : ℝ)) (X := (100077385705606575833/100000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50071960220900339191/50000000000000000000 : ℝ) ≤ (10003560388091901/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50071960220900339191/50000000000000000000 : ℝ)^512 ≤ (10003560388091901/10000000000000000 : ℝ)^2069 := by
      have hnat : (50071960220900339191 : ℕ)^512*10000000000000000^2069 ≤ 10003560388091901^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071960220900339191 50000000000000000000 10003560388091901 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003560388091901/10000000000000000 : ℝ)) (X := (50071960220900339191/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2712742353118321/50000000000000000000 : ℝ) ≤ ((78803151427081316787/78830000000000000000 : ℝ)+2*(1645939103439/788300000000000 : ℝ)*(8799/100000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (78803151427081316787/78830000000000000000 : ℝ)+2*(1645939103439/788300000000000 : ℝ)*(8799/100000 : ℝ)=(10000268509885023/10000000000000000 : ℝ) by norm_num, show 1+2*(2712742353118321/50000000000000000000 : ℝ)=(25002712742353118321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71960220900339191/100000000000000000000 : ℝ)+(2712742353118321/50000000000000000000 : ℝ) ≤ ((78803151427081316787/78830000000000000000 : ℝ)+(1645939103439/788300000000000 : ℝ)*((8341/50000 : ℝ)+(8799/100000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (78803151427081316787/78830000000000000000 : ℝ)+(1645939103439/788300000000000 : ℝ)*((8341/50000 : ℝ)+(8799/100000 : ℝ))=(5000957224494231/5000000000000000 : ℝ) by norm_num, show 1+(71960220900339191/100000000000000000000 : ℝ)+(2712742353118321/50000000000000000000 : ℝ)=(100077385705606575833/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71960220900339191/100000000000000000000 : ℝ) ≤ ((78803151427081316787/78830000000000000000 : ℝ)+2*(1645939103439/788300000000000 : ℝ)*(8341/50000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (78803151427081316787/78830000000000000000 : ℝ)+2*(1645939103439/788300000000000 : ℝ)*(8341/50000 : ℝ)=(10003560388091901/10000000000000000 : ℝ) by norm_num, show 1+2*(71960220900339191/100000000000000000000 : ℝ)=(50071960220900339191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (78803151427081316787/78830000000000000000 : ℝ)*(X 1 0+X 2 0)+(1645939103439/788300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (8799/100000 : ℝ)) (hi := (8341/50000 : ℝ)) (c := (78803151427081316787/78830000000000000000 : ℝ)) (alpha := (1645939103439/788300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (78803151427081316787/78830000000000000000 : ℝ)*(X 0 1+X 2 1)+(1645939103439/788300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (8799/100000 : ℝ)) (hi := (8341/50000 : ℝ)) (c := (78803151427081316787/78830000000000000000 : ℝ)) (alpha := (1645939103439/788300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (78803151427081316787/78830000000000000000 : ℝ)*(X 0 2+X 1 2)+(1645939103439/788300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (8799/100000 : ℝ)) (hi := (8341/50000 : ℝ)) (c := (78803151427081316787/78830000000000000000 : ℝ)) (alpha := (1645939103439/788300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190438013/10000000000 : ℝ)*X 0 0+(1358865059/2500000000 : ℝ)*X 0 1+(5226301927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355229013/10000000000 : ℝ)*X 1 0+(-2297496139/10000000000 : ℝ)*X 1 1+(52263019/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355228933/10000000000 : ℝ)*X 2 0+(2613151161/5000000000 : ℝ)*X 2 1+(-574373923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370246821/10000000000 : ℝ)*X 0 0+(2084714741/5000000000 : ℝ)*X 0 1+(4580814871/10000000000 : ℝ)*X 0 2+(4370246821/10000000000 : ℝ)*X 1 0+(2084714741/5000000000 : ℝ)*X 1 1+(4580814871/10000000000 : ℝ)*X 1 2+(4370246821/10000000000 : ℝ)*X 2 0+(2084714741/5000000000 : ℝ)*X 2 1+(4580814871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1095229677/5000000000 : ℝ)*X 0 0+(5227148139/10000000000 : ℝ)*X 0 1+(2717304499/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060493847/2000000000 : ℝ)*X 1 0+(-261148611/1250000000 : ℝ)*X 1 1+(2717304649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325617351/2500000000 : ℝ)*X 2 0+(5434609029/10000000000 : ℝ)*X 2 1+(-2089189027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370288313/10000000000 : ℝ)*X 0 0+(286196967/625000000 : ℝ)*X 0 1+(1042775699/2500000000 : ℝ)*X 0 2+(4370288313/10000000000 : ℝ)*X 1 0+(286196967/625000000 : ℝ)*X 1 1+(1042775699/2500000000 : ℝ)*X 1 2+(4370288313/10000000000 : ℝ)*X 2 0+(286196967/625000000 : ℝ)*X 2 1+(1042775699/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21639989173455830689093921461/3941500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97676899/6250000000000 : ℝ)*(base19) + (110871467/10000000000000 : ℝ)*(base23) + (102470181/50000000000000 : ℝ)*(lower2) + (20369609/50000000000000 : ℝ)*(upper3) + (35128439/20000000000000 : ℝ)*(upper5) + (3605980579335101/100000000000000 : ℝ)*(major0) + (3605980579335101/100000000000000 : ℝ)*(major1) + (3605980579335101/100000000000000 : ℝ)*(major2) + (4781093332821563/100000000000000 : ℝ)*(sp0) + (2390562504685491/50000000000000 : ℝ)*(sp1) + (597640682935837/12500000000000 : ℝ)*(sp2) + (486164561660617/20000000000000 : ℝ)*(sp3) + (16619689901/50000000000000 : ℝ)*(sp4) + (5797577993/50000000000000 : ℝ)*(sp7) + (2430834403459071/100000000000000 : ℝ)*(f.failure) + (956225314440273/20000000000000 : ℝ)*(f.sum) + (63850329604701/39415000000000000000000000000 : ℝ)*base66 + (20592817733920459513/7883000000000000000000000000000000 : ℝ)*base68 + (38179818166760459513/7883000000000000000000000000000000 : ℝ)*base70 + (20778970529983459513/7883000000000000000000000000000000 : ℝ)*base72 + (80970916497779/39415000000000000000000000000 : ℝ)*base73 + (8418522203090540487/7883000000000000000000000000000000 : ℝ)*base75 + (59682222382450540487/7883000000000000000000000000000000 : ℝ)*base77 + (41187555422298459513/7883000000000000000000000000000000 : ℝ)*base80 + (9817131651927/19707500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (257957/400000000000000000000 : ℝ)*base90 + (257957/400000000000000000000 : ℝ)*base92 + (257957/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185529363693133828549666653/61585937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (134233683/25000000000000 : ℝ)*(base19) + (52886893/6250000000000 : ℝ)*(base23) + (23259459/20000000000000 : ℝ)*(upper3) + (69871923/100000000000000 : ℝ)*(lower4) + (28401851680437/781250000000 : ℝ)*(major0) + (28401851680437/781250000000 : ℝ)*(major1) + (28401851680437/781250000000 : ℝ)*(major2) + (13126747777/100000000000000 : ℝ)*(sp1) + (15524255559/100000000000000 : ℝ)*(sp2) + (436752113/50000000000000 : ℝ)*(sp3) + (2410091296284943/50000000000000 : ℝ)*(sp4) + (4820168928887377/100000000000000 : ℝ)*(sp5) + (120504155553101/2500000000000 : ℝ)*(sp6) + (306336307962519/12500000000000 : ℝ)*(sp7) + (1225345668602189/50000000000000 : ℝ)*(f.failure) + (2410091296284943/50000000000000 : ℝ)*(f.sum) + (131606038720733/19707500000000000000000000000 : ℝ)*base66 + (55399350369091103/30792968750000000000000000000000 : ℝ)*base68 + (40869015538818989/15396484375000000000000000000000 : ℝ)*base70 + (86426809412979807/7698242187500000000000000000000 : ℝ)*base72 + (124319112641351/39415000000000000000000000000 : ℝ)*base74 + (625102711640864669/61585937500000000000000000000000 : ℝ)*base75 + (371558296962567537/123171875000000000000000000000000 : ℝ)*base78 + (74148036264667307/7698242187500000000000000000000 : ℝ)*base80 + (80434203476023/19707500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (741537/200000000000000000000 : ℝ)*base89 + (741537/200000000000000000000 : ℝ)*base91 + (741537/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (93/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_s4_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548486101/2500000000 : ℝ)*x 0 + (540482999/1000000000 : ℝ)*x 1 + (1313660189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548486101/2500000000 : ℝ)^8277 ≤ (1665484834937/12500000000000 : ℝ)^6229 := by
    have hnat : (548486101 : ℕ)^8277*12500000000000^6229 ≤ 1665484834937^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548486101 2500000000 1665484834937 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540482999/1000000000 : ℝ)^8277 ≤ (44149405069203/100000000000000 : ℝ)^6229 := by
    have hnat : (540482999 : ℕ)^8277*100000000000000^6229 ≤ 44149405069203^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540482999 1000000000 44149405069203 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313660189/2500000000 : ℝ)^8277 ≤ (5315839528927/12500000000000 : ℝ)^6229 := by
    have hnat : (1313660189 : ℕ)^8277*12500000000000^6229 ≤ 5315839528927^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313660189 2500000000 5315839528927 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548486101/2500000000 : ℝ), (540482999/1000000000 : ℝ), (1313660189/2500000000 : ℝ)] ![(1665484834937/12500000000000 : ℝ), (44149405069203/100000000000000 : ℝ), (5315839528927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548486101/2500000000 : ℝ)|^8277 ≤ (1665484834937/12500000000000 : ℝ)^6229
        have hw : |(-548486101/2500000000 : ℝ)|=(548486101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540482999/1000000000 : ℝ)|^8277 ≤ (44149405069203/100000000000000 : ℝ)^6229
        have hw : |(540482999/1000000000 : ℝ)|=(540482999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313660189/2500000000 : ℝ)|^8277 ≤ (5315839528927/12500000000000 : ℝ)^6229
        have hw : |(1313660189/2500000000 : ℝ)|=(1313660189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347626513/10000000000 : ℝ)*x 0 + (-1135158617/5000000000 : ℝ)*x 1 + (1050928257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347626513/10000000000 : ℝ)^8277 ≤ (43529590491941/100000000000000 : ℝ)^6229 := by
    have hnat : (5347626513 : ℕ)^8277*100000000000000^6229 ≤ 43529590491941^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347626513 10000000000 43529590491941 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135158617/5000000000 : ℝ)^8277 ≤ (13943687575501/100000000000000 : ℝ)^6229 := by
    have hnat : (1135158617 : ℕ)^8277*100000000000000^6229 ≤ 13943687575501^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135158617 5000000000 13943687575501 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050928257/2000000000 : ℝ)^8277 ≤ (21263360960163/50000000000000 : ℝ)^6229 := by
    have hnat : (1050928257 : ℕ)^8277*50000000000000^6229 ≤ 21263360960163^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050928257 2000000000 21263360960163 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347626513/10000000000 : ℝ), (-1135158617/5000000000 : ℝ), (1050928257/2000000000 : ℝ)] ![(43529590491941/100000000000000 : ℝ), (13943687575501/100000000000000 : ℝ), (21263360960163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347626513/10000000000 : ℝ)|^8277 ≤ (43529590491941/100000000000000 : ℝ)^6229
        have hw : |(5347626513/10000000000 : ℝ)|=(5347626513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135158617/5000000000 : ℝ)|^8277 ≤ (13943687575501/100000000000000 : ℝ)^6229
        have hw : |(-1135158617/5000000000 : ℝ)|=(1135158617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050928257/2000000000 : ℝ)|^8277 ≤ (21263360960163/50000000000000 : ℝ)^6229
        have hw : |(1050928257/2000000000 : ℝ)|=(1050928257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347626843/10000000000 : ℝ)*x 0 + (5254640949/10000000000 : ℝ)*x 1 + (-1135158619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347626843/10000000000 : ℝ)^8277 ≤ (8705918812263/20000000000000 : ℝ)^6229 := by
    have hnat : (5347626843 : ℕ)^8277*20000000000000^6229 ≤ 8705918812263^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347626843 10000000000 8705918812263 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254640949/10000000000 : ℝ)^8277 ≤ (21263359153477/50000000000000 : ℝ)^6229 := by
    have hnat : (5254640949 : ℕ)^8277*50000000000000^6229 ≤ 21263359153477^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254640949 10000000000 21263359153477 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135158619/5000000000 : ℝ)^8277 ≤ (6971843804073/50000000000000 : ℝ)^6229 := by
    have hnat : (1135158619 : ℕ)^8277*50000000000000^6229 ≤ 6971843804073^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135158619 5000000000 6971843804073 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347626843/10000000000 : ℝ), (5254640949/10000000000 : ℝ), (-1135158619/5000000000 : ℝ)] ![(8705918812263/20000000000000 : ℝ), (21263359153477/50000000000000 : ℝ), (6971843804073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347626843/10000000000 : ℝ)|^8277 ≤ (8705918812263/20000000000000 : ℝ)^6229
        have hw : |(5347626843/10000000000 : ℝ)|=(5347626843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254640949/10000000000 : ℝ)|^8277 ≤ (21263359153477/50000000000000 : ℝ)^6229
        have hw : |(5254640949/10000000000 : ℝ)|=(5254640949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135158619/5000000000 : ℝ)|^8277 ≤ (6971843804073/50000000000000 : ℝ)^6229
        have hw : |(-1135158619/5000000000 : ℝ)|=(1135158619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437233387/1000000000 : ℝ)*x 0 + (1056787089/2500000000 : ℝ)*x 1 + (90451001/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437233387/1000000000 : ℝ)^8277 ≤ (4163852722621/12500000000000 : ℝ)^6229 := by
    have hnat : (437233387 : ℕ)^8277*12500000000000^6229 ≤ 4163852722621^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437233387 1000000000 4163852722621 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056787089/2500000000 : ℝ)^8277 ≤ (31849133414989/100000000000000 : ℝ)^6229 := by
    have hnat : (1056787089 : ℕ)^8277*100000000000000^6229 ≤ 31849133414989^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056787089 2500000000 31849133414989 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90451001/200000000 : ℝ)^8277 ≤ (6968008957421/20000000000000 : ℝ)^6229 := by
    have hnat : (90451001 : ℕ)^8277*20000000000000^6229 ≤ 6968008957421^6229*200000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90451001 200000000 6968008957421 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437233387/1000000000 : ℝ), (1056787089/2500000000 : ℝ), (90451001/200000000 : ℝ)] ![(4163852722621/12500000000000 : ℝ), (31849133414989/100000000000000 : ℝ), (6968008957421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437233387/1000000000 : ℝ)|^8277 ≤ (4163852722621/12500000000000 : ℝ)^6229
        have hw : |(437233387/1000000000 : ℝ)|=(437233387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056787089/2500000000 : ℝ)|^8277 ≤ (31849133414989/100000000000000 : ℝ)^6229
        have hw : |(1056787089/2500000000 : ℝ)|=(1056787089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90451001/200000000 : ℝ)|^8277 ≤ (6968008957421/20000000000000 : ℝ)^6229
        have hw : |(90451001/200000000 : ℝ)|=(90451001/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096975697/5000000000 : ℝ)*x 0 + (1051015657/2000000000 : ℝ)*x 1 + (675548911/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096975697/5000000000 : ℝ)^8277 ≤ (6661967543513/50000000000000 : ℝ)^6229 := by
    have hnat : (1096975697 : ℕ)^8277*50000000000000^6229 ≤ 6661967543513^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096975697 5000000000 6661967543513 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051015657/2000000000 : ℝ)^8277 ≤ (42531421519647/100000000000000 : ℝ)^6229 := by
    have hnat : (1051015657 : ℕ)^8277*100000000000000^6229 ≤ 42531421519647^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051015657 2000000000 42531421519647 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675548911/1250000000 : ℝ)^8277 ≤ (1379520105551/3125000000000 : ℝ)^6229 := by
    have hnat : (675548911 : ℕ)^8277*3125000000000^6229 ≤ 1379520105551^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675548911 1250000000 1379520105551 3125000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096975697/5000000000 : ℝ), (1051015657/2000000000 : ℝ), (675548911/1250000000 : ℝ)] ![(6661967543513/50000000000000 : ℝ), (42531421519647/100000000000000 : ℝ), (1379520105551/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096975697/5000000000 : ℝ)|^8277 ≤ (6661967543513/50000000000000 : ℝ)^6229
        have hw : |(-1096975697/5000000000 : ℝ)|=(1096975697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051015657/2000000000 : ℝ)|^8277 ≤ (42531421519647/100000000000000 : ℝ)^6229
        have hw : |(1051015657/2000000000 : ℝ)|=(1051015657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675548911/1250000000 : ℝ)|^8277 ≤ (1379520105551/3125000000000 : ℝ)^6229
        have hw : |(675548911/1250000000 : ℝ)|=(675548911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309745469/10000000000 : ℝ)*x 0 + (-1060283377/5000000000 : ℝ)*x 1 + (2702195647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309745469/10000000000 : ℝ)^8277 ≤ (43120336203743/100000000000000 : ℝ)^6229 := by
    have hnat : (5309745469 : ℕ)^8277*100000000000000^6229 ≤ 43120336203743^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309745469 10000000000 43120336203743 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060283377/5000000000 : ℝ)^8277 ≤ (1591877542641/12500000000000 : ℝ)^6229 := by
    have hnat : (1060283377 : ℕ)^8277*12500000000000^6229 ≤ 1591877542641^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060283377 5000000000 1591877542641 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702195647/5000000000 : ℝ)^8277 ≤ (8828928688551/20000000000000 : ℝ)^6229 := by
    have hnat : (2702195647 : ℕ)^8277*20000000000000^6229 ≤ 8828928688551^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702195647 5000000000 8828928688551 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309745469/10000000000 : ℝ), (-1060283377/5000000000 : ℝ), (2702195647/5000000000 : ℝ)] ![(43120336203743/100000000000000 : ℝ), (1591877542641/12500000000000 : ℝ), (8828928688551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309745469/10000000000 : ℝ)|^8277 ≤ (43120336203743/100000000000000 : ℝ)^6229
        have hw : |(5309745469/10000000000 : ℝ)|=(5309745469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060283377/5000000000 : ℝ)|^8277 ≤ (1591877542641/12500000000000 : ℝ)^6229
        have hw : |(-1060283377/5000000000 : ℝ)|=(1060283377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702195647/5000000000 : ℝ)|^8277 ≤ (8828928688551/20000000000000 : ℝ)^6229
        have hw : |(2702195647/5000000000 : ℝ)|=(2702195647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66371817/125000000 : ℝ)*x 0 + (540439121/1000000000 : ℝ)*x 1 + (-265070877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66371817/125000000 : ℝ)^8277 ≤ (134751046961/312500000000 : ℝ)^6229 := by
    have hnat : (66371817 : ℕ)^8277*312500000000^6229 ≤ 134751046961^6229*125000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66371817 125000000 134751046961 312500000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540439121/1000000000 : ℝ)^8277 ≤ (44144642531027/100000000000000 : ℝ)^6229 := by
    have hnat : (540439121 : ℕ)^8277*100000000000000^6229 ≤ 44144642531027^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540439121 1000000000 44144642531027 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265070877/1250000000 : ℝ)^8277 ≤ (2547004486377/20000000000000 : ℝ)^6229 := by
    have hnat : (265070877 : ℕ)^8277*20000000000000^6229 ≤ 2547004486377^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265070877 1250000000 2547004486377 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66371817/125000000 : ℝ), (540439121/1000000000 : ℝ), (-265070877/1250000000 : ℝ)] ![(134751046961/312500000000 : ℝ), (44144642531027/100000000000000 : ℝ), (2547004486377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66371817/125000000 : ℝ)|^8277 ≤ (134751046961/312500000000 : ℝ)^6229
        have hw : |(66371817/125000000 : ℝ)|=(66371817/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540439121/1000000000 : ℝ)|^8277 ≤ (44144642531027/100000000000000 : ℝ)^6229
        have hw : |(540439121/1000000000 : ℝ)|=(540439121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265070877/1250000000 : ℝ)|^8277 ≤ (2547004486377/20000000000000 : ℝ)^6229
        have hw : |(-265070877/1250000000 : ℝ)|=(265070877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s4_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372349189/10000000000 : ℝ)*x 0 + (4521690419/10000000000 : ℝ)*x 1 + (2114005873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372349189/10000000000 : ℝ)^8277 ≤ (16655488430757/50000000000000 : ℝ)^6229 := by
    have hnat : (4372349189 : ℕ)^8277*50000000000000^6229 ≤ 16655488430757^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372349189 10000000000 16655488430757 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521690419/10000000000 : ℝ)^8277 ≤ (2176952842539/6250000000000 : ℝ)^6229 := by
    have hnat : (4521690419 : ℕ)^8277*6250000000000^6229 ≤ 2176952842539^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521690419 10000000000 2176952842539 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114005873/5000000000 : ℝ)^8277 ≤ (7964444411427/25000000000000 : ℝ)^6229 := by
    have hnat : (2114005873 : ℕ)^8277*25000000000000^6229 ≤ 7964444411427^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114005873 5000000000 7964444411427 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372349189/10000000000 : ℝ), (4521690419/10000000000 : ℝ), (2114005873/5000000000 : ℝ)] ![(16655488430757/50000000000000 : ℝ), (2176952842539/6250000000000 : ℝ), (7964444411427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372349189/10000000000 : ℝ)|^8277 ≤ (16655488430757/50000000000000 : ℝ)^6229
        have hw : |(4372349189/10000000000 : ℝ)|=(4372349189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521690419/10000000000 : ℝ)|^8277 ≤ (2176952842539/6250000000000 : ℝ)^6229
        have hw : |(4521690419/10000000000 : ℝ)|=(4521690419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114005873/5000000000 : ℝ)|^8277 ≤ (7964444411427/25000000000000 : ℝ)^6229
        have hw : |(2114005873/5000000000 : ℝ)|=(2114005873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (93/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (553/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (93/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2091/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (93/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2091/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (93/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2091/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (93/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2091/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (93/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2091/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (93/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2091/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2091/20000 : ℝ) ^ (2069/512 : ℝ) ≤ (10891134241282173/100000000000000000000 : ℝ) := by
    have hpowers : (2091/20000 : ℝ)^2069 ≤ (10891134241282173/100000000000000000000 : ℝ)^512 := by
      have hnat : (2091 : ℕ)^2069*100000000000000000000^512 ≤ 10891134241282173^512*20000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2091 20000 10891134241282173 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2091/20000 : ℝ)) (X := (10891134241282173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (93/625 : ℝ) ^ (2069/512 : ℝ) ≤ (45339373729067361/100000000000000000000 : ℝ) := by
    have hpowers : (93/625 : ℝ)^2069 ≤ (45339373729067361/100000000000000000000 : ℝ)^512 := by
      have hnat : (93 : ℕ)^2069*100000000000000000000^512 ≤ 45339373729067361^512*625^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93 625 45339373729067361 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93/625 : ℝ)) (X := (45339373729067361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010891134241282173/50000000000000000000 : ℝ) ≤ (2500134746345097/2500000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50010891134241282173/50000000000000000000 : ℝ)^512 ≤ (2500134746345097/2500000000000000 : ℝ)^2069 := by
      have hnat : (50010891134241282173 : ℕ)^512*2500000000000000^2069 ≤ 2500134746345097^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010891134241282173 50000000000000000000 2500134746345097 2500000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134746345097/2500000000000000 : ℝ)) (X := (50010891134241282173/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028115253985174767/50000000000000000000 : ℝ) ≤ (500069560006649/500000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50028115253985174767/50000000000000000000 : ℝ)^512 ≤ (500069560006649/500000000000000 : ℝ)^2069 := by
      have hnat : (50028115253985174767 : ℕ)^512*500000000000000^2069 ≤ 500069560006649^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028115253985174767 50000000000000000000 500069560006649 500000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500069560006649/500000000000000 : ℝ)) (X := (50028115253985174767/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045339373729067361/50000000000000000000 : ℝ) ≤ (2500560853721393/2500000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50045339373729067361/50000000000000000000 : ℝ)^512 ≤ (2500560853721393/2500000000000000 : ℝ)^2069 := by
      have hnat : (50045339373729067361 : ℕ)^512*2500000000000000^2069 ≤ 2500560853721393^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045339373729067361 50000000000000000000 2500560853721393 2500000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500560853721393/2500000000000000 : ℝ)) (X := (50045339373729067361/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10891134241282173/100000000000000000000 : ℝ) ≤ ((737242753330525303/737500000000000000 : ℝ)+2*(53263422037/27656250000000 : ℝ)*(2091/20000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (737242753330525303/737500000000000000 : ℝ)+2*(53263422037/27656250000000 : ℝ)*(2091/20000 : ℝ)=(2500134746345097/2500000000000000 : ℝ) by norm_num, show 1+2*(10891134241282173/100000000000000000000 : ℝ)=(50010891134241282173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45339373729067361/100000000000000000000 : ℝ)+(10891134241282173/100000000000000000000 : ℝ) ≤ ((737242753330525303/737500000000000000 : ℝ)+(53263422037/27656250000000 : ℝ)*((93/625 : ℝ)+(2091/20000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (737242753330525303/737500000000000000 : ℝ)+(53263422037/27656250000000 : ℝ)*((93/625 : ℝ)+(2091/20000 : ℝ))=(500069560006649/500000000000000 : ℝ) by norm_num, show 1+(45339373729067361/100000000000000000000 : ℝ)+(10891134241282173/100000000000000000000 : ℝ)=(50028115253985174767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45339373729067361/100000000000000000000 : ℝ) ≤ ((737242753330525303/737500000000000000 : ℝ)+2*(53263422037/27656250000000 : ℝ)*(93/625 : ℝ))^(2069/512 : ℝ) := by
    rw [show (737242753330525303/737500000000000000 : ℝ)+2*(53263422037/27656250000000 : ℝ)*(93/625 : ℝ)=(2500560853721393/2500000000000000 : ℝ) by norm_num, show 1+2*(45339373729067361/100000000000000000000 : ℝ)=(50045339373729067361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (737242753330525303/737500000000000000 : ℝ)*(X 1 0+X 2 0)+(53263422037/27656250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2091/20000 : ℝ)) (hi := (93/625 : ℝ)) (c := (737242753330525303/737500000000000000 : ℝ)) (alpha := (53263422037/27656250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (737242753330525303/737500000000000000 : ℝ)*(X 0 1+X 2 1)+(53263422037/27656250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2091/20000 : ℝ)) (hi := (93/625 : ℝ)) (c := (737242753330525303/737500000000000000 : ℝ)) (alpha := (53263422037/27656250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (737242753330525303/737500000000000000 : ℝ)*(X 0 2+X 1 2)+(53263422037/27656250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2091/20000 : ℝ)) (hi := (93/625 : ℝ)) (c := (737242753330525303/737500000000000000 : ℝ)) (alpha := (53263422037/27656250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548486101/2500000000 : ℝ)*X 0 0+(540482999/1000000000 : ℝ)*X 0 1+(1313660189/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347626513/10000000000 : ℝ)*X 1 0+(-1135158617/5000000000 : ℝ)*X 1 1+(1050928257/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347626843/10000000000 : ℝ)*X 2 0+(5254640949/10000000000 : ℝ)*X 2 1+(-1135158619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437233387/1000000000 : ℝ)*X 0 0+(1056787089/2500000000 : ℝ)*X 0 1+(90451001/200000000 : ℝ)*X 0 2+(437233387/1000000000 : ℝ)*X 1 0+(1056787089/2500000000 : ℝ)*X 1 1+(90451001/200000000 : ℝ)*X 1 2+(437233387/1000000000 : ℝ)*X 2 0+(1056787089/2500000000 : ℝ)*X 2 1+(90451001/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096975697/5000000000 : ℝ)*X 0 0+(1051015657/2000000000 : ℝ)*X 0 1+(675548911/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309745469/10000000000 : ℝ)*X 1 0+(-1060283377/5000000000 : ℝ)*X 1 1+(2702195647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66371817/125000000 : ℝ)*X 2 0+(540439121/1000000000 : ℝ)*X 2 1+(-265070877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372349189/10000000000 : ℝ)*X 0 0+(4521690419/10000000000 : ℝ)*X 0 1+(2114005873/5000000000 : ℝ)*X 0 2+(4372349189/10000000000 : ℝ)*X 1 0+(4521690419/10000000000 : ℝ)*X 1 1+(2114005873/5000000000 : ℝ)*X 1 2+(4372349189/10000000000 : ℝ)*X 2 0+(4521690419/10000000000 : ℝ)*X 2 1+(2114005873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67040790137414405659568123/18437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2190919137/100000000000000 : ℝ)*(base19) + (1998643503/100000000000000 : ℝ)*(base23) + (128082793/25000000000000 : ℝ)*(upper3) + (322548551/100000000000000 : ℝ)*(upper4) + (144281079/100000000000000 : ℝ)*(upper5) + (5021832253483147/100000000000000 : ℝ)*(major0) + (5021832253483147/100000000000000 : ℝ)*(major1) + (5021832253483147/100000000000000 : ℝ)*(major2) + (3329164395500373/50000000000000 : ℝ)*(sp0) + (1331677067116517/20000000000000 : ℝ)*(sp1) + (6658385527858219/100000000000000 : ℝ)*(sp2) + (846310838952403/25000000000000 : ℝ)*(sp3) + (58735500977/100000000000000 : ℝ)*(sp4) + (1675172563/5000000000000 : ℝ)*(sp7) + (3385276859260871/100000000000000 : ℝ)*(f.failure) + (6658387526501723/100000000000000 : ℝ)*(f.sum) + (50325540383113/11062500000000000000000000000 : ℝ)*base66 + (1428787380598424377/221250000000000000000000000000000 : ℝ)*base68 + (3003078506042174377/221250000000000000000000000000000 : ℝ)*base70 + (2281004743318424377/221250000000000000000000000000000 : ℝ)*base72 + (37906298478613/11062500000000000000000000000 : ℝ)*base74 + (1798991370181575623/221250000000000000000000000000000 : ℝ)*base75 + (594083346598424377/221250000000000000000000000000000 : ℝ)*base78 + (1628233822775924377/221250000000000000000000000000000 : ℝ)*base80 + (32478986374363/11062500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2138557/400000000000000000000 : ℝ)*base90 + (2138557/400000000000000000000 : ℝ)*base92 + (2138557/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32225867571532787854475073/9218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864982221/100000000000000 : ℝ)*(base19) + (1096086037/100000000000000 : ℝ)*(base23) + (9022203/100000000000000 : ℝ)*(lower3) + (26146947/12500000000000 : ℝ)*(lower4) + (1262801972198601/25000000000000 : ℝ)*(major0) + (1262801972198601/25000000000000 : ℝ)*(major1) + (1262801972198601/25000000000000 : ℝ)*(major2) + (1142194981/100000000000000 : ℝ)*(sp0) + (14279031447/50000000000000 : ℝ)*(sp1) + (2500338943/10000000000000 : ℝ)*(sp2) + (3348667597204477/50000000000000 : ℝ)*(sp4) + (334865345677941/5000000000000 : ℝ)*(sp5) + (1674327559282117/25000000000000 : ℝ)*(sp6) + (851269831115489/25000000000000 : ℝ)*(sp7) + (851269831115489/25000000000000 : ℝ)*(f.failure) + (1339467267320787/20000000000000 : ℝ)*(f.sum) + (3052343042639/1843750000000000000000000000 : ℝ)*base65 + (100817558941771103/18437500000000000000000000000000 : ℝ)*base67 + (133060507291771103/18437500000000000000000000000000 : ℝ)*base69 + (379391493542396103/18437500000000000000000000000000 : ℝ)*base71 + (4607872816743/921875000000000000000000000 : ℝ)*base74 + (58649458717396103/18437500000000000000000000000000 : ℝ)*base75 + (130457905007396103/18437500000000000000000000000000 : ℝ)*base77 + (139751151146103/18437500000000000000000000000000 : ℝ)*base79 + (8131885605889/1843750000000000000000000000 : ℝ)*base81 + (109563/100000000000000000000 : ℝ)*base90 + (109563/100000000000000000000 : ℝ)*base92 + (109563/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1084_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (93/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_s5_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097361383/5000000000 : ℝ)*x 0 + (5396484551/10000000000 : ℝ)*x 1 + (2631237857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097361383/5000000000 : ℝ)^8277 ≤ (13330160226699/100000000000000 : ℝ)^6229 := by
    have hnat : (1097361383 : ℕ)^8277*100000000000000^6229 ≤ 13330160226699^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097361383 5000000000 13330160226699 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396484551/10000000000 : ℝ)^8277 ≤ (881176901697/2000000000000 : ℝ)^6229 := by
    have hnat : (5396484551 : ℕ)^8277*2000000000000^6229 ≤ 881176901697^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396484551 10000000000 881176901697 2000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631237857/5000000000 : ℝ)^8277 ≤ (42610994677829/100000000000000 : ℝ)^6229 := by
    have hnat : (2631237857 : ℕ)^8277*100000000000000^6229 ≤ 42610994677829^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631237857 5000000000 42610994677829 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097361383/5000000000 : ℝ), (5396484551/10000000000 : ℝ), (2631237857/5000000000 : ℝ)] ![(13330160226699/100000000000000 : ℝ), (881176901697/2000000000000 : ℝ), (42610994677829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097361383/5000000000 : ℝ)|^8277 ≤ (13330160226699/100000000000000 : ℝ)^6229
        have hw : |(-1097361383/5000000000 : ℝ)|=(1097361383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396484551/10000000000 : ℝ)|^8277 ≤ (881176901697/2000000000000 : ℝ)^6229
        have hw : |(5396484551/10000000000 : ℝ)|=(5396484551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631237857/5000000000 : ℝ)|^8277 ≤ (42610994677829/100000000000000 : ℝ)^6229
        have hw : |(2631237857/5000000000 : ℝ)|=(2631237857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267277253/500000000 : ℝ)*x 0 + (-141421603/625000000 : ℝ)*x 1 + (1052495097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267277253/500000000 : ℝ)^8277 ≤ (21753539171469/50000000000000 : ℝ)^6229 := by
    have hnat : (267277253 : ℕ)^8277*50000000000000^6229 ≤ 21753539171469^6229*500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267277253 500000000 21753539171469 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141421603/625000000 : ℝ)^8277 ≤ (6940964715861/50000000000000 : ℝ)^6229 := by
    have hnat : (141421603 : ℕ)^8277*50000000000000^6229 ≤ 6940964715861^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141421603 625000000 6940964715861 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052495097/2000000000 : ℝ)^8277 ≤ (42610992213937/100000000000000 : ℝ)^6229 := by
    have hnat : (1052495097 : ℕ)^8277*100000000000000^6229 ≤ 42610992213937^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052495097 2000000000 42610992213937 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267277253/500000000 : ℝ), (-141421603/625000000 : ℝ), (1052495097/2000000000 : ℝ)] ![(21753539171469/50000000000000 : ℝ), (6940964715861/50000000000000 : ℝ), (42610992213937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267277253/500000000 : ℝ)|^8277 ≤ (21753539171469/50000000000000 : ℝ)^6229
        have hw : |(267277253/500000000 : ℝ)|=(267277253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141421603/625000000 : ℝ)|^8277 ≤ (6940964715861/50000000000000 : ℝ)^6229
        have hw : |(-141421603/625000000 : ℝ)|=(141421603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052495097/2000000000 : ℝ)|^8277 ≤ (42610992213937/100000000000000 : ℝ)^6229
        have hw : |(1052495097/2000000000 : ℝ)|=(1052495097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345544907/10000000000 : ℝ)*x 0 + (2631237789/5000000000 : ℝ)*x 1 + (-17677701/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345544907/10000000000 : ℝ)^8277 ≤ (21753538344129/50000000000000 : ℝ)^6229 := by
    have hnat : (5345544907 : ℕ)^8277*50000000000000^6229 ≤ 21753538344129^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345544907 10000000000 21753538344129 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631237789/5000000000 : ℝ)^8277 ≤ (42610993214557/100000000000000 : ℝ)^6229 := by
    have hnat : (2631237789 : ℕ)^8277*100000000000000^6229 ≤ 42610993214557^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631237789 5000000000 42610993214557 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17677701/78125000 : ℝ)^8277 ≤ (13881930083889/100000000000000 : ℝ)^6229 := by
    have hnat : (17677701 : ℕ)^8277*100000000000000^6229 ≤ 13881930083889^6229*78125000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17677701 78125000 13881930083889 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345544907/10000000000 : ℝ), (2631237789/5000000000 : ℝ), (-17677701/78125000 : ℝ)] ![(21753538344129/50000000000000 : ℝ), (42610993214557/100000000000000 : ℝ), (13881930083889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345544907/10000000000 : ℝ)|^8277 ≤ (21753538344129/50000000000000 : ℝ)^6229
        have hw : |(5345544907/10000000000 : ℝ)|=(5345544907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631237789/5000000000 : ℝ)|^8277 ≤ (42610993214557/100000000000000 : ℝ)^6229
        have hw : |(2631237789/5000000000 : ℝ)|=(2631237789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17677701/78125000 : ℝ)|^8277 ≤ (13881930083889/100000000000000 : ℝ)^6229
        have hw : |(-17677701/78125000 : ℝ)|=(17677701/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186393309/5000000000 : ℝ)*x 0 + (848600209/2000000000 : ℝ)*x 1 + (901315793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186393309/5000000000 : ℝ)^8277 ≤ (33315405210801/100000000000000 : ℝ)^6229 := by
    have hnat : (2186393309 : ℕ)^8277*100000000000000^6229 ≤ 33315405210801^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186393309 5000000000 33315405210801 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848600209/2000000000 : ℝ)^8277 ≤ (6401588484553/20000000000000 : ℝ)^6229 := by
    have hnat : (848600209 : ℕ)^8277*20000000000000^6229 ≤ 6401588484553^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848600209 2000000000 6401588484553 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901315793/2000000000 : ℝ)^8277 ≤ (6935330468559/20000000000000 : ℝ)^6229 := by
    have hnat : (901315793 : ℕ)^8277*20000000000000^6229 ≤ 6935330468559^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901315793 2000000000 6935330468559 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186393309/5000000000 : ℝ), (848600209/2000000000 : ℝ), (901315793/2000000000 : ℝ)] ![(33315405210801/100000000000000 : ℝ), (6401588484553/20000000000000 : ℝ), (6935330468559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186393309/5000000000 : ℝ)|^8277 ≤ (33315405210801/100000000000000 : ℝ)^6229
        have hw : |(2186393309/5000000000 : ℝ)|=(2186393309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848600209/2000000000 : ℝ)|^8277 ≤ (6401588484553/20000000000000 : ℝ)^6229
        have hw : |(848600209/2000000000 : ℝ)|=(848600209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901315793/2000000000 : ℝ)|^8277 ≤ (6935330468559/20000000000000 : ℝ)^6229
        have hw : |(901315793/2000000000 : ℝ)|=(901315793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-438945683/2000000000 : ℝ)*x 0 + (5262823753/10000000000 : ℝ)*x 1 + (5396135167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438945683/2000000000 : ℝ)^8277 ≤ (1333020581801/10000000000000 : ℝ)^6229 := by
    have hnat : (438945683 : ℕ)^8277*10000000000000^6229 ≤ 1333020581801^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438945683 2000000000 1333020581801 10000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262823753/10000000000 : ℝ)^8277 ≤ (21307369696653/50000000000000 : ℝ)^6229 := by
    have hnat : (5262823753 : ℕ)^8277*50000000000000^6229 ≤ 21307369696653^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262823753 10000000000 21307369696653 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396135167/10000000000 : ℝ)^8277 ≤ (5506881846361/12500000000000 : ℝ)^6229 := by
    have hnat : (5396135167 : ℕ)^8277*12500000000000^6229 ≤ 5506881846361^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396135167 10000000000 5506881846361 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438945683/2000000000 : ℝ), (5262823753/10000000000 : ℝ), (5396135167/10000000000 : ℝ)] ![(1333020581801/10000000000000 : ℝ), (21307369696653/50000000000000 : ℝ), (5506881846361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438945683/2000000000 : ℝ)|^8277 ≤ (1333020581801/10000000000000 : ℝ)^6229
        have hw : |(-438945683/2000000000 : ℝ)|=(438945683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262823753/10000000000 : ℝ)|^8277 ≤ (21307369696653/50000000000000 : ℝ)^6229
        have hw : |(5262823753/10000000000 : ℝ)|=(5262823753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396135167/10000000000 : ℝ)|^8277 ≤ (5506881846361/12500000000000 : ℝ)^6229
        have hw : |(5396135167/10000000000 : ℝ)|=(5396135167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311743161/10000000000 : ℝ)*x 0 + (-532271557/2500000000 : ℝ)*x 1 + (5396135167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311743161/10000000000 : ℝ)^8277 ≤ (43141894699163/100000000000000 : ℝ)^6229 := by
    have hnat : (5311743161 : ℕ)^8277*100000000000000^6229 ≤ 43141894699163^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311743161 10000000000 43141894699163 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532271557/2500000000 : ℝ)^8277 ≤ (6401525257459/50000000000000 : ℝ)^6229 := by
    have hnat : (532271557 : ℕ)^8277*50000000000000^6229 ≤ 6401525257459^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532271557 2500000000 6401525257459 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396135167/10000000000 : ℝ)^8277 ≤ (5506881846361/12500000000000 : ℝ)^6229 := by
    have hnat : (5396135167 : ℕ)^8277*12500000000000^6229 ≤ 5506881846361^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396135167 10000000000 5506881846361 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311743161/10000000000 : ℝ), (-532271557/2500000000 : ℝ), (5396135167/10000000000 : ℝ)] ![(43141894699163/100000000000000 : ℝ), (6401525257459/50000000000000 : ℝ), (5506881846361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311743161/10000000000 : ℝ)|^8277 ≤ (43141894699163/100000000000000 : ℝ)^6229
        have hw : |(5311743161/10000000000 : ℝ)|=(5311743161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532271557/2500000000 : ℝ)|^8277 ≤ (6401525257459/50000000000000 : ℝ)^6229
        have hw : |(-532271557/2500000000 : ℝ)|=(532271557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396135167/10000000000 : ℝ)|^8277 ≤ (5506881846361/12500000000000 : ℝ)^6229
        have hw : |(5396135167/10000000000 : ℝ)|=(5396135167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327935789/2500000000 : ℝ)*x 0 + (1349033793/2500000000 : ℝ)*x 1 + (-2129086227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327935789/2500000000 : ℝ)^8277 ≤ (21570947322601/50000000000000 : ℝ)^6229 := by
    have hnat : (1327935789 : ℕ)^8277*50000000000000^6229 ≤ 21570947322601^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327935789 2500000000 21570947322601 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349033793/2500000000 : ℝ)^8277 ≤ (44055054825131/100000000000000 : ℝ)^6229 := by
    have hnat : (1349033793 : ℕ)^8277*100000000000000^6229 ≤ 44055054825131^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349033793 2500000000 44055054825131 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129086227/10000000000 : ℝ)^8277 ≤ (12803050506927/100000000000000 : ℝ)^6229 := by
    have hnat : (2129086227 : ℕ)^8277*100000000000000^6229 ≤ 12803050506927^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129086227 10000000000 12803050506927 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327935789/2500000000 : ℝ), (1349033793/2500000000 : ℝ), (-2129086227/10000000000 : ℝ)] ![(21570947322601/50000000000000 : ℝ), (44055054825131/100000000000000 : ℝ), (12803050506927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327935789/2500000000 : ℝ)|^8277 ≤ (21570947322601/50000000000000 : ℝ)^6229
        have hw : |(1327935789/2500000000 : ℝ)|=(1327935789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349033793/2500000000 : ℝ)|^8277 ≤ (44055054825131/100000000000000 : ℝ)^6229
        have hw : |(1349033793/2500000000 : ℝ)|=(1349033793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129086227/10000000000 : ℝ)|^8277 ≤ (12803050506927/100000000000000 : ℝ)^6229
        have hw : |(-2129086227/10000000000 : ℝ)|=(2129086227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s5_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372797739/10000000000 : ℝ)*x 0 + (4505894107/10000000000 : ℝ)*x 1 + (2121844171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372797739/10000000000 : ℝ)^8277 ≤ (33315517797079/100000000000000 : ℝ)^6229 := by
    have hnat : (4372797739 : ℕ)^8277*100000000000000^6229 ≤ 33315517797079^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372797739 10000000000 33315517797079 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505894107/10000000000 : ℝ)^8277 ≤ (34669650143193/100000000000000 : ℝ)^6229 := by
    have hnat : (4505894107 : ℕ)^8277*100000000000000^6229 ≤ 34669650143193^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505894107 10000000000 34669650143193 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121844171/5000000000 : ℝ)^8277 ≤ (8003708010637/25000000000000 : ℝ)^6229 := by
    have hnat : (2121844171 : ℕ)^8277*25000000000000^6229 ≤ 8003708010637^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121844171 5000000000 8003708010637 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372797739/10000000000 : ℝ), (4505894107/10000000000 : ℝ), (2121844171/5000000000 : ℝ)] ![(33315517797079/100000000000000 : ℝ), (34669650143193/100000000000000 : ℝ), (8003708010637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372797739/10000000000 : ℝ)|^8277 ≤ (33315517797079/100000000000000 : ℝ)^6229
        have hw : |(4372797739/10000000000 : ℝ)|=(4372797739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505894107/10000000000 : ℝ)|^8277 ≤ (34669650143193/100000000000000 : ℝ)^6229
        have hw : |(4505894107/10000000000 : ℝ)|=(4505894107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121844171/5000000000 : ℝ)|^8277 ≤ (8003708010637/25000000000000 : ℝ)^6229
        have hw : |(2121844171/5000000000 : ℝ)|=(2121844171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11227/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (553/5000 : ℝ) ^ (2069/512 : ℝ) ≤ (13670976184923707/100000000000000000000 : ℝ) := by
    have hpowers : (553/5000 : ℝ)^2069 ≤ (13670976184923707/100000000000000000000 : ℝ)^512 := by
      have hnat : (553 : ℕ)^2069*100000000000000000000^512 ≤ 13670976184923707^512*5000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        553 5000 13670976184923707 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (553/5000 : ℝ)) (X := (13670976184923707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (2069/512 : ℝ) ≤ (948987843202839/2500000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^2069 ≤ (948987843202839/2500000000000000000 : ℝ)^512 := by
      have hnat : (89 : ℕ)^2069*2500000000000000000^512 ≤ 948987843202839^512*625^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 948987843202839 2500000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (948987843202839/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013670976184923707/50000000000000000000 : ℝ) ≤ (10000676541306381/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50013670976184923707/50000000000000000000 : ℝ)^512 ≤ (10000676541306381/10000000000000000 : ℝ)^2069 := by
      have hnat : (50013670976184923707 : ℕ)^512*10000000000000000^2069 ≤ 10000676541306381^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013670976184923707 50000000000000000000 10000676541306381 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000676541306381/10000000000000000 : ℝ)) (X := (50013670976184923707/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051630489913037267/100000000000000000000 : ℝ) ≤ (10001277413093733/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (100051630489913037267/100000000000000000000 : ℝ)^512 ≤ (10001277413093733/10000000000000000 : ℝ)^2069 := by
      have hnat : (100051630489913037267 : ℕ)^512*10000000000000000^2069 ≤ 10001277413093733^2069*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051630489913037267 100000000000000000000 10001277413093733 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001277413093733/10000000000000000 : ℝ)) (X := (100051630489913037267/100000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250948987843202839/1250000000000000000 : ℝ) ≤ (2000375656976217/2000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (1250948987843202839/1250000000000000000 : ℝ)^512 ≤ (2000375656976217/2000000000000000 : ℝ)^2069 := by
      have hnat : (1250948987843202839 : ℕ)^512*2000000000000000^2069 ≤ 2000375656976217^2069*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250948987843202839 1250000000000000000 2000375656976217 2000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000375656976217/2000000000000000 : ℝ)) (X := (1250948987843202839/1250000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13670976184923707/100000000000000000000 : ℝ) ≤ ((529814335290301089/530000000000000000 : ℝ)+2*(25036324473/13250000000000 : ℝ)*(553/5000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (529814335290301089/530000000000000000 : ℝ)+2*(25036324473/13250000000000 : ℝ)*(553/5000 : ℝ)=(10000676541306381/10000000000000000 : ℝ) by norm_num, show 1+2*(13670976184923707/100000000000000000000 : ℝ)=(50013670976184923707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(948987843202839/2500000000000000000 : ℝ)+(13670976184923707/100000000000000000000 : ℝ) ≤ ((529814335290301089/530000000000000000 : ℝ)+(25036324473/13250000000000 : ℝ)*((89/625 : ℝ)+(553/5000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (529814335290301089/530000000000000000 : ℝ)+(25036324473/13250000000000 : ℝ)*((89/625 : ℝ)+(553/5000 : ℝ))=(10001277413093733/10000000000000000 : ℝ) by norm_num, show 1+(948987843202839/2500000000000000000 : ℝ)+(13670976184923707/100000000000000000000 : ℝ)=(100051630489913037267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(948987843202839/2500000000000000000 : ℝ) ≤ ((529814335290301089/530000000000000000 : ℝ)+2*(25036324473/13250000000000 : ℝ)*(89/625 : ℝ))^(2069/512 : ℝ) := by
    rw [show (529814335290301089/530000000000000000 : ℝ)+2*(25036324473/13250000000000 : ℝ)*(89/625 : ℝ)=(2000375656976217/2000000000000000 : ℝ) by norm_num, show 1+2*(948987843202839/2500000000000000000 : ℝ)=(1250948987843202839/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (529814335290301089/530000000000000000 : ℝ)*(X 1 0+X 2 0)+(25036324473/13250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (89/625 : ℝ)) (c := (529814335290301089/530000000000000000 : ℝ)) (alpha := (25036324473/13250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (529814335290301089/530000000000000000 : ℝ)*(X 0 1+X 2 1)+(25036324473/13250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (89/625 : ℝ)) (c := (529814335290301089/530000000000000000 : ℝ)) (alpha := (25036324473/13250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (529814335290301089/530000000000000000 : ℝ)*(X 0 2+X 1 2)+(25036324473/13250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (89/625 : ℝ)) (c := (529814335290301089/530000000000000000 : ℝ)) (alpha := (25036324473/13250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1097361383/5000000000 : ℝ)*X 0 0+(5396484551/10000000000 : ℝ)*X 0 1+(2631237857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267277253/500000000 : ℝ)*X 1 0+(-141421603/625000000 : ℝ)*X 1 1+(1052495097/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345544907/10000000000 : ℝ)*X 2 0+(2631237789/5000000000 : ℝ)*X 2 1+(-17677701/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186393309/5000000000 : ℝ)*X 0 0+(848600209/2000000000 : ℝ)*X 0 1+(901315793/2000000000 : ℝ)*X 0 2+(2186393309/5000000000 : ℝ)*X 1 0+(848600209/2000000000 : ℝ)*X 1 1+(901315793/2000000000 : ℝ)*X 1 2+(2186393309/5000000000 : ℝ)*X 2 0+(848600209/2000000000 : ℝ)*X 2 1+(901315793/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438945683/2000000000 : ℝ)*X 0 0+(5262823753/10000000000 : ℝ)*X 0 1+(5396135167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311743161/10000000000 : ℝ)*X 1 0+(-532271557/2500000000 : ℝ)*X 1 1+(5396135167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327935789/2500000000 : ℝ)*X 2 0+(1349033793/2500000000 : ℝ)*X 2 1+(-2129086227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372797739/10000000000 : ℝ)*X 0 0+(4505894107/10000000000 : ℝ)*X 0 1+(2121844171/5000000000 : ℝ)*X 0 2+(4372797739/10000000000 : ℝ)*X 1 0+(4505894107/10000000000 : ℝ)*X 1 1+(2121844171/5000000000 : ℝ)*X 1 2+(4372797739/10000000000 : ℝ)*X 2 0+(4505894107/10000000000 : ℝ)*X 2 1+(2121844171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8253521300887686433883319/1325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (427358427/25000000000000 : ℝ)*(base19) + (1484455667/100000000000000 : ℝ)*(base23) + (284547/1250000000000 : ℝ)*(lower2) + (85772021/50000000000000 : ℝ)*(upper3) + (8336753/50000000000000 : ℝ)*(lower4) + (281406644356357/5000000000000 : ℝ)*(major0) + (281406644356357/5000000000000 : ℝ)*(major1) + (281406644356357/5000000000000 : ℝ)*(major2) + (466389954195923/6250000000000 : ℝ)*(sp0) + (746227252853747/10000000000000 : ℝ)*(sp1) + (7462272753515511/100000000000000 : ℝ)*(sp2) + (948491673596161/25000000000000 : ℝ)*(sp3) + (3497083641/10000000000000 : ℝ)*(sp4) + (3079282837/12500000000000 : ℝ)*(sp7) + (3793991328647339/100000000000000 : ℝ)*(f.failure) + (3731137118985589/50000000000000 : ℝ)*(f.sum) + (28450762959/132500000000000000000000000 : ℝ)*base65 + (18618158441887227/2650000000000000000000000000000 : ℝ)*base68 + (14210950603512773/2650000000000000000000000000000 : ℝ)*base69 + (3692391684787227/2650000000000000000000000000000 : ℝ)*base72 + (416892186873/66250000000000000000000000 : ℝ)*base74 + (18672549935687227/2650000000000000000000000000000 : ℝ)*base76 + (37678999481162773/2650000000000000000000000000000 : ℝ)*base77 + (23678265760887227/2650000000000000000000000000000 : ℝ)*base80 + (501709517343/66250000000000000000000000 : ℝ)*base82 + (786487/400000000000000000000 : ℝ)*base89 + (786487/400000000000000000000 : ℝ)*base91 + (786487/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3472940091912713391369/1325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22338247/4000000000000 : ℝ)*(base19) + (589363307/100000000000000 : ℝ)*(base23) + (59662417/100000000000000 : ℝ)*(upper3) + (4220397/25000000000000 : ℝ)*(lower4) + (56693197/100000000000000 : ℝ)*(upper5) + (88398681495567/1562500000000 : ℝ)*(major0) + (88398681495567/1562500000000 : ℝ)*(major1) + (88398681495567/1562500000000 : ℝ)*(major2) + (461627747/3125000000000 : ℝ)*(sp1) + (1574432187/10000000000000 : ℝ)*(sp2) + (375061628427579/5000000000000 : ℝ)*(sp4) + (7501217238007501/100000000000000 : ℝ)*(sp5) + (7501216234866403/100000000000000 : ℝ)*(sp6) + (953449643877857/25000000000000 : ℝ)*(sp7) + (953449643877857/25000000000000 : ℝ)*(f.failure) + (375061628427579/5000000000000 : ℝ)*(f.sum) + (754828740869/165625000000000000000000000 : ℝ)*base66 + (3751925653712537/828125000000000000000000000000 : ℝ)*base68 + (9146326844724963/828125000000000000000000000000 : ℝ)*base69 + (3857430622332831/414062500000000000000000000000 : ℝ)*base72 + (363821436969/165625000000000000000000000 : ℝ)*base74 + (409668978487693/51757812500000000000000000000 : ℝ)*base75 + (5429566713743787/828125000000000000000000000000 : ℝ)*base78 + (7041824594599963/828125000000000000000000000000 : ℝ)*base79 + (5658928598573/1325000000000000000000000000 : ℝ)*base81 + (50181/100000000000000000000 : ℝ)*base89 + (50181/100000000000000000000 : ℝ)*base91 + (50181/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1084_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1084_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1084_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1084_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

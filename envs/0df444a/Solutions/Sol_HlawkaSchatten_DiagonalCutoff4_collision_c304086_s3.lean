-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304086_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:50:43.243482+00:00
-- url     : https://prove2.me/submissions/845e02b0-54b0-4fbb-83ad-371c0a85f82f

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c304086_s3_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-18847361/2500000000 : ℝ)*x 0 + (-202119717/312500000 : ℝ)*x 1 + (531475229/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18847361/2500000000 : ℝ)^133 ≤ (80120798773/50000000000000 : ℝ)^101 := by
    have hnat : (18847361 : ℕ)^133*50000000000000^101 ≤ 80120798773^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18847361 2500000000 80120798773 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202119717/312500000 : ℝ)^133 ≤ (11267589155261/20000000000000 : ℝ)^101 := by
    have hnat : (202119717 : ℕ)^133*20000000000000^101 ≤ 11267589155261^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202119717 312500000 11267589155261 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531475229/1000000000 : ℝ)^133 ≤ (43501812617059/100000000000000 : ℝ)^101 := by
    have hnat : (531475229 : ℕ)^133*100000000000000^101 ≤ 43501812617059^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531475229 1000000000 43501812617059 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18847361/2500000000 : ℝ), (-202119717/312500000 : ℝ), (531475229/1000000000 : ℝ)] ![(80120798773/50000000000000 : ℝ), (11267589155261/20000000000000 : ℝ), (43501812617059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18847361/2500000000 : ℝ)|^133 ≤ (80120798773/50000000000000 : ℝ)^101
        have hw : |(-18847361/2500000000 : ℝ)|=(18847361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-202119717/312500000 : ℝ)|^133 ≤ (11267589155261/20000000000000 : ℝ)^101
        have hw : |(-202119717/312500000 : ℝ)|=(202119717/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531475229/1000000000 : ℝ)|^133 ≤ (43501812617059/100000000000000 : ℝ)^101
        have hw : |(531475229/1000000000 : ℝ)|=(531475229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (769300759/2000000000 : ℝ)*x 0 + (-360153789/1250000000 : ℝ)*x 1 + (1219988587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (769300759/2000000000 : ℝ)^133 ≤ (7104638560763/25000000000000 : ℝ)^101 := by
    have hnat : (769300759 : ℕ)^133*25000000000000^101 ≤ 7104638560763^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769300759 2000000000 7104638560763 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360153789/1250000000 : ℝ)^133 ≤ (19424737355771/100000000000000 : ℝ)^101 := by
    have hnat : (360153789 : ℕ)^133*100000000000000^101 ≤ 19424737355771^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360153789 1250000000 19424737355771 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1219988587/2000000000 : ℝ)^133 ≤ (26078354195823/50000000000000 : ℝ)^101 := by
    have hnat : (1219988587 : ℕ)^133*50000000000000^101 ≤ 26078354195823^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219988587 2000000000 26078354195823 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(769300759/2000000000 : ℝ), (-360153789/1250000000 : ℝ), (1219988587/2000000000 : ℝ)] ![(7104638560763/25000000000000 : ℝ), (19424737355771/100000000000000 : ℝ), (26078354195823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(769300759/2000000000 : ℝ)|^133 ≤ (7104638560763/25000000000000 : ℝ)^101
        have hw : |(769300759/2000000000 : ℝ)|=(769300759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360153789/1250000000 : ℝ)|^133 ≤ (19424737355771/100000000000000 : ℝ)^101
        have hw : |(-360153789/1250000000 : ℝ)|=(360153789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1219988587/2000000000 : ℝ)|^133 ≤ (26078354195823/50000000000000 : ℝ)^101
        have hw : |(1219988587/2000000000 : ℝ)|=(1219988587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (15070251/10000000000 : ℝ)*x 0 + (-8065901807/10000000000 : ℝ)*x 1 + (6739573/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15070251/10000000000 : ℝ)^133 ≤ (19233558799/100000000000000 : ℝ)^101 := by
    have hnat : (15070251 : ℕ)^133*100000000000000^101 ≤ 19233558799^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15070251 10000000000 19233558799 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8065901807/10000000000 : ℝ)^133 ≤ (75349022322469/100000000000000 : ℝ)^101 := by
    have hnat : (8065901807 : ℕ)^133*100000000000000^101 ≤ 75349022322469^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8065901807 10000000000 75349022322469 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6739573/19531250 : ℝ)^133 ≤ (12315872054861/50000000000000 : ℝ)^101 := by
    have hnat : (6739573 : ℕ)^133*50000000000000^101 ≤ 12315872054861^101*19531250^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6739573 19531250 12315872054861 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15070251/10000000000 : ℝ), (-8065901807/10000000000 : ℝ), (6739573/19531250 : ℝ)] ![(19233558799/100000000000000 : ℝ), (75349022322469/100000000000000 : ℝ), (12315872054861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15070251/10000000000 : ℝ)|^133 ≤ (19233558799/100000000000000 : ℝ)^101
        have hw : |(15070251/10000000000 : ℝ)|=(15070251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8065901807/10000000000 : ℝ)|^133 ≤ (75349022322469/100000000000000 : ℝ)^101
        have hw : |(-8065901807/10000000000 : ℝ)|=(8065901807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6739573/19531250 : ℝ)|^133 ≤ (12315872054861/50000000000000 : ℝ)^101
        have hw : |(6739573/19531250 : ℝ)|=(6739573/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5347589659/10000000000 : ℝ)*x 0 + (4616100191/10000000000 : ℝ)*x 1 + (147349607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347589659/10000000000 : ℝ)^133 ≤ (43856093093319/100000000000000 : ℝ)^101 := by
    have hnat : (5347589659 : ℕ)^133*100000000000000^101 ≤ 43856093093319^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347589659 10000000000 43856093093319 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4616100191/10000000000 : ℝ)^133 ≤ (36133246299077/100000000000000 : ℝ)^101 := by
    have hnat : (4616100191 : ℕ)^133*100000000000000^101 ≤ 36133246299077^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616100191 10000000000 36133246299077 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147349607/500000000 : ℝ)^133 ≤ (2501332574327/12500000000000 : ℝ)^101 := by
    have hnat : (147349607 : ℕ)^133*12500000000000^101 ≤ 2501332574327^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147349607 500000000 2501332574327 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347589659/10000000000 : ℝ), (4616100191/10000000000 : ℝ), (147349607/500000000 : ℝ)] ![(43856093093319/100000000000000 : ℝ), (36133246299077/100000000000000 : ℝ), (2501332574327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347589659/10000000000 : ℝ)|^133 ≤ (43856093093319/100000000000000 : ℝ)^101
        have hw : |(5347589659/10000000000 : ℝ)|=(5347589659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4616100191/10000000000 : ℝ)|^133 ≤ (36133246299077/100000000000000 : ℝ)^101
        have hw : |(4616100191/10000000000 : ℝ)|=(4616100191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147349607/500000000 : ℝ)|^133 ≤ (2501332574327/12500000000000 : ℝ)^101
        have hw : |(147349607/500000000 : ℝ)|=(147349607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (754553279/1250000000 : ℝ)*x 0 + (-3411342201/10000000000 : ℝ)*x 1 + (-1707359661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (754553279/1250000000 : ℝ)^133 ≤ (51442731864787/100000000000000 : ℝ)^101 := by
    have hnat : (754553279 : ℕ)^133*100000000000000^101 ≤ 51442731864787^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754553279 1250000000 51442731864787 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3411342201/10000000000 : ℝ)^133 ≤ (12131408408257/50000000000000 : ℝ)^101 := by
    have hnat : (3411342201 : ℕ)^133*50000000000000^101 ≤ 12131408408257^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411342201 10000000000 12131408408257 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1707359661/5000000000 : ℝ)^133 ≤ (303680641397/1250000000000 : ℝ)^101 := by
    have hnat : (1707359661 : ℕ)^133*1250000000000^101 ≤ 303680641397^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707359661 5000000000 303680641397 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(754553279/1250000000 : ℝ), (-3411342201/10000000000 : ℝ), (-1707359661/5000000000 : ℝ)] ![(51442731864787/100000000000000 : ℝ), (12131408408257/50000000000000 : ℝ), (303680641397/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(754553279/1250000000 : ℝ)|^133 ≤ (51442731864787/100000000000000 : ℝ)^101
        have hw : |(754553279/1250000000 : ℝ)|=(754553279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3411342201/10000000000 : ℝ)|^133 ≤ (12131408408257/50000000000000 : ℝ)^101
        have hw : |(-3411342201/10000000000 : ℝ)|=(3411342201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1707359661/5000000000 : ℝ)|^133 ≤ (303680641397/1250000000000 : ℝ)^101
        have hw : |(-1707359661/5000000000 : ℝ)|=(1707359661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2847540531/10000000000 : ℝ)*x 0 + (-1499817377/10000000000 : ℝ)*x 1 + (3922838133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2847540531/10000000000 : ℝ)^133 ≤ (19126200279593/100000000000000 : ℝ)^101 := by
    have hnat : (2847540531 : ℕ)^133*100000000000000^101 ≤ 19126200279593^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847540531 10000000000 19126200279593 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499817377/10000000000 : ℝ)^133 ≤ (1644414244481/20000000000000 : ℝ)^101 := by
    have hnat : (1499817377 : ℕ)^133*20000000000000^101 ≤ 1644414244481^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499817377 10000000000 1644414244481 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3922838133/5000000000 : ℝ)^133 ≤ (72651728479983/100000000000000 : ℝ)^101 := by
    have hnat : (3922838133 : ℕ)^133*100000000000000^101 ≤ 72651728479983^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3922838133 5000000000 72651728479983 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2847540531/10000000000 : ℝ), (-1499817377/10000000000 : ℝ), (3922838133/5000000000 : ℝ)] ![(19126200279593/100000000000000 : ℝ), (1644414244481/20000000000000 : ℝ), (72651728479983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2847540531/10000000000 : ℝ)|^133 ≤ (19126200279593/100000000000000 : ℝ)^101
        have hw : |(2847540531/10000000000 : ℝ)|=(2847540531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1499817377/10000000000 : ℝ)|^133 ≤ (1644414244481/20000000000000 : ℝ)^101
        have hw : |(-1499817377/10000000000 : ℝ)|=(1499817377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3922838133/5000000000 : ℝ)|^133 ≤ (72651728479983/100000000000000 : ℝ)^101
        have hw : |(3922838133/5000000000 : ℝ)|=(3922838133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1837/156250000 : ℝ)*x 0 + (-453358111/1000000000 : ℝ)*x 1 + (7185828741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1837/156250000 : ℝ)^133 ≤ (32240409/100000000000000 : ℝ)^101 := by
    have hnat : (1837 : ℕ)^133*100000000000000^101 ≤ 32240409^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837 156250000 32240409 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453358111/1000000000 : ℝ)^133 ≤ (705701650363/2000000000000 : ℝ)^101 := by
    have hnat : (453358111 : ℕ)^133*2000000000000^101 ≤ 705701650363^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453358111 1000000000 705701650363 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7185828741/10000000000 : ℝ)^133 ≤ (12942977045267/20000000000000 : ℝ)^101 := by
    have hnat : (7185828741 : ℕ)^133*20000000000000^101 ≤ 12942977045267^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7185828741 10000000000 12942977045267 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1837/156250000 : ℝ), (-453358111/1000000000 : ℝ), (7185828741/10000000000 : ℝ)] ![(32240409/100000000000000 : ℝ), (705701650363/2000000000000 : ℝ), (12942977045267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1837/156250000 : ℝ)|^133 ≤ (32240409/100000000000000 : ℝ)^101
        have hw : |(-1837/156250000 : ℝ)|=(1837/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453358111/1000000000 : ℝ)|^133 ≤ (705701650363/2000000000000 : ℝ)^101
        have hw : |(-453358111/1000000000 : ℝ)|=(453358111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7185828741/10000000000 : ℝ)|^133 ≤ (12942977045267/20000000000000 : ℝ)^101
        have hw : |(7185828741/10000000000 : ℝ)|=(7185828741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8276438619/10000000000 : ℝ)*x 0 + (1055558619/5000000000 : ℝ)*x 1 + (1627121907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8276438619/10000000000 : ℝ)^133 ≤ (77949568577863/100000000000000 : ℝ)^101 := by
    have hnat : (8276438619 : ℕ)^133*100000000000000^101 ≤ 77949568577863^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8276438619 10000000000 77949568577863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055558619/5000000000 : ℝ)^133 ≤ (3224307638263/25000000000000 : ℝ)^101 := by
    have hnat : (1055558619 : ℕ)^133*25000000000000^101 ≤ 3224307638263^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055558619 5000000000 3224307638263 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1627121907/10000000000 : ℝ)^133 ≤ (1830640172471/20000000000000 : ℝ)^101 := by
    have hnat : (1627121907 : ℕ)^133*20000000000000^101 ≤ 1830640172471^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627121907 10000000000 1830640172471 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8276438619/10000000000 : ℝ), (1055558619/5000000000 : ℝ), (1627121907/10000000000 : ℝ)] ![(77949568577863/100000000000000 : ℝ), (3224307638263/25000000000000 : ℝ), (1830640172471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8276438619/10000000000 : ℝ)|^133 ≤ (77949568577863/100000000000000 : ℝ)^101
        have hw : |(8276438619/10000000000 : ℝ)|=(8276438619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055558619/5000000000 : ℝ)|^133 ≤ (3224307638263/25000000000000 : ℝ)^101
        have hw : |(1055558619/5000000000 : ℝ)|=(1055558619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1627121907/10000000000 : ℝ)|^133 ≤ (1830640172471/20000000000000 : ℝ)^101
        have hw : |(1627121907/10000000000 : ℝ)|=(1627121907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7822164649/10000000000 : ℝ)*x 0 + (-21868653/80000000 : ℝ)*x 1 + (-20938541/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7822164649/10000000000 : ℝ)^133 ≤ (2261411383033/3125000000000 : ℝ)^101 := by
    have hnat : (7822164649 : ℕ)^133*3125000000000^101 ≤ 2261411383033^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7822164649 10000000000 2261411383033 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21868653/80000000 : ℝ)^133 ≤ (18124703582819/100000000000000 : ℝ)^101 := by
    have hnat : (21868653 : ℕ)^133*100000000000000^101 ≤ 18124703582819^101*80000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21868653 80000000 18124703582819 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20938541/125000000 : ℝ)^133 ≤ (4755066070589/50000000000000 : ℝ)^101 := by
    have hnat : (20938541 : ℕ)^133*50000000000000^101 ≤ 4755066070589^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20938541 125000000 4755066070589 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7822164649/10000000000 : ℝ), (-21868653/80000000 : ℝ), (-20938541/125000000 : ℝ)] ![(2261411383033/3125000000000 : ℝ), (18124703582819/100000000000000 : ℝ), (4755066070589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7822164649/10000000000 : ℝ)|^133 ≤ (2261411383033/3125000000000 : ℝ)^101
        have hw : |(7822164649/10000000000 : ℝ)|=(7822164649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21868653/80000000 : ℝ)|^133 ≤ (18124703582819/100000000000000 : ℝ)^101
        have hw : |(-21868653/80000000 : ℝ)|=(21868653/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20938541/125000000 : ℝ)|^133 ≤ (4755066070589/50000000000000 : ℝ)^101
        have hw : |(-20938541/125000000 : ℝ)|=(20938541/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (469472653/2000000000 : ℝ)*x 0 + (-1695514629/10000000000 : ℝ)*x 1 + (201966843/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469472653/2000000000 : ℝ)^133 ≤ (3707662639063/25000000000000 : ℝ)^101 := by
    have hnat : (469472653 : ℕ)^133*25000000000000^101 ≤ 3707662639063^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469472653 2000000000 3707662639063 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1695514629/10000000000 : ℝ)^133 ≤ (4831587574183/50000000000000 : ℝ)^101 := by
    have hnat : (1695514629 : ℕ)^133*50000000000000^101 ≤ 4831587574183^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695514629 10000000000 4831587574183 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201966843/250000000 : ℝ)^133 ≤ (37753087140231/50000000000000 : ℝ)^101 := by
    have hnat : (201966843 : ℕ)^133*50000000000000^101 ≤ 37753087140231^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201966843 250000000 37753087140231 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(469472653/2000000000 : ℝ), (-1695514629/10000000000 : ℝ), (201966843/250000000 : ℝ)] ![(3707662639063/25000000000000 : ℝ), (4831587574183/50000000000000 : ℝ), (37753087140231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(469472653/2000000000 : ℝ)|^133 ≤ (3707662639063/25000000000000 : ℝ)^101
        have hw : |(469472653/2000000000 : ℝ)|=(469472653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1695514629/10000000000 : ℝ)|^133 ≤ (4831587574183/50000000000000 : ℝ)^101
        have hw : |(-1695514629/10000000000 : ℝ)|=(1695514629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201966843/250000000 : ℝ)|^133 ≤ (37753087140231/50000000000000 : ℝ)^101
        have hw : |(201966843/250000000 : ℝ)|=(201966843/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (76069543/10000000000 : ℝ)*x 0 + (-8011440403/10000000000 : ℝ)*x 1 + (3506510821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76069543/10000000000 : ℝ)^133 ≤ (81073937397/50000000000000 : ℝ)^101 := by
    have hnat : (76069543 : ℕ)^133*50000000000000^101 ≤ 81073937397^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76069543 10000000000 81073937397 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8011440403/10000000000 : ℝ)^133 ≤ (74679787870609/100000000000000 : ℝ)^101 := by
    have hnat : (8011440403 : ℕ)^133*100000000000000^101 ≤ 74679787870609^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8011440403 10000000000 74679787870609 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3506510821/10000000000 : ℝ)^133 ≤ (3144758030299/12500000000000 : ℝ)^101 := by
    have hnat : (3506510821 : ℕ)^133*12500000000000^101 ≤ 3144758030299^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3506510821 10000000000 3144758030299 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(76069543/10000000000 : ℝ), (-8011440403/10000000000 : ℝ), (3506510821/10000000000 : ℝ)] ![(81073937397/50000000000000 : ℝ), (74679787870609/100000000000000 : ℝ), (3144758030299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(76069543/10000000000 : ℝ)|^133 ≤ (81073937397/50000000000000 : ℝ)^101
        have hw : |(76069543/10000000000 : ℝ)|=(76069543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8011440403/10000000000 : ℝ)|^133 ≤ (74679787870609/100000000000000 : ℝ)^101
        have hw : |(-8011440403/10000000000 : ℝ)|=(8011440403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3506510821/10000000000 : ℝ)|^133 ≤ (3144758030299/12500000000000 : ℝ)^101
        have hw : |(3506510821/10000000000 : ℝ)|=(3506510821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7916185079/10000000000 : ℝ)*x 0 + (2396504189/10000000000 : ℝ)*x 1 + (95128767/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7916185079/10000000000 : ℝ)^133 ≤ (73512733799503/100000000000000 : ℝ)^101 := by
    have hnat : (7916185079 : ℕ)^133*100000000000000^101 ≤ 73512733799503^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7916185079 10000000000 73512733799503 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396504189/10000000000 : ℝ)^133 ≤ (15240840107613/100000000000000 : ℝ)^101 := by
    have hnat : (2396504189 : ℕ)^133*100000000000000^101 ≤ 15240840107613^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396504189 10000000000 15240840107613 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95128767/500000000 : ℝ)^133 ≤ (5623213038661/50000000000000 : ℝ)^101 := by
    have hnat : (95128767 : ℕ)^133*50000000000000^101 ≤ 5623213038661^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95128767 500000000 5623213038661 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7916185079/10000000000 : ℝ), (2396504189/10000000000 : ℝ), (95128767/500000000 : ℝ)] ![(73512733799503/100000000000000 : ℝ), (15240840107613/100000000000000 : ℝ), (5623213038661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7916185079/10000000000 : ℝ)|^133 ≤ (73512733799503/100000000000000 : ℝ)^101
        have hw : |(7916185079/10000000000 : ℝ)|=(7916185079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2396504189/10000000000 : ℝ)|^133 ≤ (15240840107613/100000000000000 : ℝ)^101
        have hw : |(2396504189/10000000000 : ℝ)|=(2396504189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95128767/500000000 : ℝ)|^133 ≤ (5623213038661/50000000000000 : ℝ)^101
        have hw : |(95128767/500000000 : ℝ)|=(95128767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (551863137/1250000000 : ℝ)*x 0 + (-106672657/200000000 : ℝ)*x 1 + (-319101691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551863137/1250000000 : ℝ)^133 ≤ (17036925228001/50000000000000 : ℝ)^101 := by
    have hnat : (551863137 : ℕ)^133*50000000000000^101 ≤ 17036925228001^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551863137 1250000000 17036925228001 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106672657/200000000 : ℝ)^133 ≤ (8741085883213/20000000000000 : ℝ)^101 := by
    have hnat : (106672657 : ℕ)^133*20000000000000^101 ≤ 8741085883213^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106672657 200000000 8741085883213 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319101691/1000000000 : ℝ)^133 ≤ (22220720116523/100000000000000 : ℝ)^101 := by
    have hnat : (319101691 : ℕ)^133*100000000000000^101 ≤ 22220720116523^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319101691 1000000000 22220720116523 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551863137/1250000000 : ℝ), (-106672657/200000000 : ℝ), (-319101691/1000000000 : ℝ)] ![(17036925228001/50000000000000 : ℝ), (8741085883213/20000000000000 : ℝ), (22220720116523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551863137/1250000000 : ℝ)|^133 ≤ (17036925228001/50000000000000 : ℝ)^101
        have hw : |(551863137/1250000000 : ℝ)|=(551863137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106672657/200000000 : ℝ)|^133 ≤ (8741085883213/20000000000000 : ℝ)^101
        have hw : |(-106672657/200000000 : ℝ)|=(106672657/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319101691/1000000000 : ℝ)|^133 ≤ (22220720116523/100000000000000 : ℝ)^101
        have hw : |(-319101691/1000000000 : ℝ)|=(319101691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s3_s3_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3128461867/5000000000 : ℝ)*x 0 + (-1751421361/10000000000 : ℝ)*x 1 + (2300791977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3128461867/5000000000 : ℝ)^133 ≤ (53931379643579/100000000000000 : ℝ)^101 := by
    have hnat : (3128461867 : ℕ)^133*100000000000000^101 ≤ 53931379643579^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3128461867 5000000000 53931379643579 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1751421361/10000000000 : ℝ)^133 ≤ (10084928555623/100000000000000 : ℝ)^101 := by
    have hnat : (1751421361 : ℕ)^133*100000000000000^101 ≤ 10084928555623^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751421361 10000000000 10084928555623 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2300791977/5000000000 : ℝ)^133 ≤ (7196738358061/20000000000000 : ℝ)^101 := by
    have hnat : (2300791977 : ℕ)^133*20000000000000^101 ≤ 7196738358061^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300791977 5000000000 7196738358061 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3128461867/5000000000 : ℝ), (-1751421361/10000000000 : ℝ), (2300791977/5000000000 : ℝ)] ![(53931379643579/100000000000000 : ℝ), (10084928555623/100000000000000 : ℝ), (7196738358061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3128461867/5000000000 : ℝ)|^133 ≤ (53931379643579/100000000000000 : ℝ)^101
        have hw : |(3128461867/5000000000 : ℝ)|=(3128461867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1751421361/10000000000 : ℝ)|^133 ≤ (10084928555623/100000000000000 : ℝ)^101
        have hw : |(-1751421361/10000000000 : ℝ)|=(1751421361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2300791977/5000000000 : ℝ)|^133 ≤ (7196738358061/20000000000000 : ℝ)^101
        have hw : |(2300791977/5000000000 : ℝ)|=(2300791977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304086_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((37107/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37107/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8753/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8753/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85659/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85659/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7881/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7881/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15171/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15171/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (37107/50000 : ℝ) ^ (33/8 : ℝ) ≤ (1826560690544900997/6250000000000000000 : ℝ) := by
    have hpowers : (37107/50000 : ℝ)^33 ≤ (1826560690544900997/6250000000000000000 : ℝ)^8 := by
      have hnat : (37107 : ℕ)^33*6250000000000000000^8 ≤ 1826560690544900997^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37107 50000 1826560690544900997 6250000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37107/50000 : ℝ)) (X := (1826560690544900997/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (8076560690544900997/6250000000000000000 : ℝ) ≤ (5320630278082113/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (8076560690544900997/6250000000000000000 : ℝ)^8 ≤ (5320630278082113/5000000000000000 : ℝ)^33 := by
      have hnat : (8076560690544900997 : ℕ)^8*5000000000000000^33 ≤ 5320630278082113^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8076560690544900997 6250000000000000000 5320630278082113 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5320630278082113/5000000000000000 : ℝ)) (X := (8076560690544900997/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (4951560690544900997/3125000000000000000 : ℝ) ≤ (1118043464333301/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (4951560690544900997/3125000000000000000 : ℝ)^8 ≤ (1118043464333301/1000000000000000 : ℝ)^33 := by
      have hnat : (4951560690544900997 : ℕ)^8*1000000000000000^33 ≤ 1118043464333301^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4951560690544900997 3125000000000000000 1118043464333301 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1118043464333301/1000000000000000 : ℝ)) (X := (4951560690544900997/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(320630278082113/3710700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11232793482683/154612500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (37107/50000 : ℝ)) (alpha := (320630278082113/3710700000000000 : ℝ)) (beta := (11232793482683/154612500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37107/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(320630278082113/3710700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11232793482683/154612500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (8753/10000 : ℝ) ^ (33/8 : ℝ) ≤ (57729438039275539519/100000000000000000000 : ℝ) := by
    have hpowers : (8753/10000 : ℝ)^33 ≤ (57729438039275539519/100000000000000000000 : ℝ)^8 := by
      have hnat : (8753 : ℕ)^33*100000000000000000000^8 ≤ 57729438039275539519^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8753 10000 57729438039275539519 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8753/10000 : ℝ)) (X := (57729438039275539519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (157729438039275539519/100000000000000000000 : ℝ) ≤ (2792022145196947/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (157729438039275539519/100000000000000000000 : ℝ)^8 ≤ (2792022145196947/2500000000000000 : ℝ)^33 := by
      have hnat : (157729438039275539519 : ℕ)^8*2500000000000000^33 ≤ 2792022145196947^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        157729438039275539519 100000000000000000000 2792022145196947 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2792022145196947/2500000000000000 : ℝ)) (X := (157729438039275539519/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (107729438039275539519/50000000000000000000 : ℝ) ≤ (752827763525463/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (107729438039275539519/50000000000000000000 : ℝ)^8 ≤ (752827763525463/625000000000000 : ℝ)^33 := by
      have hnat : (107729438039275539519 : ℕ)^8*625000000000000^33 ≤ 752827763525463^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107729438039275539519 50000000000000000000 752827763525463 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (752827763525463/625000000000000 : ℝ)) (X := (107729438039275539519/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(292022145196947/2188250000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(43857781780981/437650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (8753/10000 : ℝ)) (alpha := (292022145196947/2188250000000000 : ℝ)) (beta := (43857781780981/437650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (8753/10000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(292022145196947/2188250000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(43857781780981/437650000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (85659/100000 : ℝ) ^ (33/8 : ℝ) ≤ (412551960769046723/781250000000000000 : ℝ) := by
    have hpowers : (85659/100000 : ℝ)^33 ≤ (412551960769046723/781250000000000000 : ℝ)^8 := by
      have hnat : (85659 : ℕ)^33*781250000000000000^8 ≤ 412551960769046723^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85659 100000 412551960769046723 781250000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85659/100000 : ℝ)) (X := (412551960769046723/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (1193801960769046723/781250000000000000 : ℝ) ≤ (11082571638157299/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1193801960769046723/781250000000000000 : ℝ)^8 ≤ (11082571638157299/10000000000000000 : ℝ)^33 := by
      have hnat : (1193801960769046723 : ℕ)^8*10000000000000000^33 ≤ 11082571638157299^33*781250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1193801960769046723 781250000000000000 11082571638157299 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11082571638157299/10000000000000000 : ℝ)) (X := (1193801960769046723/781250000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (803176960769046723/390625000000000000 : ℝ) ≤ (5954718094727391/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (803176960769046723/390625000000000000 : ℝ)^8 ≤ (5954718094727391/5000000000000000 : ℝ)^33 := by
      have hnat : (803176960769046723 : ℕ)^8*5000000000000000^33 ≤ 5954718094727391^33*390625000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        803176960769046723 390625000000000000 5954718094727391 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5954718094727391/5000000000000000 : ℝ)) (X := (803176960769046723/390625000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1082571638157299/8565900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(275621517099161/2855300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (85659/100000 : ℝ)) (alpha := (1082571638157299/8565900000000000 : ℝ)) (beta := (275621517099161/2855300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (85659/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1082571638157299/8565900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(275621517099161/2855300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-18847361/2500000000 : ℝ)*X 0 0+(-202119717/312500000 : ℝ)*X 0 1+(531475229/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((769300759/2000000000 : ℝ)*X 0 0+(-360153789/1250000000 : ℝ)*X 0 1+(1219988587/2000000000 : ℝ)*X 0 2+(769300759/2000000000 : ℝ)*X 1 0+(-360153789/1250000000 : ℝ)*X 1 1+(1219988587/2000000000 : ℝ)*X 1 2+(769300759/2000000000 : ℝ)*X 2 0+(-360153789/1250000000 : ℝ)*X 2 1+(1219988587/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((15070251/10000000000 : ℝ)*X 0 0+(-8065901807/10000000000 : ℝ)*X 0 1+(6739573/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((5347589659/10000000000 : ℝ)*X 1 0+(4616100191/10000000000 : ℝ)*X 1 1+(147349607/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((754553279/1250000000 : ℝ)*X 2 0+(-3411342201/10000000000 : ℝ)*X 2 1+(-1707359661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2847540531/10000000000 : ℝ)*X 0 0+(-1499817377/10000000000 : ℝ)*X 0 1+(3922838133/5000000000 : ℝ)*X 0 2+(2847540531/10000000000 : ℝ)*X 1 0+(-1499817377/10000000000 : ℝ)*X 1 1+(3922838133/5000000000 : ℝ)*X 1 2+(2847540531/10000000000 : ℝ)*X 2 0+(-1499817377/10000000000 : ℝ)*X 2 1+(3922838133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1837/156250000 : ℝ)*X 0 0+(-453358111/1000000000 : ℝ)*X 0 1+(7185828741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((8276438619/10000000000 : ℝ)*X 1 0+(1055558619/5000000000 : ℝ)*X 1 1+(1627121907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((7822164649/10000000000 : ℝ)*X 2 0+(-21868653/80000000 : ℝ)*X 2 1+(-20938541/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((469472653/2000000000 : ℝ)*X 0 0+(-1695514629/10000000000 : ℝ)*X 0 1+(201966843/250000000 : ℝ)*X 0 2+(469472653/2000000000 : ℝ)*X 1 0+(-1695514629/10000000000 : ℝ)*X 1 1+(201966843/250000000 : ℝ)*X 1 2+(469472653/2000000000 : ℝ)*X 2 0+(-1695514629/10000000000 : ℝ)*X 2 1+(201966843/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((76069543/10000000000 : ℝ)*X 0 0+(-8011440403/10000000000 : ℝ)*X 0 1+(3506510821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((7916185079/10000000000 : ℝ)*X 1 0+(2396504189/10000000000 : ℝ)*X 1 1+(95128767/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((551863137/1250000000 : ℝ)*X 2 0+(-106672657/200000000 : ℝ)*X 2 1+(-319101691/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((3128461867/5000000000 : ℝ)*X 0 0+(-1751421361/10000000000 : ℝ)*X 0 1+(2300791977/5000000000 : ℝ)*X 0 2+(3128461867/5000000000 : ℝ)*X 1 0+(-1751421361/10000000000 : ℝ)*X 1 1+(2300791977/5000000000 : ℝ)*X 1 2+(3128461867/5000000000 : ℝ)*X 2 0+(-1751421361/10000000000 : ℝ)*X 2 1+(2300791977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((28809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (66686308478561800989750033397/9200342306312500000000000000000000 : ℝ) := by norm_num
    linear_combination (119993765657/250000000000 : ℝ)*(base7) + (4106731/1000000000000 : ℝ)*(base40) + (155997/1000000000000 : ℝ)*(base43) + (168461254391/500000000000 : ℝ)*(base54) + (2249913446109/1000000000000 : ℝ)*(major_s3_0) + (17577447579/7812500000 : ℝ)*(major_s3_1) + (1912990937327/1000000000000 : ℝ)*(major_s3_2) + (1940263/100000000000 : ℝ)*(sp_s3_6) + (1357626006469/500000000000 : ℝ)*(sp_s3_7) + (2715919237427/1000000000000 : ℝ)*(sp_s3_8) + (2378996572647/1000000000000 : ℝ)*(sp_s3_9) + (1626341737209/1000000000000 : ℝ)*(sp_s3_13) + (24666313/250000000000 : ℝ)*(sp_s3_20) + (166767123/250000000000 : ℝ)*(sp_s3_21) + (741703625623/500000000000 : ℝ)*(f.failure) + (2715919237427/1000000000000 : ℝ)*(f.sum) + (482992513807399289/14995464540000000000000000000000 : ℝ)*base62 + (1425283726146943/2855300000000000000000000000 : ℝ)*base65 + (88004355239/2136962890625000000000000 : ℝ)*base66 + (4142790709173407/8565900000000000000000000000 : ℝ)*base68 + (4975964808403261/105110731250000000000000000000 : ℝ)*base70 + (524449653063/7362500000000000000000000 : ℝ)*base72 + (119792709874573/437650000000000000000000000 : ℝ)*base74 + (15255947232379/58900000000000000000000000 : ℝ)*base77 + (158520770206195317/644439625000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (5207/6250000000000000 : ℝ)*base87 + (5207/6250000000000000 : ℝ)*base89 + (5207/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-7881/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7881/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7643149837105568587030423/504531510000000000000000000000 : ℝ) := by norm_num
    linear_combination (797853022461/1000000000000 : ℝ)*(base7) + (17790199/1000000000000 : ℝ)*(base21) + (14175205731/200000000000 : ℝ)*(base40) + (605259/62500000000 : ℝ)*(base54) + (9148860493/200000000000 : ℝ)*(base60) + (394054108907/200000000000 : ℝ)*(major_s3_0) + (394054108907/200000000000 : ℝ)*(major_s3_1) + (197026086039/100000000000 : ℝ)*(major_s3_2) + (22405961/200000000000 : ℝ)*(sp_s3_13) + (107099519901/50000000000 : ℝ)*(sp_s3_14) + (2141862840309/1000000000000 : ℝ)*(sp_s3_15) + (2141962923677/1000000000000 : ℝ)*(sp_s3_16) + (419353021623/200000000000 : ℝ)*(sp_s3_20) + (7972357/62500000000 : ℝ)*(sp_s3_22) + (324758449901/250000000000 : ℝ)*(f.failure) + (107099519901/50000000000 : ℝ)*(f.sum) + (20597580254654017/624811022500000000000000000000 : ℝ)*base62 + (128286074928219/285530000000000000000000000 : ℝ)*base64 + (65751760986821/437650000000000000000000000 : ℝ)*base66 + (4337485381941/28553000000000000000000000 : ℝ)*base68 + (641990375172539909/3027189060000000000000000000000 : ℝ)*base70 + (46527587519813/123690000000000000000000000 : ℝ)*base72 + (5421755424701/10941250000000000000000000 : ℝ)*base75 + (363749659807279/742140000000000000000000000 : ℝ)*base76 + (658916555857968211/5413292850000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (37/97656250000000 : ℝ)*base87 + (37/97656250000000 : ℝ)*base89 + (4309/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15171/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15171/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (984377412600861557895650009/187443306750000000000000000000000 : ℝ) := by norm_num
    linear_combination (782679755543/1000000000000 : ℝ)*(base7) + (37963262293/125000000000 : ℝ)*(base40) + (75545331917/1000000000000 : ℝ)*(base43) + (322751/200000000000 : ℝ)*(base50) + (517004780869/200000000000 : ℝ)*(major_s3_0) + (2509478572427/1000000000000 : ℝ)*(major_s3_1) + (517004780869/200000000000 : ℝ)*(major_s3_2) + (6593953/1000000000000 : ℝ)*(sp_s3_0) + (43575533/1000000000000 : ℝ)*(sp_s3_15) + (8093341/1000000000000 : ℝ)*(sp_s3_16) + (2900130385459/1000000000000 : ℝ)*(sp_s3_21) + (743909683949/250000000000 : ℝ)*(sp_s3_22) + (2900128886071/1000000000000 : ℝ)*(sp_s3_23) + (2487031187807/1000000000000 : ℝ)*(sp_s3_27) + (340870286453/200000000000 : ℝ)*(f.failure) + (297568231133/100000000000 : ℝ)*(f.sum) + (5693796303101012171/74977322700000000000000000000000 : ℝ)*base63 + (19954252456307/571060000000000000000000000 : ℝ)*base65 + (768811392883797/1094125000000000000000000000 : ℝ)*base67 + (2005659581442449/1713180000000000000000000000 : ℝ)*base69 + (46803788516303807/756797265000000000000000000000 : ℝ)*base71 + (68727135647927/123690000000000000000000000 : ℝ)*base73 + (50823038783173/109412500000000000000000000 : ℝ)*base75 + (3531477468793/29685600000000000000000000 : ℝ)*base77 + (9033431806778259361/27066464250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (73/2500000000000000 : ℝ)*base86 + (2427/2500000000000000 : ℝ)*base89 + (73/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((37107/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37107/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8753/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8753/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85659/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85659/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7881/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7881/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15171/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15171/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304086_s3 p hpa hpb X hX hprev2

#print axioms solution

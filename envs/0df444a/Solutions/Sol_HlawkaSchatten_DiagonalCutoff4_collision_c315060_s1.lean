-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:56:08.012617+00:00
-- url     : https://prove2.me/submissions/f40fdbe8-08fa-41a8-a5ef-07ecd1ab9f2c

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
theorem collision_support_c315060_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1860485749/10000000000 : ℝ)*x 0 + (84086213/200000000 : ℝ)*x 1 + (-6215244731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1860485749/10000000000 : ℝ)^19 ≤ (11881192720819/100000000000000 : ℝ)^15 := by
    have hnat : (1860485749 : ℕ)^19*100000000000000^15 ≤ 11881192720819^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860485749 10000000000 11881192720819 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84086213/200000000 : ℝ)^19 ≤ (33369272922773/100000000000000 : ℝ)^15 := by
    have hnat : (84086213 : ℕ)^19*100000000000000^15 ≤ 33369272922773^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84086213 200000000 33369272922773 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6215244731/10000000000 : ℝ)^19 ≤ (171092294843/312500000000 : ℝ)^15 := by
    have hnat : (6215244731 : ℕ)^19*312500000000^15 ≤ 171092294843^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6215244731 10000000000 171092294843 312500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1860485749/10000000000 : ℝ), (84086213/200000000 : ℝ), (-6215244731/10000000000 : ℝ)] ![(11881192720819/100000000000000 : ℝ), (33369272922773/100000000000000 : ℝ), (171092294843/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1860485749/10000000000 : ℝ)|^19 ≤ (11881192720819/100000000000000 : ℝ)^15
        have hw : |(-1860485749/10000000000 : ℝ)|=(1860485749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84086213/200000000 : ℝ)|^19 ≤ (33369272922773/100000000000000 : ℝ)^15
        have hw : |(84086213/200000000 : ℝ)|=(84086213/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6215244731/10000000000 : ℝ)|^19 ≤ (171092294843/312500000000 : ℝ)^15
        have hw : |(-6215244731/10000000000 : ℝ)|=(6215244731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4490164961/10000000000 : ℝ)*x 0 + (-534354961/2500000000 : ℝ)*x 1 + (-1149192423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490164961/10000000000 : ℝ)^19 ≤ (36268721135693/100000000000000 : ℝ)^15 := by
    have hnat : (4490164961 : ℕ)^19*100000000000000^15 ≤ 36268721135693^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490164961 10000000000 36268721135693 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534354961/2500000000 : ℝ)^19 ≤ (3541064213737/25000000000000 : ℝ)^15 := by
    have hnat : (534354961 : ℕ)^19*25000000000000^15 ≤ 3541064213737^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534354961 2500000000 3541064213737 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149192423/2000000000 : ℝ)^19 ≤ (49567021990797/100000000000000 : ℝ)^15 := by
    have hnat : (1149192423 : ℕ)^19*100000000000000^15 ≤ 49567021990797^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149192423 2000000000 49567021990797 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490164961/10000000000 : ℝ), (-534354961/2500000000 : ℝ), (-1149192423/2000000000 : ℝ)] ![(36268721135693/100000000000000 : ℝ), (3541064213737/25000000000000 : ℝ), (49567021990797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490164961/10000000000 : ℝ)|^19 ≤ (36268721135693/100000000000000 : ℝ)^15
        have hw : |(4490164961/10000000000 : ℝ)|=(4490164961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534354961/2500000000 : ℝ)|^19 ≤ (3541064213737/25000000000000 : ℝ)^15
        have hw : |(-534354961/2500000000 : ℝ)|=(534354961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1149192423/2000000000 : ℝ)|^19 ≤ (49567021990797/100000000000000 : ℝ)^15
        have hw : |(-1149192423/2000000000 : ℝ)|=(1149192423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (584528467/1250000000 : ℝ)*x 0 + (5925705161/10000000000 : ℝ)*x 1 + (331863001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (584528467/1250000000 : ℝ)^19 ≤ (38182804843139/100000000000000 : ℝ)^15 := by
    have hnat : (584528467 : ℕ)^19*100000000000000^15 ≤ 38182804843139^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584528467 1250000000 38182804843139 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5925705161/10000000000 : ℝ)^19 ≤ (51539165537057/100000000000000 : ℝ)^15 := by
    have hnat : (5925705161 : ℕ)^19*100000000000000^15 ≤ 51539165537057^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925705161 10000000000 51539165537057 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (331863001/2000000000 : ℝ)^19 ≤ (10278029612387/100000000000000 : ℝ)^15 := by
    have hnat : (331863001 : ℕ)^19*100000000000000^15 ≤ 10278029612387^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331863001 2000000000 10278029612387 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(584528467/1250000000 : ℝ), (5925705161/10000000000 : ℝ), (331863001/2000000000 : ℝ)] ![(38182804843139/100000000000000 : ℝ), (51539165537057/100000000000000 : ℝ), (10278029612387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(584528467/1250000000 : ℝ)|^19 ≤ (38182804843139/100000000000000 : ℝ)^15
        have hw : |(584528467/1250000000 : ℝ)|=(584528467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5925705161/10000000000 : ℝ)|^19 ≤ (51539165537057/100000000000000 : ℝ)^15
        have hw : |(5925705161/10000000000 : ℝ)|=(5925705161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(331863001/2000000000 : ℝ)|^19 ≤ (10278029612387/100000000000000 : ℝ)^15
        have hw : |(331863001/2000000000 : ℝ)|=(331863001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1743032549/10000000000 : ℝ)*x 0 + (479141717/1250000000 : ℝ)*x 1 + (-1656625707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1743032549/10000000000 : ℝ)^19 ≤ (42731387793/390625000000 : ℝ)^15 := by
    have hnat : (1743032549 : ℕ)^19*390625000000^15 ≤ 42731387793^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743032549 10000000000 42731387793 390625000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479141717/1250000000 : ℝ)^19 ≤ (29682583462577/100000000000000 : ℝ)^15 := by
    have hnat : (479141717 : ℕ)^19*100000000000000^15 ≤ 29682583462577^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479141717 1250000000 29682583462577 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1656625707/2500000000 : ℝ)^19 ≤ (1855568163941/3125000000000 : ℝ)^15 := by
    have hnat : (1656625707 : ℕ)^19*3125000000000^15 ≤ 1855568163941^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656625707 2500000000 1855568163941 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1743032549/10000000000 : ℝ), (479141717/1250000000 : ℝ), (-1656625707/2500000000 : ℝ)] ![(42731387793/390625000000 : ℝ), (29682583462577/100000000000000 : ℝ), (1855568163941/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1743032549/10000000000 : ℝ)|^19 ≤ (42731387793/390625000000 : ℝ)^15
        have hw : |(-1743032549/10000000000 : ℝ)|=(1743032549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(479141717/1250000000 : ℝ)|^19 ≤ (29682583462577/100000000000000 : ℝ)^15
        have hw : |(479141717/1250000000 : ℝ)|=(479141717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1656625707/2500000000 : ℝ)|^19 ≤ (1855568163941/3125000000000 : ℝ)^15
        have hw : |(-1656625707/2500000000 : ℝ)|=(1656625707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2052433587/5000000000 : ℝ)*x 0 + (-1403384781/10000000000 : ℝ)*x 1 + (-1324175053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052433587/5000000000 : ℝ)^19 ≤ (4046587019107/12500000000000 : ℝ)^15 := by
    have hnat : (2052433587 : ℕ)^19*12500000000000^15 ≤ 4046587019107^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052433587 5000000000 4046587019107 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403384781/10000000000 : ℝ)^19 ≤ (8312989510823/100000000000000 : ℝ)^15 := by
    have hnat : (1403384781 : ℕ)^19*100000000000000^15 ≤ 8312989510823^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403384781 10000000000 8312989510823 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324175053/2000000000 : ℝ)^19 ≤ (59314314318979/100000000000000 : ℝ)^15 := by
    have hnat : (1324175053 : ℕ)^19*100000000000000^15 ≤ 59314314318979^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324175053 2000000000 59314314318979 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052433587/5000000000 : ℝ), (-1403384781/10000000000 : ℝ), (-1324175053/2000000000 : ℝ)] ![(4046587019107/12500000000000 : ℝ), (8312989510823/100000000000000 : ℝ), (59314314318979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052433587/5000000000 : ℝ)|^19 ≤ (4046587019107/12500000000000 : ℝ)^15
        have hw : |(2052433587/5000000000 : ℝ)|=(2052433587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1403384781/10000000000 : ℝ)|^19 ≤ (8312989510823/100000000000000 : ℝ)^15
        have hw : |(-1403384781/10000000000 : ℝ)|=(1403384781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324175053/2000000000 : ℝ)|^19 ≤ (59314314318979/100000000000000 : ℝ)^15
        have hw : |(-1324175053/2000000000 : ℝ)|=(1324175053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (171838359/400000000 : ℝ)*x 0 + (419774169/625000000 : ℝ)*x 1 + (246154067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171838359/400000000 : ℝ)^19 ≤ (34293316848843/100000000000000 : ℝ)^15 := by
    have hnat : (171838359 : ℕ)^19*100000000000000^15 ≤ 34293316848843^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171838359 400000000 34293316848843 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419774169/625000000 : ℝ)^19 ≤ (30200111686127/50000000000000 : ℝ)^15 := by
    have hnat : (419774169 : ℕ)^19*50000000000000^15 ≤ 30200111686127^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419774169 625000000 30200111686127 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246154067/2500000000 : ℝ)^19 ≤ (5306459763443/100000000000000 : ℝ)^15 := by
    have hnat : (246154067 : ℕ)^19*100000000000000^15 ≤ 5306459763443^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246154067 2500000000 5306459763443 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171838359/400000000 : ℝ), (419774169/625000000 : ℝ), (246154067/2500000000 : ℝ)] ![(34293316848843/100000000000000 : ℝ), (30200111686127/50000000000000 : ℝ), (5306459763443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171838359/400000000 : ℝ)|^19 ≤ (34293316848843/100000000000000 : ℝ)^15
        have hw : |(171838359/400000000 : ℝ)|=(171838359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(419774169/625000000 : ℝ)|^19 ≤ (30200111686127/50000000000000 : ℝ)^15
        have hw : |(419774169/625000000 : ℝ)|=(419774169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(246154067/2500000000 : ℝ)|^19 ≤ (5306459763443/100000000000000 : ℝ)^15
        have hw : |(246154067/2500000000 : ℝ)|=(246154067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (63048001/100000000 : ℝ)*x 0 + (5249448627/10000000000 : ℝ)*x 1 + (-11134273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63048001/100000000 : ℝ)^19 ≤ (11150140403377/20000000000000 : ℝ)^15 := by
    have hnat : (63048001 : ℕ)^19*20000000000000^15 ≤ 11150140403377^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63048001 100000000 11150140403377 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5249448627/10000000000 : ℝ)^19 ≤ (22102802593549/50000000000000 : ℝ)^15 := by
    have hnat : (5249448627 : ℕ)^19*50000000000000^15 ≤ 22102802593549^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249448627 10000000000 22102802593549 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11134273/5000000000 : ℝ)^19 ≤ (43692781287/100000000000000 : ℝ)^15 := by
    have hnat : (11134273 : ℕ)^19*100000000000000^15 ≤ 43692781287^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11134273 5000000000 43692781287 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63048001/100000000 : ℝ), (5249448627/10000000000 : ℝ), (-11134273/5000000000 : ℝ)] ![(11150140403377/20000000000000 : ℝ), (22102802593549/50000000000000 : ℝ), (43692781287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63048001/100000000 : ℝ)|^19 ≤ (11150140403377/20000000000000 : ℝ)^15
        have hw : |(63048001/100000000 : ℝ)|=(63048001/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5249448627/10000000000 : ℝ)|^19 ≤ (22102802593549/50000000000000 : ℝ)^15
        have hw : |(5249448627/10000000000 : ℝ)|=(5249448627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11134273/5000000000 : ℝ)|^19 ≤ (43692781287/100000000000000 : ℝ)^15
        have hw : |(-11134273/5000000000 : ℝ)|=(11134273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-52844637/500000000 : ℝ)*x 0 + (510006313/1250000000 : ℝ)*x 1 + (-3431293259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52844637/500000000 : ℝ)^19 ≤ (725575324789/12500000000000 : ℝ)^15 := by
    have hnat : (52844637 : ℕ)^19*12500000000000^15 ≤ 725575324789^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52844637 500000000 725575324789 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510006313/1250000000 : ℝ)^19 ≤ (16062495548921/50000000000000 : ℝ)^15 := by
    have hnat : (510006313 : ℕ)^19*50000000000000^15 ≤ 16062495548921^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510006313 1250000000 16062495548921 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3431293259/5000000000 : ℝ)^19 ≤ (62070406289769/100000000000000 : ℝ)^15 := by
    have hnat : (3431293259 : ℕ)^19*100000000000000^15 ≤ 62070406289769^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431293259 5000000000 62070406289769 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52844637/500000000 : ℝ), (510006313/1250000000 : ℝ), (-3431293259/5000000000 : ℝ)] ![(725575324789/12500000000000 : ℝ), (16062495548921/50000000000000 : ℝ), (62070406289769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52844637/500000000 : ℝ)|^19 ≤ (725575324789/12500000000000 : ℝ)^15
        have hw : |(-52844637/500000000 : ℝ)|=(52844637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(510006313/1250000000 : ℝ)|^19 ≤ (16062495548921/50000000000000 : ℝ)^15
        have hw : |(510006313/1250000000 : ℝ)|=(510006313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3431293259/5000000000 : ℝ)|^19 ≤ (62070406289769/100000000000000 : ℝ)^15
        have hw : |(-3431293259/5000000000 : ℝ)|=(3431293259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3716028457/10000000000 : ℝ)*x 0 + (-776938943/5000000000 : ℝ)*x 1 + (-3428370733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3716028457/10000000000 : ℝ)^19 ≤ (28538650929101/100000000000000 : ℝ)^15 := by
    have hnat : (3716028457 : ℕ)^19*100000000000000^15 ≤ 28538650929101^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716028457 10000000000 28538650929101 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776938943/5000000000 : ℝ)^19 ≤ (9457900098571/100000000000000 : ℝ)^15 := by
    have hnat : (776938943 : ℕ)^19*100000000000000^15 ≤ 9457900098571^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776938943 5000000000 9457900098571 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3428370733/5000000000 : ℝ)^19 ≤ (62003448957303/100000000000000 : ℝ)^15 := by
    have hnat : (3428370733 : ℕ)^19*100000000000000^15 ≤ 62003448957303^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3428370733 5000000000 62003448957303 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3716028457/10000000000 : ℝ), (-776938943/5000000000 : ℝ), (-3428370733/5000000000 : ℝ)] ![(28538650929101/100000000000000 : ℝ), (9457900098571/100000000000000 : ℝ), (62003448957303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3716028457/10000000000 : ℝ)|^19 ≤ (28538650929101/100000000000000 : ℝ)^15
        have hw : |(3716028457/10000000000 : ℝ)|=(3716028457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776938943/5000000000 : ℝ)|^19 ≤ (9457900098571/100000000000000 : ℝ)^15
        have hw : |(-776938943/5000000000 : ℝ)|=(776938943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3428370733/5000000000 : ℝ)|^19 ≤ (62003448957303/100000000000000 : ℝ)^15
        have hw : |(-3428370733/5000000000 : ℝ)|=(3428370733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5915362543/10000000000 : ℝ)*x 0 + (1281049847/2500000000 : ℝ)*x 1 + (1041951123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5915362543/10000000000 : ℝ)^19 ≤ (25712624201913/50000000000000 : ℝ)^15 := by
    have hnat : (5915362543 : ℕ)^19*50000000000000^15 ≤ 25712624201913^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5915362543 10000000000 25712624201913 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281049847/2500000000 : ℝ)^19 ≤ (21436948436959/50000000000000 : ℝ)^15 := by
    have hnat : (1281049847 : ℕ)^19*50000000000000^15 ≤ 21436948436959^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281049847 2500000000 21436948436959 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041951123/10000000000 : ℝ)^19 ≤ (5700854711219/100000000000000 : ℝ)^15 := by
    have hnat : (1041951123 : ℕ)^19*100000000000000^15 ≤ 5700854711219^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041951123 10000000000 5700854711219 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5915362543/10000000000 : ℝ), (1281049847/2500000000 : ℝ), (1041951123/10000000000 : ℝ)] ![(25712624201913/50000000000000 : ℝ), (21436948436959/50000000000000 : ℝ), (5700854711219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5915362543/10000000000 : ℝ)|^19 ≤ (25712624201913/50000000000000 : ℝ)^15
        have hw : |(5915362543/10000000000 : ℝ)|=(5915362543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281049847/2500000000 : ℝ)|^19 ≤ (21436948436959/50000000000000 : ℝ)^15
        have hw : |(1281049847/2500000000 : ℝ)|=(1281049847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041951123/10000000000 : ℝ)|^19 ≤ (5700854711219/100000000000000 : ℝ)^15
        have hw : |(1041951123/10000000000 : ℝ)|=(1041951123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7903448213/10000000000 : ℝ)*x 0 + (682716777/2000000000 : ℝ)*x 1 + (-28376391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7903448213/10000000000 : ℝ)^19 ≤ (2319624729657/3125000000000 : ℝ)^15 := by
    have hnat : (7903448213 : ℕ)^19*3125000000000^15 ≤ 2319624729657^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7903448213 10000000000 2319624729657 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682716777/2000000000 : ℝ)^19 ≤ (6407275667269/25000000000000 : ℝ)^15 := by
    have hnat : (682716777 : ℕ)^19*25000000000000^15 ≤ 6407275667269^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682716777 2000000000 6407275667269 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28376391/5000000000 : ℝ)^19 ≤ (17863247263/12500000000000 : ℝ)^15 := by
    have hnat : (28376391 : ℕ)^19*12500000000000^15 ≤ 17863247263^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28376391 5000000000 17863247263 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7903448213/10000000000 : ℝ), (682716777/2000000000 : ℝ), (-28376391/5000000000 : ℝ)] ![(2319624729657/3125000000000 : ℝ), (6407275667269/25000000000000 : ℝ), (17863247263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7903448213/10000000000 : ℝ)|^19 ≤ (2319624729657/3125000000000 : ℝ)^15
        have hw : |(7903448213/10000000000 : ℝ)|=(7903448213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682716777/2000000000 : ℝ)|^19 ≤ (6407275667269/25000000000000 : ℝ)^15
        have hw : |(682716777/2000000000 : ℝ)|=(682716777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28376391/5000000000 : ℝ)|^19 ≤ (17863247263/12500000000000 : ℝ)^15
        have hw : |(-28376391/5000000000 : ℝ)|=(28376391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-667305709/10000000000 : ℝ)*x 0 + (1094622941/2000000000 : ℝ)*x 1 + (-2899772407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667305709/10000000000 : ℝ)^19 ≤ (405248557373/12500000000000 : ℝ)^15 := by
    have hnat : (667305709 : ℕ)^19*12500000000000^15 ≤ 405248557373^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667305709 10000000000 405248557373 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094622941/2000000000 : ℝ)^19 ≤ (46604776562547/100000000000000 : ℝ)^15 := by
    have hnat : (1094622941 : ℕ)^19*100000000000000^15 ≤ 46604776562547^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094622941 2000000000 46604776562547 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899772407/5000000000 : ℝ)^19 ≤ (50153234964031/100000000000000 : ℝ)^15 := by
    have hnat : (2899772407 : ℕ)^19*100000000000000^15 ≤ 50153234964031^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899772407 5000000000 50153234964031 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-667305709/10000000000 : ℝ), (1094622941/2000000000 : ℝ), (-2899772407/5000000000 : ℝ)] ![(405248557373/12500000000000 : ℝ), (46604776562547/100000000000000 : ℝ), (50153234964031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-667305709/10000000000 : ℝ)|^19 ≤ (405248557373/12500000000000 : ℝ)^15
        have hw : |(-667305709/10000000000 : ℝ)|=(667305709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094622941/2000000000 : ℝ)|^19 ≤ (46604776562547/100000000000000 : ℝ)^15
        have hw : |(1094622941/2000000000 : ℝ)|=(1094622941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2899772407/5000000000 : ℝ)|^19 ≤ (50153234964031/100000000000000 : ℝ)^15
        have hw : |(-2899772407/5000000000 : ℝ)|=(2899772407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2876983163/5000000000 : ℝ)*x 0 + (-939146421/10000000000 : ℝ)*x 1 + (-5356214761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2876983163/5000000000 : ℝ)^19 ≤ (12413624631259/25000000000000 : ℝ)^15 := by
    have hnat : (2876983163 : ℕ)^19*25000000000000^15 ≤ 12413624631259^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876983163 5000000000 12413624631259 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939146421/10000000000 : ℝ)^19 ≤ (4997991615133/100000000000000 : ℝ)^15 := by
    have hnat : (939146421 : ℕ)^19*100000000000000^15 ≤ 4997991615133^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939146421 10000000000 4997991615133 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5356214761/10000000000 : ℝ)^19 ≤ (906950197163/2000000000000 : ℝ)^15 := by
    have hnat : (5356214761 : ℕ)^19*2000000000000^15 ≤ 906950197163^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356214761 10000000000 906950197163 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2876983163/5000000000 : ℝ), (-939146421/10000000000 : ℝ), (-5356214761/10000000000 : ℝ)] ![(12413624631259/25000000000000 : ℝ), (4997991615133/100000000000000 : ℝ), (906950197163/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2876983163/5000000000 : ℝ)|^19 ≤ (12413624631259/25000000000000 : ℝ)^15
        have hw : |(2876983163/5000000000 : ℝ)|=(2876983163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-939146421/10000000000 : ℝ)|^19 ≤ (4997991615133/100000000000000 : ℝ)^15
        have hw : |(-939146421/10000000000 : ℝ)|=(939146421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5356214761/10000000000 : ℝ)|^19 ≤ (906950197163/2000000000000 : ℝ)^15
        have hw : |(-5356214761/10000000000 : ℝ)|=(5356214761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1059709349/2500000000 : ℝ)*x 0 + (6474637631/10000000000 : ℝ)*x 1 + (1444603661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059709349/2500000000 : ℝ)^19 ≤ (33716764485419/100000000000000 : ℝ)^15 := by
    have hnat : (1059709349 : ℕ)^19*100000000000000^15 ≤ 33716764485419^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059709349 2500000000 33716764485419 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6474637631/10000000000 : ℝ)^19 ≤ (28829886279309/50000000000000 : ℝ)^15 := by
    have hnat : (6474637631 : ℕ)^19*50000000000000^15 ≤ 28829886279309^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6474637631 10000000000 28829886279309 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444603661/10000000000 : ℝ)^19 ≤ (4311731464901/50000000000000 : ℝ)^15 := by
    have hnat : (1444603661 : ℕ)^19*50000000000000^15 ≤ 4311731464901^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444603661 10000000000 4311731464901 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059709349/2500000000 : ℝ), (6474637631/10000000000 : ℝ), (1444603661/10000000000 : ℝ)] ![(33716764485419/100000000000000 : ℝ), (28829886279309/50000000000000 : ℝ), (4311731464901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059709349/2500000000 : ℝ)|^19 ≤ (33716764485419/100000000000000 : ℝ)^15
        have hw : |(1059709349/2500000000 : ℝ)|=(1059709349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6474637631/10000000000 : ℝ)|^19 ≤ (28829886279309/50000000000000 : ℝ)^15
        have hw : |(6474637631/10000000000 : ℝ)|=(6474637631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1444603661/10000000000 : ℝ)|^19 ≤ (4311731464901/50000000000000 : ℝ)^15
        have hw : |(1444603661/10000000000 : ℝ)|=(1444603661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315060_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (260863593/312500000 : ℝ)*x 0 + (2816831363/10000000000 : ℝ)*x 1 + (-58384663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260863593/312500000 : ℝ)^19 ≤ (79551255232389/100000000000000 : ℝ)^15 := by
    have hnat : (260863593 : ℕ)^19*100000000000000^15 ≤ 79551255232389^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260863593 312500000 79551255232389 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816831363/10000000000 : ℝ)^19 ≤ (2511541854129/12500000000000 : ℝ)^15 := by
    have hnat : (2816831363 : ℕ)^19*12500000000000^15 ≤ 2511541854129^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816831363 10000000000 2511541854129 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58384663/5000000000 : ℝ)^19 ≤ (89102479259/25000000000000 : ℝ)^15 := by
    have hnat : (58384663 : ℕ)^19*25000000000000^15 ≤ 89102479259^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58384663 5000000000 89102479259 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260863593/312500000 : ℝ), (2816831363/10000000000 : ℝ), (-58384663/5000000000 : ℝ)] ![(79551255232389/100000000000000 : ℝ), (2511541854129/12500000000000 : ℝ), (89102479259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260863593/312500000 : ℝ)|^19 ≤ (79551255232389/100000000000000 : ℝ)^15
        have hw : |(260863593/312500000 : ℝ)|=(260863593/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816831363/10000000000 : ℝ)|^19 ≤ (2511541854129/12500000000000 : ℝ)^15
        have hw : |(2816831363/10000000000 : ℝ)|=(2816831363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58384663/5000000000 : ℝ)|^19 ≤ (89102479259/25000000000000 : ℝ)^15
        have hw : |(-58384663/5000000000 : ℝ)|=(58384663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315060_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((3229/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3229/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80339/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80339/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71427/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5283/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5283/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28247/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28247/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10081/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10081/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (3229/4000 : ℝ) ^ (75/16 : ℝ) ≤ (1832610860636057623/5000000000000000000 : ℝ) := by
    have hpowers : (3229/4000 : ℝ)^75 ≤ (1832610860636057623/5000000000000000000 : ℝ)^16 := by
      have hnat : (3229 : ℕ)^75*5000000000000000000^16 ≤ 1832610860636057623^16*4000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3229 4000 1832610860636057623 5000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3229/4000 : ℝ)) (X := (1832610860636057623/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (6832610860636057623/5000000000000000000 : ℝ) ≤ (534443209360779/500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (6832610860636057623/5000000000000000000 : ℝ)^16 ≤ (534443209360779/500000000000000 : ℝ)^75 := by
      have hnat : (6832610860636057623 : ℕ)^16*500000000000000^75 ≤ 534443209360779^75*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6832610860636057623 5000000000000000000 534443209360779 500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (534443209360779/500000000000000 : ℝ)) (X := (6832610860636057623/5000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (4332610860636057623/2500000000000000000 : ℝ) ≤ (89957225251203/80000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (4332610860636057623/2500000000000000000 : ℝ)^16 ≤ (89957225251203/80000000000000 : ℝ)^75 := by
      have hnat : (4332610860636057623 : ℕ)^16*80000000000000^75 ≤ 89957225251203^75*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4332610860636057623 2500000000000000000 89957225251203 80000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (89957225251203/80000000000000 : ℝ)) (X := (4332610860636057623/2500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(34443209360779/403625000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(111157793836959/1614500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (3229/4000 : ℝ)) (alpha := (34443209360779/403625000000000 : ℝ)) (beta := (111157793836959/1614500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3229/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(34443209360779/403625000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(111157793836959/1614500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (80339/100000 : ℝ) ^ (75/16 : ℝ) ≤ (4479737997250938441/12500000000000000000 : ℝ) := by
    have hpowers : (80339/100000 : ℝ)^75 ≤ (4479737997250938441/12500000000000000000 : ℝ)^16 := by
      have hnat : (80339 : ℕ)^75*12500000000000000000^16 ≤ 4479737997250938441^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80339 100000 4479737997250938441 12500000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80339/100000 : ℝ)) (X := (4479737997250938441/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (16979737997250938441/12500000000000000000 : ℝ) ≤ (10675243925536939/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (16979737997250938441/12500000000000000000 : ℝ)^16 ≤ (10675243925536939/10000000000000000 : ℝ)^75 := by
      have hnat : (16979737997250938441 : ℕ)^16*10000000000000000^75 ≤ 10675243925536939^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16979737997250938441 12500000000000000000 10675243925536939 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10675243925536939/10000000000000000 : ℝ)) (X := (16979737997250938441/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10729737997250938441/6250000000000000000 : ℝ) ≤ (5611013052847001/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (10729737997250938441/6250000000000000000 : ℝ)^16 ≤ (5611013052847001/5000000000000000 : ℝ)^75 := by
      have hnat : (10729737997250938441 : ℕ)^16*5000000000000000^75 ≤ 5611013052847001^75*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10729737997250938441 6250000000000000000 5611013052847001 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5611013052847001/5000000000000000 : ℝ)) (X := (10729737997250938441/6250000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(675243925536939/8033900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(546782180157063/8033900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (80339/100000 : ℝ)) (alpha := (675243925536939/8033900000000000 : ℝ)) (beta := (546782180157063/8033900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (80339/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(675243925536939/8033900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(546782180157063/8033900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (71427/100000 : ℝ) ^ (75/16 : ℝ) ≤ (5163213152010546947/25000000000000000000 : ℝ) := by
    have hpowers : (71427/100000 : ℝ)^75 ≤ (5163213152010546947/25000000000000000000 : ℝ)^16 := by
      have hnat : (71427 : ℕ)^75*25000000000000000000^16 ≤ 5163213152010546947^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71427 100000 5163213152010546947 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71427/100000 : ℝ)) (X := (5163213152010546947/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (30163213152010546947/25000000000000000000 : ℝ) ≤ (5204328374104849/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (30163213152010546947/25000000000000000000 : ℝ)^16 ≤ (5204328374104849/5000000000000000 : ℝ)^75 := by
      have hnat : (30163213152010546947 : ℕ)^16*5000000000000000^75 ≤ 5204328374104849^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30163213152010546947 25000000000000000000 5204328374104849 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5204328374104849/5000000000000000 : ℝ)) (X := (30163213152010546947/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (17663213152010546947/12500000000000000000 : ℝ) ≤ (1076549661316361/1000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (17663213152010546947/12500000000000000000 : ℝ)^16 ≤ (1076549661316361/1000000000000000 : ℝ)^75 := by
      have hnat : (17663213152010546947 : ℕ)^16*1000000000000000^75 ≤ 1076549661316361^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17663213152010546947 12500000000000000000 1076549661316361 1000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1076549661316361/1000000000000000 : ℝ)) (X := (17663213152010546947/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(204328374104849/3571350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14868327706413/297612500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (71427/100000 : ℝ)) (alpha := (204328374104849/3571350000000000 : ℝ)) (beta := (14868327706413/297612500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (71427/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(204328374104849/3571350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14868327706413/297612500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1860485749/10000000000 : ℝ)*X 0 0+(84086213/200000000 : ℝ)*X 0 1+(-6215244731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4490164961/10000000000 : ℝ)*X 1 0+(-534354961/2500000000 : ℝ)*X 1 1+(-1149192423/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((584528467/1250000000 : ℝ)*X 2 0+(5925705161/10000000000 : ℝ)*X 2 1+(331863001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1743032549/10000000000 : ℝ)*X 0 0+(479141717/1250000000 : ℝ)*X 0 1+(-1656625707/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2052433587/5000000000 : ℝ)*X 1 0+(-1403384781/10000000000 : ℝ)*X 1 1+(-1324175053/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((171838359/400000000 : ℝ)*X 2 0+(419774169/625000000 : ℝ)*X 2 1+(246154067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((63048001/100000000 : ℝ)*X 0 0+(5249448627/10000000000 : ℝ)*X 0 1+(-11134273/5000000000 : ℝ)*X 0 2+(63048001/100000000 : ℝ)*X 1 0+(5249448627/10000000000 : ℝ)*X 1 1+(-11134273/5000000000 : ℝ)*X 1 2+(63048001/100000000 : ℝ)*X 2 0+(5249448627/10000000000 : ℝ)*X 2 1+(-11134273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-52844637/500000000 : ℝ)*X 0 0+(510006313/1250000000 : ℝ)*X 0 1+(-3431293259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3716028457/10000000000 : ℝ)*X 1 0+(-776938943/5000000000 : ℝ)*X 1 1+(-3428370733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5915362543/10000000000 : ℝ)*X 2 0+(1281049847/2500000000 : ℝ)*X 2 1+(1041951123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7903448213/10000000000 : ℝ)*X 0 0+(682716777/2000000000 : ℝ)*X 0 1+(-28376391/5000000000 : ℝ)*X 0 2+(7903448213/10000000000 : ℝ)*X 1 0+(682716777/2000000000 : ℝ)*X 1 1+(-28376391/5000000000 : ℝ)*X 1 2+(7903448213/10000000000 : ℝ)*X 2 0+(682716777/2000000000 : ℝ)*X 2 1+(-28376391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-667305709/10000000000 : ℝ)*X 0 0+(1094622941/2000000000 : ℝ)*X 0 1+(-2899772407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2876983163/5000000000 : ℝ)*X 1 0+(-939146421/10000000000 : ℝ)*X 1 1+(-5356214761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1059709349/2500000000 : ℝ)*X 2 0+(6474637631/10000000000 : ℝ)*X 2 1+(1444603661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((260863593/312500000 : ℝ)*X 0 0+(2816831363/10000000000 : ℝ)*X 0 1+(-58384663/5000000000 : ℝ)*X 0 2+(260863593/312500000 : ℝ)*X 1 0+(2816831363/10000000000 : ℝ)*X 1 1+(-58384663/5000000000 : ℝ)*X 1 2+(260863593/312500000 : ℝ)*X 2 0+(2816831363/10000000000 : ℝ)*X 2 1+(-58384663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((5283/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5283/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4447838906512840919480010113383/386025184342437500000000000000000000 : ℝ) := by norm_num
    linear_combination (221718303981/1000000000000 : ℝ)*(base7) + (251894685639/500000000000 : ℝ)*(base59) + (2788839931093/500000000000 : ℝ)*(major_s1_0) + (2788839931093/500000000000 : ℝ)*(major_s1_1) + (2788839931093/500000000000 : ℝ)*(major_s1_2) + (44872507/1000000000000 : ℝ)*(sp_s1_0) + (950479/40000000000 : ℝ)*(sp_s1_1) + (1566545526609/200000000000 : ℝ)*(sp_s1_7) + (1958185086071/250000000000 : ℝ)*(sp_s1_8) + (3916421365489/500000000000 : ℝ)*(sp_s1_9) + (1707593320337/500000000000 : ℝ)*(sp_s1_13) + (10824623/100000000000 : ℝ)*(sp_s1_14) + (116645523/1000000000000 : ℝ)*(sp_s1_15) + (7604161/200000000000 : ℝ)*(sp_s1_23) + (1596734168347/500000000000 : ℝ)*(f.failure) + (7832880751783/1000000000000 : ℝ)*(f.sum) + (5276139865341440839/57383737530000000000000000000000 : ℝ)*base63 + (331887669581067/297612500000000000000000000 : ℝ)*base65 + (1488195337574773/2008475000000000000000000000 : ℝ)*base66 + (691679899526911/892837500000000000000000000 : ℝ)*base69 + (271740132748549161/600619226562500000000000000000 : ℝ)*base71 + (304225390335619/403625000000000000000000000 : ℝ)*base72 + (1501074176896977/4016950000000000000000000000 : ℝ)*base75 + (241125101058663/807250000000000000000000000 : ℝ)*base77 + (1627037816545562073/64853657750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (18673/50000000000000000 : ℝ)*base87 + (18673/50000000000000000 : ℝ)*base89 + (18673/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28247/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28247/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4015380699931374964694017866117/308820147473950000000000000000000000 : ℝ) := by norm_num
    linear_combination (95611131349/200000000000 : ℝ)*(base7) + (731987/500000000000 : ℝ)*(base39) + (21796754951/1000000000000 : ℝ)*(base59) + (739220514531/200000000000 : ℝ)*(major_s1_0) + (739220514531/200000000000 : ℝ)*(major_s1_1) + (739220514531/200000000000 : ℝ)*(major_s1_2) + (30262697/1000000000000 : ℝ)*(sp_s1_2) + (25455457/500000000000 : ℝ)*(sp_s1_7) + (102587797/1000000000000 : ℝ)*(sp_s1_8) + (1249452767849/250000000000 : ℝ)*(sp_s1_14) + (4997759394513/1000000000000 : ℝ)*(sp_s1_15) + (4997831719613/1000000000000 : ℝ)*(sp_s1_16) + (2594185904953/1000000000000 : ℝ)*(sp_s1_20) + (51896803/1000000000000 : ℝ)*(sp_s1_27) + (2116182145011/1000000000000 : ℝ)*(f.failure) + (499786198231/100000000000 : ℝ)*(f.sum) + (10584599776480094507/38255825020000000000000000000000 : ℝ)*base62 + (1777013877611/4761800000000000000000000 : ℝ)*base65 + (92164134634303/321356000000000000000000000 : ℝ)*base66 + (4187904592051/238090000000000000000000000 : ℝ)*base68 + (335106610728809047/3843963050000000000000000000000 : ℝ)*base71 + (57155104191541/322900000000000000000000000 : ℝ)*base72 + (4484070780899/321356000000000000000000000 : ℝ)*base74 + (29810713990823/161450000000000000000000000 : ℝ)*base77 + (948944476626268429/6485365775000000000000000000000 : ℝ)*base79 + (23751/100000000000000000 : ℝ)*base86 + (23751/100000000000000000 : ℝ)*base88 + (23751/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10081/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10081/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (411360280726736016466038881/47819781275000000000000000000000 : ℝ) := by norm_num
    linear_combination (1810876911/250000000000 : ℝ)*(base7) + (10001677/1000000000000 : ℝ)*(base11) + (16064078737/62500000000 : ℝ)*(base39) + (3114518319/100000000000 : ℝ)*(base59) + (514491072499/125000000000 : ℝ)*(major_s1_0) + (514491072499/125000000000 : ℝ)*(major_s1_1) + (514491072499/125000000000 : ℝ)*(major_s1_2) + (21136969/1000000000000 : ℝ)*(sp_s1_0) + (13457733/1000000000000 : ℝ)*(sp_s1_2) + (26757373/250000000000 : ℝ)*(sp_s1_9) + (2935528711137/500000000000 : ℝ)*(sp_s1_21) + (146777214023/25000000000 : ℝ)*(sp_s1_22) + (2935484036847/500000000000 : ℝ)*(sp_s1_23) + (590948651087/250000000000 : ℝ)*(sp_s1_27) + (18410555443/7812500000 : ℝ)*(f.failure) + (146777214023/25000000000 : ℝ)*(f.sum) + (15030186324059345213/57383737530000000000000000000000 : ℝ)*base62 + (296421091699/18600781250000000000000000 : ℝ)*base65 + (522808329556733/4016950000000000000000000000 : ℝ)*base67 + (172194770462059/446418750000000000000000000 : ℝ)*base68 + (173669967420681039/4804953812500000000000000000000 : ℝ)*base70 + (5562936965259/201812500000000000000000000 : ℝ)*base72 + (14686969071517/125529687500000000000000000 : ℝ)*base75 + (407426755623761/807250000000000000000000000 : ℝ)*base77 + (3766614279704009631/64853657750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (187/781250000000000 : ℝ)*base87 + (187/781250000000000 : ℝ)*base89 + (187/781250000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((3229/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3229/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80339/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80339/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-71427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-71427/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5283/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5283/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28247/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28247/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10081/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10081/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315060_s1 p hpa hpb X hX hprev0

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301053_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:31:03.337952+00:00
-- url     : https://prove2.me/submissions/32c733df-4d82-401f-8142-444f01353878

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
theorem collision_support_c301053_s5_s5_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-400322361/2000000000 : ℝ)*x 0 + (5336802767/10000000000 : ℝ)*x 1 + (2724402501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400322361/2000000000 : ℝ)^65 ≤ (2367494535617/20000000000000 : ℝ)^49 := by
    have hnat : (400322361 : ℕ)^65*20000000000000^49 ≤ 2367494535617^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400322361 2000000000 2367494535617 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5336802767/10000000000 : ℝ)^65 ≤ (10868512503723/25000000000000 : ℝ)^49 := by
    have hnat : (5336802767 : ℕ)^65*25000000000000^49 ≤ 10868512503723^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336802767 10000000000 10868512503723 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724402501/5000000000 : ℝ)^65 ≤ (44688477297093/100000000000000 : ℝ)^49 := by
    have hnat : (2724402501 : ℕ)^65*100000000000000^49 ≤ 44688477297093^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724402501 5000000000 44688477297093 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400322361/2000000000 : ℝ), (5336802767/10000000000 : ℝ), (2724402501/5000000000 : ℝ)] ![(2367494535617/20000000000000 : ℝ), (10868512503723/25000000000000 : ℝ), (44688477297093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400322361/2000000000 : ℝ)|^65 ≤ (2367494535617/20000000000000 : ℝ)^49
        have hw : |(-400322361/2000000000 : ℝ)|=(400322361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5336802767/10000000000 : ℝ)|^65 ≤ (10868512503723/25000000000000 : ℝ)^49
        have hw : |(5336802767/10000000000 : ℝ)|=(5336802767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724402501/5000000000 : ℝ)|^65 ≤ (44688477297093/100000000000000 : ℝ)^49
        have hw : |(2724402501/5000000000 : ℝ)|=(2724402501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1124552391/2500000000 : ℝ)*x 0 + (-1328673691/10000000000 : ℝ)*x 1 + (6672976761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124552391/2500000000 : ℝ)^65 ≤ (34653453365277/100000000000000 : ℝ)^49 := by
    have hnat : (1124552391 : ℕ)^65*100000000000000^49 ≤ 34653453365277^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124552391 2500000000 34653453365277 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328673691/10000000000 : ℝ)^65 ≤ (1718413186971/25000000000000 : ℝ)^49 := by
    have hnat : (1328673691 : ℕ)^65*25000000000000^49 ≤ 1718413186971^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328673691 10000000000 1718413186971 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6672976761/10000000000 : ℝ)^65 ≤ (58472893860391/100000000000000 : ℝ)^49 := by
    have hnat : (6672976761 : ℕ)^65*100000000000000^49 ≤ 58472893860391^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6672976761 10000000000 58472893860391 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124552391/2500000000 : ℝ), (-1328673691/10000000000 : ℝ), (6672976761/10000000000 : ℝ)] ![(34653453365277/100000000000000 : ℝ), (1718413186971/25000000000000 : ℝ), (58472893860391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124552391/2500000000 : ℝ)|^65 ≤ (34653453365277/100000000000000 : ℝ)^49
        have hw : |(1124552391/2500000000 : ℝ)|=(1124552391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1328673691/10000000000 : ℝ)|^65 ≤ (1718413186971/25000000000000 : ℝ)^49
        have hw : |(-1328673691/10000000000 : ℝ)|=(1328673691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6672976761/10000000000 : ℝ)|^65 ≤ (58472893860391/100000000000000 : ℝ)^49
        have hw : |(6672976761/10000000000 : ℝ)|=(6672976761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4516684451/10000000000 : ℝ)*x 0 + (1331745231/2000000000 : ℝ)*x 1 + (-82829467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4516684451/10000000000 : ℝ)^65 ≤ (17421190776163/50000000000000 : ℝ)^49 := by
    have hnat : (4516684451 : ℕ)^65*50000000000000^49 ≤ 17421190776163^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516684451 10000000000 17421190776163 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331745231/2000000000 : ℝ)^65 ≤ (58307303876893/100000000000000 : ℝ)^49 := by
    have hnat : (1331745231 : ℕ)^65*100000000000000^49 ≤ 58307303876893^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331745231 2000000000 58307303876893 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82829467/625000000 : ℝ)^65 ≤ (6850314562173/100000000000000 : ℝ)^49 := by
    have hnat : (82829467 : ℕ)^65*100000000000000^49 ≤ 6850314562173^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82829467 625000000 6850314562173 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4516684451/10000000000 : ℝ), (1331745231/2000000000 : ℝ), (-82829467/625000000 : ℝ)] ![(17421190776163/50000000000000 : ℝ), (58307303876893/100000000000000 : ℝ), (6850314562173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4516684451/10000000000 : ℝ)|^65 ≤ (17421190776163/50000000000000 : ℝ)^49
        have hw : |(4516684451/10000000000 : ℝ)|=(4516684451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1331745231/2000000000 : ℝ)|^65 ≤ (58307303876893/100000000000000 : ℝ)^49
        have hw : |(1331745231/2000000000 : ℝ)|=(1331745231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82829467/625000000 : ℝ)|^65 ≤ (6850314562173/100000000000000 : ℝ)^49
        have hw : |(-82829467/625000000 : ℝ)|=(82829467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740403867/10000000000 : ℝ)*x 0 + (421675573/1000000000 : ℝ)*x 1 + (3331619353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740403867/10000000000 : ℝ)^65 ≤ (9833294181557/100000000000000 : ℝ)^49 := by
    have hnat : (1740403867 : ℕ)^65*100000000000000^49 ≤ 9833294181557^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740403867 10000000000 9833294181557 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421675573/1000000000 : ℝ)^65 ≤ (7951744809317/25000000000000 : ℝ)^49 := by
    have hnat : (421675573 : ℕ)^65*25000000000000^49 ≤ 7951744809317^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421675573 1000000000 7951744809317 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3331619353/5000000000 : ℝ)^65 ≤ (58359726560231/100000000000000 : ℝ)^49 := by
    have hnat : (3331619353 : ℕ)^65*100000000000000^49 ≤ 58359726560231^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331619353 5000000000 58359726560231 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740403867/10000000000 : ℝ), (421675573/1000000000 : ℝ), (3331619353/5000000000 : ℝ)] ![(9833294181557/100000000000000 : ℝ), (7951744809317/25000000000000 : ℝ), (58359726560231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740403867/10000000000 : ℝ)|^65 ≤ (9833294181557/100000000000000 : ℝ)^49
        have hw : |(-1740403867/10000000000 : ℝ)|=(1740403867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(421675573/1000000000 : ℝ)|^65 ≤ (7951744809317/25000000000000 : ℝ)^49
        have hw : |(421675573/1000000000 : ℝ)|=(421675573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3331619353/5000000000 : ℝ)|^65 ≤ (58359726560231/100000000000000 : ℝ)^49
        have hw : |(3331619353/5000000000 : ℝ)|=(3331619353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (882165857/2500000000 : ℝ)*x 0 + (-94859841/2500000000 : ℝ)*x 1 + (3967745737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882165857/2500000000 : ℝ)^65 ≤ (6278142059063/25000000000000 : ℝ)^49 := by
    have hnat : (882165857 : ℕ)^65*25000000000000^49 ≤ 6278142059063^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882165857 2500000000 6278142059063 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94859841/2500000000 : ℝ)^65 ≤ (1303733653939/100000000000000 : ℝ)^49 := by
    have hnat : (94859841 : ℕ)^65*100000000000000^49 ≤ 1303733653939^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94859841 2500000000 1303733653939 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3967745737/5000000000 : ℝ)^65 ≤ (73583698096929/100000000000000 : ℝ)^49 := by
    have hnat : (3967745737 : ℕ)^65*100000000000000^49 ≤ 73583698096929^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3967745737 5000000000 73583698096929 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(882165857/2500000000 : ℝ), (-94859841/2500000000 : ℝ), (3967745737/5000000000 : ℝ)] ![(6278142059063/25000000000000 : ℝ), (1303733653939/100000000000000 : ℝ), (73583698096929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(882165857/2500000000 : ℝ)|^65 ≤ (6278142059063/25000000000000 : ℝ)^49
        have hw : |(882165857/2500000000 : ℝ)|=(882165857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94859841/2500000000 : ℝ)|^65 ≤ (1303733653939/100000000000000 : ℝ)^49
        have hw : |(-94859841/2500000000 : ℝ)|=(94859841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3967745737/5000000000 : ℝ)|^65 ≤ (73583698096929/100000000000000 : ℝ)^49
        have hw : |(3967745737/5000000000 : ℝ)|=(3967745737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1773931783/5000000000 : ℝ)*x 0 + (7921678231/10000000000 : ℝ)*x 1 + (-376900617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1773931783/5000000000 : ℝ)^65 ≤ (25293989291297/100000000000000 : ℝ)^49 := by
    have hnat : (1773931783 : ℕ)^65*100000000000000^49 ≤ 25293989291297^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773931783 5000000000 25293989291297 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7921678231/10000000000 : ℝ)^65 ≤ (18353458927789/25000000000000 : ℝ)^49 := by
    have hnat : (7921678231 : ℕ)^65*25000000000000^49 ≤ 18353458927789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7921678231 10000000000 18353458927789 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376900617/10000000000 : ℝ)^65 ≤ (646087492749/50000000000000 : ℝ)^49 := by
    have hnat : (376900617 : ℕ)^65*50000000000000^49 ≤ 646087492749^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376900617 10000000000 646087492749 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1773931783/5000000000 : ℝ), (7921678231/10000000000 : ℝ), (-376900617/10000000000 : ℝ)] ![(25293989291297/100000000000000 : ℝ), (18353458927789/25000000000000 : ℝ), (646087492749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1773931783/5000000000 : ℝ)|^65 ≤ (25293989291297/100000000000000 : ℝ)^49
        have hw : |(1773931783/5000000000 : ℝ)|=(1773931783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7921678231/10000000000 : ℝ)|^65 ≤ (18353458927789/25000000000000 : ℝ)^49
        have hw : |(7921678231/10000000000 : ℝ)|=(7921678231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-376900617/10000000000 : ℝ)|^65 ≤ (646087492749/50000000000000 : ℝ)^49
        have hw : |(-376900617/10000000000 : ℝ)|=(376900617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6517886241/10000000000 : ℝ)*x 0 + (5143517143/10000000000 : ℝ)*x 1 + (509035217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6517886241/10000000000 : ℝ)^65 ≤ (28338506122967/50000000000000 : ℝ)^49 := by
    have hnat : (6517886241 : ℕ)^65*50000000000000^49 ≤ 28338506122967^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6517886241 10000000000 28338506122967 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143517143/10000000000 : ℝ)^65 ≤ (10349462944489/25000000000000 : ℝ)^49 := by
    have hnat : (5143517143 : ℕ)^65*25000000000000^49 ≤ 10349462944489^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143517143 10000000000 10349462944489 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509035217/10000000000 : ℝ)^65 ≤ (1925135960687/100000000000000 : ℝ)^49 := by
    have hnat : (509035217 : ℕ)^65*100000000000000^49 ≤ 1925135960687^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509035217 10000000000 1925135960687 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6517886241/10000000000 : ℝ), (5143517143/10000000000 : ℝ), (509035217/10000000000 : ℝ)] ![(28338506122967/50000000000000 : ℝ), (10349462944489/25000000000000 : ℝ), (1925135960687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6517886241/10000000000 : ℝ)|^65 ≤ (28338506122967/50000000000000 : ℝ)^49
        have hw : |(6517886241/10000000000 : ℝ)|=(6517886241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143517143/10000000000 : ℝ)|^65 ≤ (10349462944489/25000000000000 : ℝ)^49
        have hw : |(5143517143/10000000000 : ℝ)|=(5143517143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(509035217/10000000000 : ℝ)|^65 ≤ (1925135960687/100000000000000 : ℝ)^49
        have hw : |(509035217/10000000000 : ℝ)|=(509035217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1375053367/10000000000 : ℝ)*x 0 + (986885583/2500000000 : ℝ)*x 1 + (1778725811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375053367/10000000000 : ℝ)^65 ≤ (449608514919/6250000000000 : ℝ)^49 := by
    have hnat : (1375053367 : ℕ)^65*6250000000000^49 ≤ 449608514919^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375053367 10000000000 449608514919 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986885583/2500000000 : ℝ)^65 ≤ (29141717072027/100000000000000 : ℝ)^49 := by
    have hnat : (986885583 : ℕ)^65*100000000000000^49 ≤ 29141717072027^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986885583 2500000000 29141717072027 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1778725811/2500000000 : ℝ)^65 ≤ (63664546675439/100000000000000 : ℝ)^49 := by
    have hnat : (1778725811 : ℕ)^65*100000000000000^49 ≤ 63664546675439^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778725811 2500000000 63664546675439 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1375053367/10000000000 : ℝ), (986885583/2500000000 : ℝ), (1778725811/2500000000 : ℝ)] ![(449608514919/6250000000000 : ℝ), (29141717072027/100000000000000 : ℝ), (63664546675439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1375053367/10000000000 : ℝ)|^65 ≤ (449608514919/6250000000000 : ℝ)^49
        have hw : |(-1375053367/10000000000 : ℝ)|=(1375053367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(986885583/2500000000 : ℝ)|^65 ≤ (29141717072027/100000000000000 : ℝ)^49
        have hw : |(986885583/2500000000 : ℝ)|=(986885583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1778725811/2500000000 : ℝ)|^65 ≤ (63664546675439/100000000000000 : ℝ)^49
        have hw : |(1778725811/2500000000 : ℝ)|=(1778725811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2335161319/10000000000 : ℝ)*x 0 + (-7807541/80000000 : ℝ)*x 1 + (8524253811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2335161319/10000000000 : ℝ)^65 ≤ (181536111183/1250000000000 : ℝ)^49 := by
    have hnat : (2335161319 : ℕ)^65*1250000000000^49 ≤ 181536111183^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335161319 10000000000 181536111183 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7807541/80000000 : ℝ)^65 ≤ (570624472117/12500000000000 : ℝ)^49 := by
    have hnat : (7807541 : ℕ)^65*12500000000000^49 ≤ 570624472117^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7807541 80000000 570624472117 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8524253811/10000000000 : ℝ)^65 ≤ (80912115317313/100000000000000 : ℝ)^49 := by
    have hnat : (8524253811 : ℕ)^65*100000000000000^49 ≤ 80912115317313^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8524253811 10000000000 80912115317313 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2335161319/10000000000 : ℝ), (-7807541/80000000 : ℝ), (8524253811/10000000000 : ℝ)] ![(181536111183/1250000000000 : ℝ), (570624472117/12500000000000 : ℝ), (80912115317313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2335161319/10000000000 : ℝ)|^65 ≤ (181536111183/1250000000000 : ℝ)^49
        have hw : |(2335161319/10000000000 : ℝ)|=(2335161319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7807541/80000000 : ℝ)|^65 ≤ (570624472117/12500000000000 : ℝ)^49
        have hw : |(-7807541/80000000 : ℝ)|=(7807541/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8524253811/10000000000 : ℝ)|^65 ≤ (80912115317313/100000000000000 : ℝ)^49
        have hw : |(8524253811/10000000000 : ℝ)|=(8524253811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6129273407/10000000000 : ℝ)*x 0 + (5469436969/10000000000 : ℝ)*x 1 + (-10686057/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6129273407/10000000000 : ℝ)^65 ≤ (52238599242489/100000000000000 : ℝ)^49 := by
    have hnat : (6129273407 : ℕ)^65*100000000000000^49 ≤ 52238599242489^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6129273407 10000000000 52238599242489 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469436969/10000000000 : ℝ)^65 ≤ (44913082790919/100000000000000 : ℝ)^49 := by
    have hnat : (5469436969 : ℕ)^65*100000000000000^49 ≤ 44913082790919^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469436969 10000000000 44913082790919 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10686057/156250000 : ℝ)^65 ≤ (1424158978527/50000000000000 : ℝ)^49 := by
    have hnat : (10686057 : ℕ)^65*50000000000000^49 ≤ 1424158978527^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10686057 156250000 1424158978527 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6129273407/10000000000 : ℝ), (5469436969/10000000000 : ℝ), (-10686057/156250000 : ℝ)] ![(52238599242489/100000000000000 : ℝ), (44913082790919/100000000000000 : ℝ), (1424158978527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6129273407/10000000000 : ℝ)|^65 ≤ (52238599242489/100000000000000 : ℝ)^49
        have hw : |(6129273407/10000000000 : ℝ)|=(6129273407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469436969/10000000000 : ℝ)|^65 ≤ (44913082790919/100000000000000 : ℝ)^49
        have hw : |(5469436969/10000000000 : ℝ)|=(5469436969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10686057/156250000 : ℝ)|^65 ≤ (1424158978527/50000000000000 : ℝ)^49
        have hw : |(-10686057/156250000 : ℝ)|=(10686057/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9245490539/10000000000 : ℝ)*x 0 + (326256947/2500000000 : ℝ)*x 1 + (741623569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9245490539/10000000000 : ℝ)^65 ≤ (90116651689079/100000000000000 : ℝ)^49 := by
    have hnat : (9245490539 : ℕ)^65*100000000000000^49 ≤ 90116651689079^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9245490539 10000000000 90116651689079 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326256947/2500000000 : ℝ)^65 ≤ (6711854569243/100000000000000 : ℝ)^49 := by
    have hnat : (326256947 : ℕ)^65*100000000000000^49 ≤ 6711854569243^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326256947 2500000000 6711854569243 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741623569/10000000000 : ℝ)^65 ≤ (1585746866349/50000000000000 : ℝ)^49 := by
    have hnat : (741623569 : ℕ)^65*50000000000000^49 ≤ 1585746866349^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741623569 10000000000 1585746866349 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9245490539/10000000000 : ℝ), (326256947/2500000000 : ℝ), (741623569/10000000000 : ℝ)] ![(90116651689079/100000000000000 : ℝ), (6711854569243/100000000000000 : ℝ), (1585746866349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9245490539/10000000000 : ℝ)|^65 ≤ (90116651689079/100000000000000 : ℝ)^49
        have hw : |(9245490539/10000000000 : ℝ)|=(9245490539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326256947/2500000000 : ℝ)|^65 ≤ (6711854569243/100000000000000 : ℝ)^49
        have hw : |(326256947/2500000000 : ℝ)|=(326256947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(741623569/10000000000 : ℝ)|^65 ≤ (1585746866349/50000000000000 : ℝ)^49
        have hw : |(741623569/10000000000 : ℝ)|=(741623569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-137522273/1000000000 : ℝ)*x 0 + (3430356353/5000000000 : ℝ)*x 1 + (2124997923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137522273/1000000000 : ℝ)^65 ≤ (7194911621971/100000000000000 : ℝ)^49 := by
    have hnat : (137522273 : ℕ)^65*100000000000000^49 ≤ 7194911621971^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137522273 1000000000 7194911621971 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3430356353/5000000000 : ℝ)^65 ≤ (12133016126127/20000000000000 : ℝ)^49 := by
    have hnat : (3430356353 : ℕ)^65*20000000000000^49 ≤ 12133016126127^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3430356353 5000000000 12133016126127 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124997923/5000000000 : ℝ)^65 ≤ (16070003860969/50000000000000 : ℝ)^49 := by
    have hnat : (2124997923 : ℕ)^65*50000000000000^49 ≤ 16070003860969^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124997923 5000000000 16070003860969 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137522273/1000000000 : ℝ), (3430356353/5000000000 : ℝ), (2124997923/5000000000 : ℝ)] ![(7194911621971/100000000000000 : ℝ), (12133016126127/20000000000000 : ℝ), (16070003860969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137522273/1000000000 : ℝ)|^65 ≤ (7194911621971/100000000000000 : ℝ)^49
        have hw : |(-137522273/1000000000 : ℝ)|=(137522273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3430356353/5000000000 : ℝ)|^65 ≤ (12133016126127/20000000000000 : ℝ)^49
        have hw : |(3430356353/5000000000 : ℝ)|=(3430356353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124997923/5000000000 : ℝ)|^65 ≤ (16070003860969/50000000000000 : ℝ)^49
        have hw : |(2124997923/5000000000 : ℝ)|=(2124997923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6094362077/10000000000 : ℝ)*x 0 + (-82504597/1250000000 : ℝ)*x 1 + (5517605559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6094362077/10000000000 : ℝ)^65 ≤ (81006668123/156250000000 : ℝ)^49 := by
    have hnat : (6094362077 : ℕ)^65*156250000000^49 ≤ 81006668123^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6094362077 10000000000 81006668123 156250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82504597/1250000000 : ℝ)^65 ≤ (2717196174339/100000000000000 : ℝ)^49 := by
    have hnat : (82504597 : ℕ)^65*100000000000000^49 ≤ 2717196174339^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82504597 1250000000 2717196174339 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517605559/10000000000 : ℝ)^65 ≤ (22719268109719/50000000000000 : ℝ)^49 := by
    have hnat : (5517605559 : ℕ)^65*50000000000000^49 ≤ 22719268109719^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517605559 10000000000 22719268109719 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6094362077/10000000000 : ℝ), (-82504597/1250000000 : ℝ), (5517605559/10000000000 : ℝ)] ![(81006668123/156250000000 : ℝ), (2717196174339/100000000000000 : ℝ), (22719268109719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6094362077/10000000000 : ℝ)|^65 ≤ (81006668123/156250000000 : ℝ)^49
        have hw : |(6094362077/10000000000 : ℝ)|=(6094362077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82504597/1250000000 : ℝ)|^65 ≤ (2717196174339/100000000000000 : ℝ)^49
        have hw : |(-82504597/1250000000 : ℝ)|=(82504597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517605559/10000000000 : ℝ)|^65 ≤ (22719268109719/50000000000000 : ℝ)^49
        have hw : |(5517605559/10000000000 : ℝ)|=(5517605559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2355321443/10000000000 : ℝ)*x 0 + (8519072643/10000000000 : ℝ)*x 1 + (-38382721/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2355321443/10000000000 : ℝ)^65 ≤ (14689443688091/100000000000000 : ℝ)^49 := by
    have hnat : (2355321443 : ℕ)^65*100000000000000^49 ≤ 14689443688091^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355321443 10000000000 14689443688091 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8519072643/10000000000 : ℝ)^65 ≤ (40423441783727/50000000000000 : ℝ)^49 := by
    have hnat : (8519072643 : ℕ)^65*50000000000000^49 ≤ 40423441783727^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8519072643 10000000000 40423441783727 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38382721/400000000 : ℝ)^65 ≤ (278979545531/6250000000000 : ℝ)^49 := by
    have hnat : (38382721 : ℕ)^65*6250000000000^49 ≤ 278979545531^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38382721 400000000 278979545531 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2355321443/10000000000 : ℝ), (8519072643/10000000000 : ℝ), (-38382721/400000000 : ℝ)] ![(14689443688091/100000000000000 : ℝ), (40423441783727/50000000000000 : ℝ), (278979545531/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2355321443/10000000000 : ℝ)|^65 ≤ (14689443688091/100000000000000 : ℝ)^49
        have hw : |(2355321443/10000000000 : ℝ)|=(2355321443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8519072643/10000000000 : ℝ)|^65 ≤ (40423441783727/50000000000000 : ℝ)^49
        have hw : |(8519072643/10000000000 : ℝ)|=(8519072643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38382721/400000000 : ℝ)|^65 ≤ (278979545531/6250000000000 : ℝ)^49
        have hw : |(-38382721/400000000 : ℝ)|=(38382721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s5_s5_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9277015341/10000000000 : ℝ)*x 0 + (1079306857/10000000000 : ℝ)*x 1 + (926096449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9277015341/10000000000 : ℝ)^65 ≤ (90524488338033/100000000000000 : ℝ)^49 := by
    have hnat : (9277015341 : ℕ)^65*100000000000000^49 ≤ 90524488338033^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9277015341 10000000000 90524488338033 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079306857/10000000000 : ℝ)^65 ≤ (652149511473/12500000000000 : ℝ)^49 := by
    have hnat : (1079306857 : ℕ)^65*12500000000000^49 ≤ 652149511473^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079306857 10000000000 652149511473 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926096449/10000000000 : ℝ)^65 ≤ (2129157780193/50000000000000 : ℝ)^49 := by
    have hnat : (926096449 : ℕ)^65*50000000000000^49 ≤ 2129157780193^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926096449 10000000000 2129157780193 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9277015341/10000000000 : ℝ), (1079306857/10000000000 : ℝ), (926096449/10000000000 : ℝ)] ![(90524488338033/100000000000000 : ℝ), (652149511473/12500000000000 : ℝ), (2129157780193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9277015341/10000000000 : ℝ)|^65 ≤ (90524488338033/100000000000000 : ℝ)^49
        have hw : |(9277015341/10000000000 : ℝ)|=(9277015341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079306857/10000000000 : ℝ)|^65 ≤ (652149511473/12500000000000 : ℝ)^49
        have hw : |(1079306857/10000000000 : ℝ)|=(1079306857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926096449/10000000000 : ℝ)|^65 ≤ (2129157780193/50000000000000 : ℝ)^49
        have hw : |(926096449/10000000000 : ℝ)|=(926096449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301053_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((37181/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37181/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40477/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40477/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80247/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80247/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((51/80 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51/80 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36449/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36449/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72187/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (37181/50000 : ℝ) ^ (129/32 : ℝ) ≤ (15147953812254727977/50000000000000000000 : ℝ) := by
    have hpowers : (37181/50000 : ℝ)^129 ≤ (15147953812254727977/50000000000000000000 : ℝ)^32 := by
      have hnat : (37181 : ℕ)^129*50000000000000000000^32 ≤ 15147953812254727977^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37181 50000 15147953812254727977 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37181/50000 : ℝ)) (X := (15147953812254727977/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (65147953812254727977/50000000000000000000 : ℝ) ≤ (2669623203916269/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (65147953812254727977/50000000000000000000 : ℝ)^32 ≤ (2669623203916269/2500000000000000 : ℝ)^129 := by
      have hnat : (65147953812254727977 : ℕ)^32*2500000000000000^129 ≤ 2669623203916269^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65147953812254727977 50000000000000000000 2669623203916269 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2669623203916269/2500000000000000 : ℝ)) (X := (65147953812254727977/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (40147953812254727977/25000000000000000000 : ℝ) ≤ (2249376526299019/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (40147953812254727977/25000000000000000000 : ℝ)^32 ≤ (2249376526299019/2000000000000000 : ℝ)^129 := by
      have hnat : (40147953812254727977 : ℕ)^32*2000000000000000^129 ≤ 2249376526299019^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40147953812254727977 25000000000000000000 2249376526299019 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2249376526299019/2000000000000000 : ℝ)) (X := (40147953812254727977/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(169623203916269/1859050000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(568389815830019/7436200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (37181/50000 : ℝ)) (alpha := (169623203916269/1859050000000000 : ℝ)) (beta := (568389815830019/7436200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37181/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(169623203916269/1859050000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(568389815830019/7436200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (40477/50000 : ℝ) ^ (129/32 : ℝ) ≤ (42666370180631911261/100000000000000000000 : ℝ) := by
    have hpowers : (40477/50000 : ℝ)^129 ≤ (42666370180631911261/100000000000000000000 : ℝ)^32 := by
      have hnat : (40477 : ℕ)^129*100000000000000000000^32 ≤ 42666370180631911261^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40477 50000 42666370180631911261 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40477/50000 : ℝ)) (X := (42666370180631911261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (142666370180631911261/100000000000000000000 : ℝ) ≤ (10921475856744259/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (142666370180631911261/100000000000000000000 : ℝ)^32 ≤ (10921475856744259/10000000000000000 : ℝ)^129 := by
      have hnat : (142666370180631911261 : ℕ)^32*10000000000000000^129 ≤ 10921475856744259^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        142666370180631911261 100000000000000000000 10921475856744259 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10921475856744259/10000000000000000 : ℝ)) (X := (142666370180631911261/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (92666370180631911261/50000000000000000000 : ℝ) ≤ (1456728988784843/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (92666370180631911261/50000000000000000000 : ℝ)^32 ≤ (1456728988784843/1250000000000000 : ℝ)^129 := by
      have hnat : (92666370180631911261 : ℕ)^32*1250000000000000^129 ≤ 1456728988784843^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92666370180631911261 50000000000000000000 1456728988784843 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1456728988784843/1250000000000000 : ℝ)) (X := (92666370180631911261/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(54204462161427/476200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(146471210706897/1619080000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (40477/50000 : ℝ)) (alpha := (54204462161427/476200000000000 : ℝ)) (beta := (146471210706897/1619080000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (40477/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(54204462161427/476200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(146471210706897/1619080000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (80247/100000 : ℝ) ^ (129/32 : ℝ) ≤ (41184009180396877083/100000000000000000000 : ℝ) := by
    have hpowers : (80247/100000 : ℝ)^129 ≤ (41184009180396877083/100000000000000000000 : ℝ)^32 := by
      have hnat : (80247 : ℕ)^129*100000000000000000000^32 ≤ 41184009180396877083^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80247 100000 41184009180396877083 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80247/100000 : ℝ)) (X := (41184009180396877083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (141184009180396877083/100000000000000000000 : ℝ) ≤ (10893215505998101/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (141184009180396877083/100000000000000000000 : ℝ)^32 ≤ (10893215505998101/10000000000000000 : ℝ)^129 := by
      have hnat : (141184009180396877083 : ℕ)^32*10000000000000000^129 ≤ 10893215505998101^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141184009180396877083 100000000000000000000 10893215505998101 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10893215505998101/10000000000000000 : ℝ)) (X := (141184009180396877083/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (91184009180396877083/50000000000000000000 : ℝ) ≤ (11607306574376723/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (91184009180396877083/50000000000000000000 : ℝ)^32 ≤ (11607306574376723/10000000000000000 : ℝ)^129 := by
      have hnat : (91184009180396877083 : ℕ)^32*10000000000000000^129 ≤ 11607306574376723^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91184009180396877083 50000000000000000000 11607306574376723 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11607306574376723/10000000000000000 : ℝ)) (X := (91184009180396877083/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(297738501999367/2674900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(357045534189311/4012350000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (80247/100000 : ℝ)) (alpha := (297738501999367/2674900000000000 : ℝ)) (beta := (357045534189311/4012350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (80247/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(297738501999367/2674900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(357045534189311/4012350000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-400322361/2000000000 : ℝ)*X 0 0+(5336802767/10000000000 : ℝ)*X 0 1+(2724402501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((1124552391/2500000000 : ℝ)*X 1 0+(-1328673691/10000000000 : ℝ)*X 1 1+(6672976761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((4516684451/10000000000 : ℝ)*X 2 0+(1331745231/2000000000 : ℝ)*X 2 1+(-82829467/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-1740403867/10000000000 : ℝ)*X 0 0+(421675573/1000000000 : ℝ)*X 0 1+(3331619353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((882165857/2500000000 : ℝ)*X 1 0+(-94859841/2500000000 : ℝ)*X 1 1+(3967745737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((1773931783/5000000000 : ℝ)*X 2 0+(7921678231/10000000000 : ℝ)*X 2 1+(-376900617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((6517886241/10000000000 : ℝ)*X 0 0+(5143517143/10000000000 : ℝ)*X 0 1+(509035217/10000000000 : ℝ)*X 0 2+(6517886241/10000000000 : ℝ)*X 1 0+(5143517143/10000000000 : ℝ)*X 1 1+(509035217/10000000000 : ℝ)*X 1 2+(6517886241/10000000000 : ℝ)*X 2 0+(5143517143/10000000000 : ℝ)*X 2 1+(509035217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1375053367/10000000000 : ℝ)*X 0 0+(986885583/2500000000 : ℝ)*X 0 1+(1778725811/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((2335161319/10000000000 : ℝ)*X 1 0+(-7807541/80000000 : ℝ)*X 1 1+(8524253811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((6129273407/10000000000 : ℝ)*X 2 0+(5469436969/10000000000 : ℝ)*X 2 1+(-10686057/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((9245490539/10000000000 : ℝ)*X 0 0+(326256947/2500000000 : ℝ)*X 0 1+(741623569/10000000000 : ℝ)*X 0 2+(9245490539/10000000000 : ℝ)*X 1 0+(326256947/2500000000 : ℝ)*X 1 1+(741623569/10000000000 : ℝ)*X 1 2+(9245490539/10000000000 : ℝ)*X 2 0+(326256947/2500000000 : ℝ)*X 2 1+(741623569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-137522273/1000000000 : ℝ)*X 0 0+(3430356353/5000000000 : ℝ)*X 0 1+(2124997923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((6094362077/10000000000 : ℝ)*X 1 0+(-82504597/1250000000 : ℝ)*X 1 1+(5517605559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((2355321443/10000000000 : ℝ)*X 2 0+(8519072643/10000000000 : ℝ)*X 2 1+(-38382721/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((9277015341/10000000000 : ℝ)*X 0 0+(1079306857/10000000000 : ℝ)*X 0 1+(926096449/10000000000 : ℝ)*X 0 2+(9277015341/10000000000 : ℝ)*X 1 0+(1079306857/10000000000 : ℝ)*X 1 1+(926096449/10000000000 : ℝ)*X 1 2+(9277015341/10000000000 : ℝ)*X 2 0+(1079306857/10000000000 : ℝ)*X 2 1+(926096449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((51/80 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51/80 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57354456824580045379926645130843/4025658528941300000000000000000000000 : ℝ) := by norm_num
    linear_combination (64346763261/1000000000000 : ℝ)*(base7) + (14813/31250000000 : ℝ)*(base49) + (55381/100000000000 : ℝ)*(base59) + (3270083959583/1000000000000 : ℝ)*(major_s5_0) + (3270083959583/1000000000000 : ℝ)*(major_s5_1) + (3270083959583/1000000000000 : ℝ)*(major_s5_2) + (16887531/200000000000 : ℝ)*(sp_s5_0) + (4317/31250000000 : ℝ)*(sp_s5_1) + (4289577959429/1000000000000 : ℝ)*(sp_s5_7) + (2144938356851/500000000000 : ℝ)*(sp_s5_8) + (2144939018229/500000000000 : ℝ)*(sp_s5_9) + (227499815153/100000000000 : ℝ)*(sp_s5_13) + (107819687/500000000000 : ℝ)*(sp_s5_14) + (296153/250000000000 : ℝ)*(sp_s5_15) + (2210651388269/1000000000000 : ℝ)*(f.failure) + (2144939018229/500000000000 : ℝ)*(f.sum) + (42580850329534571/12737873800000000000000000000000 : ℝ)*base63 + (161898412882717/1003087500000000000000000000 : ℝ)*base64 + (477797970637449/1619080000000000000000000000 : ℝ)*base67 + (404864502224739/2674900000000000000000000000 : ℝ)*base68 + (4124488429402171207/74591592675000000000000000000000 : ℝ)*base70 + (1282530429397803/7436200000000000000000000000 : ℝ)*base72 + (76145096955019/476200000000000000000000000 : ℝ)*base74 + (75484446876313/1859050000000000000000000000 : ℝ)*base76 + (66565114360661931157/150497533700000000000000000000000 : ℝ)*base79 + (889/25000000000000000 : ℝ)*base87 + (889/25000000000000000 : ℝ)*base89 + (889/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36449/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36449/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3307707020828878984647/267490000000000000000000000 : ℝ) := by norm_num
    linear_combination (63471097277/125000000000 : ℝ)*(base7) + (640279/250000000000 : ℝ)*(base53) + (2238193207701/1000000000000 : ℝ)*(major_s5_0) + (2238193207701/1000000000000 : ℝ)*(major_s5_1) + (447638129317/200000000000 : ℝ)*(major_s5_2) + (25197883/1000000000000 : ℝ)*(sp_s5_0) + (1427333/62500000000 : ℝ)*(sp_s5_2) + (42777301/1000000000000 : ℝ)*(sp_s5_7) + (21471279/250000000000 : ℝ)*(sp_s5_8) + (2650486966293/1000000000000 : ℝ)*(sp_s5_14) + (2650469056361/1000000000000 : ℝ)*(sp_s5_15) + (165658416579/62500000000 : ℝ)*(sp_s5_16) + (1010345627809/500000000000 : ℝ)*(sp_s5_20) + (147212237/1000000000000 : ℝ)*(sp_s5_27) + (756534844819/500000000000 : ℝ)*(f.failure) + (2650557502593/1000000000000 : ℝ)*(f.sum) + (9370407844635412767/12737873800000000000000000000000 : ℝ)*base62 + (255710863272493/802470000000000000000000000 : ℝ)*base65 + (104276265711551/1619080000000000000000000000 : ℝ)*base67 + (197532744471209/534980000000000000000000000 : ℝ)*base68 + (768917486577595577/9323949084375000000000000000000 : ℝ)*base70 + (1295162398064119/7436200000000000000000000000 : ℝ)*base73 + (50316603361427/476200000000000000000000000 : ℝ)*base75 + (377246163211181/464762500000000000000000000 : ℝ)*base77 + (24630138588732316351/150497533700000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (11061/12500000000000000 : ℝ)*base86 + (11061/12500000000000000 : ℝ)*base88 + (11061/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72187/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (806878327999205701505999929/99455456900000000000000000000000 : ℝ) := by norm_num
    linear_combination (500773957803/1000000000000 : ℝ)*(base7) + (210741/200000000000 : ℝ)*(base27) + (65301/100000000000 : ℝ)*(base34) + (37018342649/1000000000000 : ℝ)*(base40) + (2241623429127/1000000000000 : ℝ)*(major_s5_0) + (280203010267/125000000000 : ℝ)*(major_s5_1) + (280203010267/125000000000 : ℝ)*(major_s5_2) + (430299/200000000000 : ℝ)*(sp_s5_0) + (17585863/1000000000000 : ℝ)*(sp_s5_1) + (63203259/1000000000000 : ℝ)*(sp_s5_9) + (1329703452407/500000000000 : ℝ)*(sp_s5_21) + (531878424691/200000000000 : ℝ)*(sp_s5_22) + (2659346506059/1000000000000 : ℝ)*(sp_s5_23) + (2016161290147/1000000000000 : ℝ)*(sp_s5_27) + (757694519529/500000000000 : ℝ)*(f.failure) + (1329704854659/500000000000 : ℝ)*(f.sum) + (153861551526579161/1592234225000000000000000000000 : ℝ)*base62 + (184525403717297/501543750000000000000000000 : ℝ)*base64 + (147973264142847/404770000000000000000000000 : ℝ)*base66 + (223459231352963/668725000000000000000000000 : ℝ)*base69 + (511863218719988521/1193465482800000000000000000000 : ℝ)*base70 + (3352211027413993/7436200000000000000000000000 : ℝ)*base73 + (1163953133829/3720312500000000000000000 : ℝ)*base75 + (426459975656031/929525000000000000000000000 : ℝ)*base76 + (163286347555252488741/300995067400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (10551/12500000000000000 : ℝ)*base86 + (1949/12500000000000000 : ℝ)*base89 + (1949/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((37181/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37181/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40477/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40477/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80247/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80247/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((51/80 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51/80 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36449/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36449/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72187/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301053_s5 p hpa hpb X hX hprev4

#print axioms solution

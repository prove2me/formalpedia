-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301082_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:42:43.088554+00:00
-- url     : https://prove2.me/submissions/0f5c2c8b-129e-4040-b7b5-40701a6fcaa1

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
theorem collision_support_c301082_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3798393279/10000000000 : ℝ)*x 0 + (804545721/2500000000 : ℝ)*x 1 + (1187566907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3798393279/10000000000 : ℝ)^65 ≤ (5538044381823/20000000000000 : ℝ)^49 := by
    have hnat : (3798393279 : ℕ)^65*20000000000000^49 ≤ 5538044381823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3798393279 10000000000 5538044381823 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804545721/2500000000 : ℝ)^65 ≤ (2778053216701/12500000000000 : ℝ)^49 := by
    have hnat : (804545721 : ℕ)^65*12500000000000^49 ≤ 2778053216701^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804545721 2500000000 2778053216701 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187566907/2000000000 : ℝ)^65 ≤ (50085352344981/100000000000000 : ℝ)^49 := by
    have hnat : (1187566907 : ℕ)^65*100000000000000^49 ≤ 50085352344981^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187566907 2000000000 50085352344981 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3798393279/10000000000 : ℝ), (804545721/2500000000 : ℝ), (1187566907/2000000000 : ℝ)] ![(5538044381823/20000000000000 : ℝ), (2778053216701/12500000000000 : ℝ), (50085352344981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3798393279/10000000000 : ℝ)|^65 ≤ (5538044381823/20000000000000 : ℝ)^49
        have hw : |(-3798393279/10000000000 : ℝ)|=(3798393279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804545721/2500000000 : ℝ)|^65 ≤ (2778053216701/12500000000000 : ℝ)^49
        have hw : |(804545721/2500000000 : ℝ)|=(804545721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1187566907/2000000000 : ℝ)|^65 ≤ (50085352344981/100000000000000 : ℝ)^49
        have hw : |(1187566907/2000000000 : ℝ)|=(1187566907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4460482357/10000000000 : ℝ)*x 0 + (-3173685101/10000000000 : ℝ)*x 1 + (5377452339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460482357/10000000000 : ℝ)^65 ≤ (6853686805781/20000000000000 : ℝ)^49 := by
    have hnat : (4460482357 : ℕ)^65*20000000000000^49 ≤ 6853686805781^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460482357 10000000000 6853686805781 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3173685101/10000000000 : ℝ)^65 ≤ (1090885503633/5000000000000 : ℝ)^49 := by
    have hnat : (3173685101 : ℕ)^65*5000000000000^49 ≤ 1090885503633^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173685101 10000000000 1090885503633 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377452339/10000000000 : ℝ)^65 ≤ (8782771176779/20000000000000 : ℝ)^49 := by
    have hnat : (5377452339 : ℕ)^65*20000000000000^49 ≤ 8782771176779^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377452339 10000000000 8782771176779 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460482357/10000000000 : ℝ), (-3173685101/10000000000 : ℝ), (5377452339/10000000000 : ℝ)] ![(6853686805781/20000000000000 : ℝ), (1090885503633/5000000000000 : ℝ), (8782771176779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460482357/10000000000 : ℝ)|^65 ≤ (6853686805781/20000000000000 : ℝ)^49
        have hw : |(4460482357/10000000000 : ℝ)|=(4460482357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3173685101/10000000000 : ℝ)|^65 ≤ (1090885503633/5000000000000 : ℝ)^49
        have hw : |(-3173685101/10000000000 : ℝ)|=(3173685101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377452339/10000000000 : ℝ)|^65 ≤ (8782771176779/20000000000000 : ℝ)^49
        have hw : |(5377452339/10000000000 : ℝ)|=(5377452339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1599927823/2500000000 : ℝ)*x 0 + (5183079743/10000000000 : ℝ)*x 1 + (-137251463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1599927823/2500000000 : ℝ)^65 ≤ (55317916341191/100000000000000 : ℝ)^49 := by
    have hnat : (1599927823 : ℕ)^65*100000000000000^49 ≤ 55317916341191^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599927823 2500000000 55317916341191 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183079743/10000000000 : ℝ)^65 ≤ (20910388614039/50000000000000 : ℝ)^49 := by
    have hnat : (5183079743 : ℕ)^65*50000000000000^49 ≤ 20910388614039^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183079743 10000000000 20910388614039 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137251463/2000000000 : ℝ)^65 ≤ (2861306425727/100000000000000 : ℝ)^49 := by
    have hnat : (137251463 : ℕ)^65*100000000000000^49 ≤ 2861306425727^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137251463 2000000000 2861306425727 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1599927823/2500000000 : ℝ), (5183079743/10000000000 : ℝ), (-137251463/2000000000 : ℝ)] ![(55317916341191/100000000000000 : ℝ), (20910388614039/50000000000000 : ℝ), (2861306425727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1599927823/2500000000 : ℝ)|^65 ≤ (55317916341191/100000000000000 : ℝ)^49
        have hw : |(1599927823/2500000000 : ℝ)|=(1599927823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183079743/10000000000 : ℝ)|^65 ≤ (20910388614039/50000000000000 : ℝ)^49
        have hw : |(5183079743/10000000000 : ℝ)|=(5183079743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137251463/2000000000 : ℝ)|^65 ≤ (2861306425727/100000000000000 : ℝ)^49
        have hw : |(-137251463/2000000000 : ℝ)|=(137251463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1417347371/5000000000 : ℝ)*x 0 + (2085564953/10000000000 : ℝ)*x 1 + (7536599239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1417347371/5000000000 : ℝ)^65 ≤ (18781611137377/100000000000000 : ℝ)^49 := by
    have hnat : (1417347371 : ℕ)^65*100000000000000^49 ≤ 18781611137377^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417347371 5000000000 18781611137377 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085564953/10000000000 : ℝ)^65 ≤ (156256984043/1250000000000 : ℝ)^49 := by
    have hnat : (2085564953 : ℕ)^65*1250000000000^49 ≤ 156256984043^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085564953 10000000000 156256984043 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7536599239/10000000000 : ℝ)^65 ≤ (34358915065361/50000000000000 : ℝ)^49 := by
    have hnat : (7536599239 : ℕ)^65*50000000000000^49 ≤ 34358915065361^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7536599239 10000000000 34358915065361 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1417347371/5000000000 : ℝ), (2085564953/10000000000 : ℝ), (7536599239/10000000000 : ℝ)] ![(18781611137377/100000000000000 : ℝ), (156256984043/1250000000000 : ℝ), (34358915065361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1417347371/5000000000 : ℝ)|^65 ≤ (18781611137377/100000000000000 : ℝ)^49
        have hw : |(-1417347371/5000000000 : ℝ)|=(1417347371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085564953/10000000000 : ℝ)|^65 ≤ (156256984043/1250000000000 : ℝ)^49
        have hw : |(2085564953/10000000000 : ℝ)|=(2085564953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7536599239/10000000000 : ℝ)|^65 ≤ (34358915065361/50000000000000 : ℝ)^49
        have hw : |(7536599239/10000000000 : ℝ)|=(7536599239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (999946917/2500000000 : ℝ)*x 0 + (-31419557/250000000 : ℝ)*x 1 + (7139851479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999946917/2500000000 : ℝ)^65 ≤ (3706805745311/12500000000000 : ℝ)^49 := by
    have hnat : (999946917 : ℕ)^65*12500000000000^49 ≤ 3706805745311^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999946917 2500000000 3706805745311 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31419557/250000000 : ℝ)^65 ≤ (3192352831779/50000000000000 : ℝ)^49 := by
    have hnat : (31419557 : ℕ)^65*50000000000000^49 ≤ 3192352831779^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31419557 250000000 3192352831779 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7139851479/10000000000 : ℝ)^65 ≤ (63960848357143/100000000000000 : ℝ)^49 := by
    have hnat : (7139851479 : ℕ)^65*100000000000000^49 ≤ 63960848357143^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7139851479 10000000000 63960848357143 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(999946917/2500000000 : ℝ), (-31419557/250000000 : ℝ), (7139851479/10000000000 : ℝ)] ![(3706805745311/12500000000000 : ℝ), (3192352831779/50000000000000 : ℝ), (63960848357143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(999946917/2500000000 : ℝ)|^65 ≤ (3706805745311/12500000000000 : ℝ)^49
        have hw : |(999946917/2500000000 : ℝ)|=(999946917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31419557/250000000 : ℝ)|^65 ≤ (3192352831779/50000000000000 : ℝ)^49
        have hw : |(-31419557/250000000 : ℝ)|=(31419557/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7139851479/10000000000 : ℝ)|^65 ≤ (63960848357143/100000000000000 : ℝ)^49
        have hw : |(7139851479/10000000000 : ℝ)|=(7139851479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1145533601/2500000000 : ℝ)*x 0 + (7133698951/10000000000 : ℝ)*x 1 + (-210994217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1145533601/2500000000 : ℝ)^65 ≤ (35513713996569/100000000000000 : ℝ)^49 := by
    have hnat : (1145533601 : ℕ)^65*100000000000000^49 ≤ 35513713996569^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145533601 2500000000 35513713996569 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7133698951/10000000000 : ℝ)^65 ≤ (63887745424997/100000000000000 : ℝ)^49 := by
    have hnat : (7133698951 : ℕ)^65*100000000000000^49 ≤ 63887745424997^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7133698951 10000000000 63887745424997 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210994217/10000000000 : ℝ)^65 ≤ (149635141373/25000000000000 : ℝ)^49 := by
    have hnat : (210994217 : ℕ)^65*25000000000000^49 ≤ 149635141373^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210994217 10000000000 149635141373 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1145533601/2500000000 : ℝ), (7133698951/10000000000 : ℝ), (-210994217/10000000000 : ℝ)] ![(35513713996569/100000000000000 : ℝ), (63887745424997/100000000000000 : ℝ), (149635141373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1145533601/2500000000 : ℝ)|^65 ≤ (35513713996569/100000000000000 : ℝ)^49
        have hw : |(1145533601/2500000000 : ℝ)|=(1145533601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7133698951/10000000000 : ℝ)|^65 ≤ (63887745424997/100000000000000 : ℝ)^49
        have hw : |(7133698951/10000000000 : ℝ)|=(7133698951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210994217/10000000000 : ℝ)|^65 ≤ (149635141373/25000000000000 : ℝ)^49
        have hw : |(-210994217/10000000000 : ℝ)|=(210994217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3204063/1000000000 : ℝ)*x 0 + (1641568181/2000000000 : ℝ)*x 1 + (1651162013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3204063/1000000000 : ℝ)^65 ≤ (49117480627/100000000000000 : ℝ)^49 := by
    have hnat : (3204063 : ℕ)^65*100000000000000^49 ≤ 49117480627^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3204063 1000000000 49117480627 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1641568181/2000000000 : ℝ)^65 ≤ (76952378829399/100000000000000 : ℝ)^49 := by
    have hnat : (1641568181 : ℕ)^65*100000000000000^49 ≤ 76952378829399^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641568181 2000000000 76952378829399 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1651162013/5000000000 : ℝ)^65 ≤ (22998503686169/100000000000000 : ℝ)^49 := by
    have hnat : (1651162013 : ℕ)^65*100000000000000^49 ≤ 22998503686169^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651162013 5000000000 22998503686169 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3204063/1000000000 : ℝ), (1641568181/2000000000 : ℝ), (1651162013/5000000000 : ℝ)] ![(49117480627/100000000000000 : ℝ), (76952378829399/100000000000000 : ℝ), (22998503686169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3204063/1000000000 : ℝ)|^65 ≤ (49117480627/100000000000000 : ℝ)^49
        have hw : |(3204063/1000000000 : ℝ)|=(3204063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1641568181/2000000000 : ℝ)|^65 ≤ (76952378829399/100000000000000 : ℝ)^49
        have hw : |(1641568181/2000000000 : ℝ)|=(1641568181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1651162013/5000000000 : ℝ)|^65 ≤ (22998503686169/100000000000000 : ℝ)^49
        have hw : |(1651162013/5000000000 : ℝ)|=(1651162013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2959034071/10000000000 : ℝ)*x 0 + (2177398397/10000000000 : ℝ)*x 1 + (7384302423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2959034071/10000000000 : ℝ)^65 ≤ (9941095470689/50000000000000 : ℝ)^49 := by
    have hnat : (2959034071 : ℕ)^65*50000000000000^49 ≤ 9941095470689^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959034071 10000000000 9941095470689 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177398397/10000000000 : ℝ)^65 ≤ (6617963384079/50000000000000 : ℝ)^49 := by
    have hnat : (2177398397 : ℕ)^65*50000000000000^49 ≤ 6617963384079^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177398397 10000000000 6617963384079 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7384302423/10000000000 : ℝ)^65 ≤ (66881882270693/100000000000000 : ℝ)^49 := by
    have hnat : (7384302423 : ℕ)^65*100000000000000^49 ≤ 66881882270693^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7384302423 10000000000 66881882270693 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2959034071/10000000000 : ℝ), (2177398397/10000000000 : ℝ), (7384302423/10000000000 : ℝ)] ![(9941095470689/50000000000000 : ℝ), (6617963384079/50000000000000 : ℝ), (66881882270693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2959034071/10000000000 : ℝ)|^65 ≤ (9941095470689/50000000000000 : ℝ)^49
        have hw : |(-2959034071/10000000000 : ℝ)|=(2959034071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2177398397/10000000000 : ℝ)|^65 ≤ (6617963384079/50000000000000 : ℝ)^49
        have hw : |(2177398397/10000000000 : ℝ)|=(2177398397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7384302423/10000000000 : ℝ)|^65 ≤ (66881882270693/100000000000000 : ℝ)^49
        have hw : |(7384302423/10000000000 : ℝ)|=(7384302423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3601057023/5000000000 : ℝ)*x 0 + (-2249021959/10000000000 : ℝ)*x 1 + (1568381713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3601057023/5000000000 : ℝ)^65 ≤ (808772417913/1250000000000 : ℝ)^49 := by
    have hnat : (3601057023 : ℕ)^65*1250000000000^49 ≤ 808772417913^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3601057023 5000000000 808772417913 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249021959/10000000000 : ℝ)^65 ≤ (3454138991829/25000000000000 : ℝ)^49 := by
    have hnat : (2249021959 : ℕ)^65*25000000000000^49 ≤ 3454138991829^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249021959 10000000000 3454138991829 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568381713/5000000000 : ℝ)^65 ≤ (10740825292053/50000000000000 : ℝ)^49 := by
    have hnat : (1568381713 : ℕ)^65*50000000000000^49 ≤ 10740825292053^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568381713 5000000000 10740825292053 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3601057023/5000000000 : ℝ), (-2249021959/10000000000 : ℝ), (1568381713/5000000000 : ℝ)] ![(808772417913/1250000000000 : ℝ), (3454138991829/25000000000000 : ℝ), (10740825292053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3601057023/5000000000 : ℝ)|^65 ≤ (808772417913/1250000000000 : ℝ)^49
        have hw : |(3601057023/5000000000 : ℝ)|=(3601057023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249021959/10000000000 : ℝ)|^65 ≤ (3454138991829/25000000000000 : ℝ)^49
        have hw : |(-2249021959/10000000000 : ℝ)|=(2249021959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1568381713/5000000000 : ℝ)|^65 ≤ (10740825292053/50000000000000 : ℝ)^49
        have hw : |(1568381713/5000000000 : ℝ)|=(1568381713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4056503937/5000000000 : ℝ)*x 0 + (3255260661/10000000000 : ℝ)*x 1 + (-91050519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4056503937/5000000000 : ℝ)^65 ≤ (15155037052949/20000000000000 : ℝ)^49 := by
    have hnat : (4056503937 : ℕ)^65*20000000000000^49 ≤ 15155037052949^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056503937 5000000000 15155037052949 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3255260661/10000000000 : ℝ)^65 ≤ (22564728005729/100000000000000 : ℝ)^49 := by
    have hnat : (3255260661 : ℕ)^65*100000000000000^49 ≤ 22564728005729^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3255260661 10000000000 22564728005729 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91050519/2000000000 : ℝ)^65 ≤ (332017343307/20000000000000 : ℝ)^49 := by
    have hnat : (91050519 : ℕ)^65*20000000000000^49 ≤ 332017343307^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91050519 2000000000 332017343307 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4056503937/5000000000 : ℝ), (3255260661/10000000000 : ℝ), (-91050519/2000000000 : ℝ)] ![(15155037052949/20000000000000 : ℝ), (22564728005729/100000000000000 : ℝ), (332017343307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4056503937/5000000000 : ℝ)|^65 ≤ (15155037052949/20000000000000 : ℝ)^49
        have hw : |(4056503937/5000000000 : ℝ)|=(4056503937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3255260661/10000000000 : ℝ)|^65 ≤ (22564728005729/100000000000000 : ℝ)^49
        have hw : |(3255260661/10000000000 : ℝ)|=(3255260661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91050519/2000000000 : ℝ)|^65 ≤ (332017343307/20000000000000 : ℝ)^49
        have hw : |(-91050519/2000000000 : ℝ)|=(91050519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-501909/625000000 : ℝ)*x 0 + (203240741/500000000 : ℝ)*x 1 + (1523474357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501909/625000000 : ℝ)^65 ≤ (3917594209/50000000000000 : ℝ)^49 := by
    have hnat : (501909 : ℕ)^65*50000000000000^49 ≤ 3917594209^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501909 625000000 3917594209 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203240741/500000000 : ℝ)^65 ≤ (30295673175413/100000000000000 : ℝ)^49 := by
    have hnat : (203240741 : ℕ)^65*100000000000000^49 ≤ 30295673175413^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203240741 500000000 30295673175413 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523474357/2000000000 : ℝ)^65 ≤ (4356030726531/6250000000000 : ℝ)^49 := by
    have hnat : (1523474357 : ℕ)^65*6250000000000^49 ≤ 4356030726531^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523474357 2000000000 4356030726531 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501909/625000000 : ℝ), (203240741/500000000 : ℝ), (1523474357/2000000000 : ℝ)] ![(3917594209/50000000000000 : ℝ), (30295673175413/100000000000000 : ℝ), (4356030726531/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501909/625000000 : ℝ)|^65 ≤ (3917594209/50000000000000 : ℝ)^49
        have hw : |(-501909/625000000 : ℝ)|=(501909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203240741/500000000 : ℝ)|^65 ≤ (30295673175413/100000000000000 : ℝ)^49
        have hw : |(203240741/500000000 : ℝ)|=(203240741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1523474357/2000000000 : ℝ)|^65 ≤ (4356030726531/6250000000000 : ℝ)^49
        have hw : |(1523474357/2000000000 : ℝ)|=(1523474357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1320556311/2500000000 : ℝ)*x 0 + (1663827299/5000000000 : ℝ)*x 1 + (1105625873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320556311/2500000000 : ℝ)^65 ≤ (21442635282521/50000000000000 : ℝ)^49 := by
    have hnat : (1320556311 : ℕ)^65*50000000000000^49 ≤ 21442635282521^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320556311 2500000000 21442635282521 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1663827299/5000000000 : ℝ)^65 ≤ (5808202606101/25000000000000 : ℝ)^49 := by
    have hnat : (1663827299 : ℕ)^65*25000000000000^49 ≤ 5808202606101^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663827299 5000000000 5808202606101 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105625873/2500000000 : ℝ)^65 ≤ (16940959498973/50000000000000 : ℝ)^49 := by
    have hnat : (1105625873 : ℕ)^65*50000000000000^49 ≤ 16940959498973^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105625873 2500000000 16940959498973 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1320556311/2500000000 : ℝ), (1663827299/5000000000 : ℝ), (1105625873/2500000000 : ℝ)] ![(21442635282521/50000000000000 : ℝ), (5808202606101/25000000000000 : ℝ), (16940959498973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1320556311/2500000000 : ℝ)|^65 ≤ (21442635282521/50000000000000 : ℝ)^49
        have hw : |(-1320556311/2500000000 : ℝ)|=(1320556311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1663827299/5000000000 : ℝ)|^65 ≤ (5808202606101/25000000000000 : ℝ)^49
        have hw : |(1663827299/5000000000 : ℝ)|=(1663827299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105625873/2500000000 : ℝ)|^65 ≤ (16940959498973/50000000000000 : ℝ)^49
        have hw : |(1105625873/2500000000 : ℝ)|=(1105625873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (476744937/1000000000 : ℝ)*x 0 + (-2829172797/10000000000 : ℝ)*x 1 + (5370213541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (476744937/1000000000 : ℝ)^65 ≤ (18715724935683/50000000000000 : ℝ)^49 := by
    have hnat : (476744937 : ℕ)^65*50000000000000^49 ≤ 18715724935683^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476744937 1000000000 18715724935683 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829172797/10000000000 : ℝ)^65 ≤ (2341636714723/12500000000000 : ℝ)^49 := by
    have hnat : (2829172797 : ℕ)^65*12500000000000^49 ≤ 2341636714723^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829172797 10000000000 2341636714723 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5370213541/10000000000 : ℝ)^65 ≤ (21917728195903/50000000000000 : ℝ)^49 := by
    have hnat : (5370213541 : ℕ)^65*50000000000000^49 ≤ 21917728195903^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370213541 10000000000 21917728195903 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(476744937/1000000000 : ℝ), (-2829172797/10000000000 : ℝ), (5370213541/10000000000 : ℝ)] ![(18715724935683/50000000000000 : ℝ), (2341636714723/12500000000000 : ℝ), (21917728195903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(476744937/1000000000 : ℝ)|^65 ≤ (18715724935683/50000000000000 : ℝ)^49
        have hw : |(476744937/1000000000 : ℝ)|=(476744937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2829172797/10000000000 : ℝ)|^65 ≤ (2341636714723/12500000000000 : ℝ)^49
        have hw : |(-2829172797/10000000000 : ℝ)|=(2829172797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5370213541/10000000000 : ℝ)|^65 ≤ (21917728195903/50000000000000 : ℝ)^49
        have hw : |(5370213541/10000000000 : ℝ)|=(5370213541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1963342203/2500000000 : ℝ)*x 0 + (1144473/3125000 : ℝ)*x 1 + (-40078311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963342203/2500000000 : ℝ)^65 ≤ (72575253698527/100000000000000 : ℝ)^49 := by
    have hnat : (1963342203 : ℕ)^65*100000000000000^49 ≤ 72575253698527^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963342203 2500000000 72575253698527 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144473/3125000 : ℝ)^65 ≤ (26382038863487/100000000000000 : ℝ)^49 := by
    have hnat : (1144473 : ℕ)^65*100000000000000^49 ≤ 26382038863487^49*3125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144473 3125000 26382038863487 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40078311/1250000000 : ℝ)^65 ≤ (521353713221/50000000000000 : ℝ)^49 := by
    have hnat : (40078311 : ℕ)^65*50000000000000^49 ≤ 521353713221^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40078311 1250000000 521353713221 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1963342203/2500000000 : ℝ), (1144473/3125000 : ℝ), (-40078311/1250000000 : ℝ)] ![(72575253698527/100000000000000 : ℝ), (26382038863487/100000000000000 : ℝ), (521353713221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1963342203/2500000000 : ℝ)|^65 ≤ (72575253698527/100000000000000 : ℝ)^49
        have hw : |(1963342203/2500000000 : ℝ)|=(1963342203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144473/3125000 : ℝ)|^65 ≤ (26382038863487/100000000000000 : ℝ)^49
        have hw : |(1144473/3125000 : ℝ)|=(1144473/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40078311/1250000000 : ℝ)|^65 ≤ (521353713221/50000000000000 : ℝ)^49
        have hw : |(-40078311/1250000000 : ℝ)|=(40078311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-162220089/10000000000 : ℝ)*x 0 + (3642681499/5000000000 : ℝ)*x 1 + (1105625873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162220089/10000000000 : ℝ)^65 ≤ (211163577137/50000000000000 : ℝ)^49 := by
    have hnat : (162220089 : ℕ)^65*50000000000000^49 ≤ 211163577137^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162220089 10000000000 211163577137 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3642681499/5000000000 : ℝ)^65 ≤ (65695753832577/100000000000000 : ℝ)^49 := by
    have hnat : (3642681499 : ℕ)^65*100000000000000^49 ≤ 65695753832577^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642681499 5000000000 65695753832577 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105625873/2500000000 : ℝ)^65 ≤ (16940959498973/50000000000000 : ℝ)^49 := by
    have hnat : (1105625873 : ℕ)^65*50000000000000^49 ≤ 16940959498973^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105625873 2500000000 16940959498973 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-162220089/10000000000 : ℝ), (3642681499/5000000000 : ℝ), (1105625873/2500000000 : ℝ)] ![(211163577137/50000000000000 : ℝ), (65695753832577/100000000000000 : ℝ), (16940959498973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-162220089/10000000000 : ℝ)|^65 ≤ (211163577137/50000000000000 : ℝ)^49
        have hw : |(-162220089/10000000000 : ℝ)|=(162220089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3642681499/5000000000 : ℝ)|^65 ≤ (65695753832577/100000000000000 : ℝ)^49
        have hw : |(3642681499/5000000000 : ℝ)|=(3642681499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105625873/2500000000 : ℝ)|^65 ≤ (16940959498973/50000000000000 : ℝ)^49
        have hw : |(1105625873/2500000000 : ℝ)|=(1105625873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301082_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((42969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((48653/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(48653/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(88931/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(88931/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10757/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(10757/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(73799/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(73799/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (42969/50000 : ℝ) ^ (129/32 : ℝ) ≤ (54285551970309632371/100000000000000000000 : ℝ) := by
    have hpowers : (42969/50000 : ℝ)^129 ≤ (54285551970309632371/100000000000000000000 : ℝ)^32 := by
      have hnat : (42969 : ℕ)^129*100000000000000000000^32 ≤ 54285551970309632371^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42969 50000 54285551970309632371 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42969/50000 : ℝ)) (X := (54285551970309632371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (154285551970309632371/100000000000000000000 : ℝ) ≤ (1391958720688231/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (154285551970309632371/100000000000000000000 : ℝ)^32 ≤ (1391958720688231/1250000000000000 : ℝ)^129 := by
      have hnat : (154285551970309632371 : ℕ)^32*1250000000000000^129 ≤ 1391958720688231^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154285551970309632371 100000000000000000000 1391958720688231 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1391958720688231/1250000000000000 : ℝ)) (X := (154285551970309632371/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (104285551970309632371/50000000000000000000 : ℝ) ≤ (1200037521668069/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (104285551970309632371/50000000000000000000 : ℝ)^32 ≤ (1200037521668069/1000000000000000 : ℝ)^129 := by
      have hnat : (104285551970309632371 : ℕ)^32*1000000000000000^129 ≤ 1200037521668069^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104285551970309632371 50000000000000000000 1200037521668069 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1200037521668069/1000000000000000 : ℝ)) (X := (104285551970309632371/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141958720688231/1074225000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(144117575195807/1432300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (42969/50000 : ℝ)) (alpha := (141958720688231/1074225000000000 : ℝ)) (beta := (144117575195807/1432300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42969/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141958720688231/1074225000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(144117575195807/1432300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (48653/50000 : ℝ) ^ (129/32 : ℝ) ≤ (89575211835562777141/100000000000000000000 : ℝ) := by
    have hpowers : (48653/50000 : ℝ)^129 ≤ (89575211835562777141/100000000000000000000 : ℝ)^32 := by
      have hnat : (48653 : ℕ)^129*100000000000000000000^32 ≤ 89575211835562777141^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48653 50000 89575211835562777141 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48653/50000 : ℝ)) (X := (89575211835562777141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (189575211835562777141/100000000000000000000 : ℝ) ≤ (5859722580253979/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (189575211835562777141/100000000000000000000 : ℝ)^32 ≤ (5859722580253979/5000000000000000 : ℝ)^129 := by
      have hnat : (189575211835562777141 : ℕ)^32*5000000000000000^129 ≤ 5859722580253979^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189575211835562777141 100000000000000000000 5859722580253979 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5859722580253979/5000000000000000 : ℝ)) (X := (189575211835562777141/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (139575211835562777141/50000000000000000000 : ℝ) ≤ (6450086657649573/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (139575211835562777141/50000000000000000000 : ℝ)^32 ≤ (6450086657649573/5000000000000000 : ℝ)^129 := by
      have hnat : (139575211835562777141 : ℕ)^32*5000000000000000^129 ≤ 6450086657649573^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139575211835562777141 50000000000000000000 6450086657649573 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6450086657649573/5000000000000000 : ℝ)) (X := (139575211835562777141/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(859722580253979/4865300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(295182038697797/2432650000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (48653/50000 : ℝ)) (alpha := (859722580253979/4865300000000000 : ℝ)) (beta := (295182038697797/2432650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (48653/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(859722580253979/4865300000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(295182038697797/2432650000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (88931/100000 : ℝ) ^ (129/32 : ℝ) ≤ (62319019987138624851/100000000000000000000 : ℝ) := by
    have hpowers : (88931/100000 : ℝ)^129 ≤ (62319019987138624851/100000000000000000000 : ℝ)^32 := by
      have hnat : (88931 : ℕ)^129*100000000000000000000^32 ≤ 62319019987138624851^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88931 100000 62319019987138624851 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88931/100000 : ℝ)) (X := (62319019987138624851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (162319019987138624851/100000000000000000000 : ℝ) ≤ (1409596047585113/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (162319019987138624851/100000000000000000000 : ℝ)^32 ≤ (1409596047585113/1250000000000000 : ℝ)^129 := by
      have hnat : (162319019987138624851 : ℕ)^32*1250000000000000^129 ≤ 1409596047585113^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162319019987138624851 100000000000000000000 1409596047585113 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1409596047585113/1250000000000000 : ℝ)) (X := (162319019987138624851/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (112319019987138624851/50000000000000000000 : ℝ) ≤ (3055833339343107/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (112319019987138624851/50000000000000000000 : ℝ)^32 ≤ (3055833339343107/2500000000000000 : ℝ)^129 := by
      have hnat : (112319019987138624851 : ℕ)^32*2500000000000000^129 ≤ 3055833339343107^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112319019987138624851 50000000000000000000 3055833339343107 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3055833339343107/2500000000000000 : ℝ)) (X := (112319019987138624851/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(159596047585113/1111637500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(236641244172881/2223275000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (88931/100000 : ℝ)) (alpha := (159596047585113/1111637500000000 : ℝ)) (beta := (236641244172881/2223275000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (88931/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(159596047585113/1111637500000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(236641244172881/2223275000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3798393279/10000000000 : ℝ)*X 0 0+(804545721/2500000000 : ℝ)*X 0 1+(1187566907/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4460482357/10000000000 : ℝ)*X 1 0+(-3173685101/10000000000 : ℝ)*X 1 1+(5377452339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1599927823/2500000000 : ℝ)*X 2 0+(5183079743/10000000000 : ℝ)*X 2 1+(-137251463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1417347371/5000000000 : ℝ)*X 0 0+(2085564953/10000000000 : ℝ)*X 0 1+(7536599239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((999946917/2500000000 : ℝ)*X 1 0+(-31419557/250000000 : ℝ)*X 1 1+(7139851479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1145533601/2500000000 : ℝ)*X 2 0+(7133698951/10000000000 : ℝ)*X 2 1+(-210994217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3204063/1000000000 : ℝ)*X 0 0+(1641568181/2000000000 : ℝ)*X 0 1+(1651162013/5000000000 : ℝ)*X 0 2+(3204063/1000000000 : ℝ)*X 1 0+(1641568181/2000000000 : ℝ)*X 1 1+(1651162013/5000000000 : ℝ)*X 1 2+(3204063/1000000000 : ℝ)*X 2 0+(1641568181/2000000000 : ℝ)*X 2 1+(1651162013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2959034071/10000000000 : ℝ)*X 0 0+(2177398397/10000000000 : ℝ)*X 0 1+(7384302423/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3601057023/5000000000 : ℝ)*X 1 0+(-2249021959/10000000000 : ℝ)*X 1 1+(1568381713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4056503937/5000000000 : ℝ)*X 2 0+(3255260661/10000000000 : ℝ)*X 2 1+(-91050519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-501909/625000000 : ℝ)*X 0 0+(203240741/500000000 : ℝ)*X 0 1+(1523474357/2000000000 : ℝ)*X 0 2+(-501909/625000000 : ℝ)*X 1 0+(203240741/500000000 : ℝ)*X 1 1+(1523474357/2000000000 : ℝ)*X 1 2+(-501909/625000000 : ℝ)*X 2 0+(203240741/500000000 : ℝ)*X 2 1+(1523474357/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1320556311/2500000000 : ℝ)*X 0 0+(1663827299/5000000000 : ℝ)*X 0 1+(1105625873/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((476744937/1000000000 : ℝ)*X 1 0+(-2829172797/10000000000 : ℝ)*X 1 1+(5370213541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1963342203/2500000000 : ℝ)*X 2 0+(1144473/3125000 : ℝ)*X 2 1+(-40078311/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((-162220089/10000000000 : ℝ)*X 0 0+(3642681499/5000000000 : ℝ)*X 0 1+(1105625873/2500000000 : ℝ)*X 0 2+(-162220089/10000000000 : ℝ)*X 1 0+(3642681499/5000000000 : ℝ)*X 1 1+(1105625873/2500000000 : ℝ)*X 1 2+(-162220089/10000000000 : ℝ)*X 2 0+(3642681499/5000000000 : ℝ)*X 2 1+(1105625873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((72757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8723932889253561560967/716150000000000000000000000 : ℝ) := by norm_num
    linear_combination (83879143677/125000000000 : ℝ)*(base7) + (64128027951/1000000000000 : ℝ)*(base39) + (6429353923/1000000000000 : ℝ)*(base49) + (17158543/500000000000 : ℝ)*(base53) + (93569383629/1000000000000 : ℝ)*(base60) + (2026329159617/1000000000000 : ℝ)*(major_s1_0) + (2026329159617/1000000000000 : ℝ)*(major_s1_1) + (2026294842531/1000000000000 : ℝ)*(major_s1_2) + (71380361/1000000000000 : ℝ)*(sp_s1_1) + (17726505799/7812500000 : ℝ)*(sp_s1_7) + (2269387645299/1000000000000 : ℝ)*(sp_s1_8) + (1134746671373/500000000000 : ℝ)*(sp_s1_9) + (2040877907277/1000000000000 : ℝ)*(sp_s1_13) + (466283387/1000000000000 : ℝ)*(sp_s1_14) + (68492237893/50000000000 : ℝ)*(f.failure) + (1134746671373/500000000000 : ℝ)*(f.sum) + (1854774354666694141/21633799715000000000000000000000 : ℝ)*base63 + (447877481602539/2223275000000000000000000000 : ℝ)*base64 + (469601303717213/4865300000000000000000000000 : ℝ)*base67 + (1661024051617957/4446550000000000000000000000 : ℝ)*base68 + (5615792197143757589/23882975868750000000000000000000 : ℝ)*base71 + (916922336284541/1432300000000000000000000000 : ℝ)*base72 + (1436039308447659/2432650000000000000000000000 : ℝ)*base74 + (1585573097534641/2148450000000000000000000000 : ℝ)*base76 + (5011387583680749951/17421422975000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (217/1250000000000000 : ℝ)*base86 + (217/1250000000000000 : ℝ)*base88 + (217/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((10757/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(10757/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (896827878123272608353/55581875000000000000000000 : ℝ) := by norm_num
    linear_combination (154682966733/1000000000000 : ℝ)*(base1) + (89784251457/100000000000 : ℝ)*(base7) + (636817/200000000000 : ℝ)*(base33) + (44085834557/250000000000 : ℝ)*(base60) + (1152311400227/500000000000 : ℝ)*(major_s1_0) + (2304625984539/1000000000000 : ℝ)*(major_s1_1) + (2304625984539/1000000000000 : ℝ)*(major_s1_2) + (7409309/250000000000 : ℝ)*(sp_s1_0) + (17543729/500000000000 : ℝ)*(sp_s1_2) + (3049269/100000000000 : ℝ)*(sp_s1_8) + (1326451519391/500000000000 : ℝ)*(sp_s1_14) + (249821603251/100000000000 : ℝ)*(sp_s1_15) + (2498211437741/1000000000000 : ℝ)*(sp_s1_16) + (1150569655391/500000000000 : ℝ)*(sp_s1_20) + (311595952589/200000000000 : ℝ)*(f.failure) + (624562427321/250000000000 : ℝ)*(f.sum) + (12198813228590399447/216337997150000000000000000000000 : ℝ)*base62 + (487260984544143/1111637500000000000000000000 : ℝ)*base64 + (1582474953900799/4865300000000000000000000000 : ℝ)*base66 + (54335363080567/69477343750000000000000000 : ℝ)*base68 + (853143910848920203/4776595173750000000000000000000 : ℝ)*base70 + (270386240180411/716150000000000000000000000 : ℝ)*base72 + (88700757788487/2432650000000000000000000000 : ℝ)*base75 + (156256648185673/2148450000000000000000000000 : ℝ)*base77 + (3706466440628063847/69685691900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1191/5000000000000000 : ℝ)*base86 + (1191/5000000000000000 : ℝ)*base88 + (1191/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(73799/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(73799/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (52921086830214609/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (97975610577/1000000000000 : ℝ)*(base1) + (64389587441/100000000000 : ℝ)*(base7) + (38165201257/500000000000 : ℝ)*(base39) + (476360725877/1000000000000 : ℝ)*(base44) + (2466963271353/1000000000000 : ℝ)*(major_s1_0) + (497650636369/250000000000 : ℝ)*(major_s1_1) + (2466963271353/1000000000000 : ℝ)*(major_s1_2) + (3632597/200000000000 : ℝ)*(sp_s1_13) + (2626929/200000000000 : ℝ)*(sp_s1_15) + (10125737/500000000000 : ℝ)*(sp_s1_16) + (185473370409/62500000000 : ℝ)*(sp_s1_21) + (478644891089/200000000000 : ℝ)*(sp_s1_22) + (2869578064493/1000000000000 : ℝ)*(sp_s1_23) + (1389811879/800000000 : ℝ)*(sp_s1_27) + (1667723473779/1000000000000 : ℝ)*(f.failure) + (2869598315967/1000000000000 : ℝ)*(f.sum) + (631684269638283729/5408449928750000000000000000000 : ℝ)*base62 + (687462197707751/4446550000000000000000000000 : ℝ)*base65 + (286469978100533/608162500000000000000000000 : ℝ)*base67 + (717623152448711/1111637500000000000000000000 : ℝ)*base69 + (158748654750820353/2547517426000000000000000000000 : ℝ)*base70 + (652772735903121/1432300000000000000000000000 : ℝ)*base73 + (303931121130937/608162500000000000000000000 : ℝ)*base75 + (145150750926377/716150000000000000000000000 : ℝ)*base77 + (1122668906203668837/13937138380000000000000000000000 : ℝ)*base78 + (3801/25000000000000000 : ℝ)*base86 + (3801/25000000000000000 : ℝ)*base88 + (3801/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((42969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((48653/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(48653/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(88931/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(88931/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10757/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(10757/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(73799/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(73799/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301082_s1 p hpa hpb X hX hprev0

#print axioms solution

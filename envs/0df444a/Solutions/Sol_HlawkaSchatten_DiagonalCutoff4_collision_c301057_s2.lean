-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301057_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:34:09.262991+00:00
-- url     : https://prove2.me/submissions/8242071b-d2b5-4787-9e27-693025d742f1

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
theorem collision_support_c301057_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-156434893/500000000 : ℝ)*x 0 + (1562549459/5000000000 : ℝ)*x 1 + (6564544439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156434893/500000000 : ℝ)^65 ≤ (214084093681/1000000000000 : ℝ)^49 := by
    have hnat : (156434893 : ℕ)^65*1000000000000^49 ≤ 214084093681^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156434893 500000000 214084093681 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562549459/5000000000 : ℝ)^65 ≤ (10687874115193/50000000000000 : ℝ)^49 := by
    have hnat : (1562549459 : ℕ)^65*50000000000000^49 ≤ 10687874115193^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562549459 5000000000 10687874115193 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6564544439/10000000000 : ℝ)^65 ≤ (28607921189977/50000000000000 : ℝ)^49 := by
    have hnat : (6564544439 : ℕ)^65*50000000000000^49 ≤ 28607921189977^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6564544439 10000000000 28607921189977 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156434893/500000000 : ℝ), (1562549459/5000000000 : ℝ), (6564544439/10000000000 : ℝ)] ![(214084093681/1000000000000 : ℝ), (10687874115193/50000000000000 : ℝ), (28607921189977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156434893/500000000 : ℝ)|^65 ≤ (214084093681/1000000000000 : ℝ)^49
        have hw : |(-156434893/500000000 : ℝ)|=(156434893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562549459/5000000000 : ℝ)|^65 ≤ (10687874115193/50000000000000 : ℝ)^49
        have hw : |(1562549459/5000000000 : ℝ)|=(1562549459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6564544439/10000000000 : ℝ)|^65 ≤ (28607921189977/50000000000000 : ℝ)^49
        have hw : |(6564544439/10000000000 : ℝ)|=(6564544439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3126543983/10000000000 : ℝ)*x 0 + (-1561473759/5000000000 : ℝ)*x 1 + (656792309/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3126543983/10000000000 : ℝ)^65 ≤ (1336803813571/6250000000000 : ℝ)^49 := by
    have hnat : (3126543983 : ℕ)^65*6250000000000^49 ≤ 1336803813571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126543983 10000000000 1336803813571 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561473759/5000000000 : ℝ)^65 ≤ (5339057424331/25000000000000 : ℝ)^49 := by
    have hnat : (1561473759 : ℕ)^65*25000000000000^49 ≤ 5339057424331^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561473759 5000000000 5339057424331 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656792309/1000000000 : ℝ)^65 ≤ (57254909266523/100000000000000 : ℝ)^49 := by
    have hnat : (656792309 : ℕ)^65*100000000000000^49 ≤ 57254909266523^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656792309 1000000000 57254909266523 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3126543983/10000000000 : ℝ), (-1561473759/5000000000 : ℝ), (656792309/1000000000 : ℝ)] ![(1336803813571/6250000000000 : ℝ), (5339057424331/25000000000000 : ℝ), (57254909266523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3126543983/10000000000 : ℝ)|^65 ≤ (1336803813571/6250000000000 : ℝ)^49
        have hw : |(3126543983/10000000000 : ℝ)|=(3126543983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1561473759/5000000000 : ℝ)|^65 ≤ (5339057424331/25000000000000 : ℝ)^49
        have hw : |(-1561473759/5000000000 : ℝ)|=(1561473759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656792309/1000000000 : ℝ)|^65 ≤ (57254909266523/100000000000000 : ℝ)^49
        have hw : |(656792309/1000000000 : ℝ)|=(656792309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (370460341/625000000 : ℝ)*x 0 + (5932385717/10000000000 : ℝ)*x 1 + (3830807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370460341/625000000 : ℝ)^65 ≤ (49968245221311/100000000000000 : ℝ)^49 := by
    have hnat : (370460341 : ℕ)^65*100000000000000^49 ≤ 49968245221311^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370460341 625000000 49968245221311 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5932385717/10000000000 : ℝ)^65 ≤ (25012196721437/50000000000000 : ℝ)^49 := by
    have hnat : (5932385717 : ℕ)^65*50000000000000^49 ≤ 25012196721437^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5932385717 10000000000 25012196721437 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3830807/5000000000 : ℝ)^65 ≤ (368065797/5000000000000 : ℝ)^49 := by
    have hnat : (3830807 : ℕ)^65*5000000000000^49 ≤ 368065797^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3830807 5000000000 368065797 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(370460341/625000000 : ℝ), (5932385717/10000000000 : ℝ), (3830807/5000000000 : ℝ)] ![(49968245221311/100000000000000 : ℝ), (25012196721437/50000000000000 : ℝ), (368065797/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(370460341/625000000 : ℝ)|^65 ≤ (49968245221311/100000000000000 : ℝ)^49
        have hw : |(370460341/625000000 : ℝ)|=(370460341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5932385717/10000000000 : ℝ)|^65 ≤ (25012196721437/50000000000000 : ℝ)^49
        have hw : |(5932385717/10000000000 : ℝ)|=(5932385717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3830807/5000000000 : ℝ)|^65 ≤ (368065797/5000000000000 : ℝ)^49
        have hw : |(3830807/5000000000 : ℝ)|=(3830807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2471750891/5000000000 : ℝ)*x 0 + (2473844373/5000000000 : ℝ)*x 1 + (3128189269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2471750891/5000000000 : ℝ)^65 ≤ (3927603665703/10000000000000 : ℝ)^49 := by
    have hnat : (2471750891 : ℕ)^65*10000000000000^49 ≤ 3927603665703^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2471750891 5000000000 3927603665703 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2473844373/5000000000 : ℝ)^65 ≤ (39320170272181/100000000000000 : ℝ)^49 := by
    have hnat : (2473844373 : ℕ)^65*100000000000000^49 ≤ 39320170272181^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2473844373 5000000000 39320170272181 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3128189269/10000000000 : ℝ)^65 ≤ (21403793055647/100000000000000 : ℝ)^49 := by
    have hnat : (3128189269 : ℕ)^65*100000000000000^49 ≤ 21403793055647^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3128189269 10000000000 21403793055647 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2471750891/5000000000 : ℝ), (2473844373/5000000000 : ℝ), (3128189269/10000000000 : ℝ)] ![(3927603665703/10000000000000 : ℝ), (39320170272181/100000000000000 : ℝ), (21403793055647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2471750891/5000000000 : ℝ)|^65 ≤ (3927603665703/10000000000000 : ℝ)^49
        have hw : |(2471750891/5000000000 : ℝ)|=(2471750891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2473844373/5000000000 : ℝ)|^65 ≤ (39320170272181/100000000000000 : ℝ)^49
        have hw : |(2473844373/5000000000 : ℝ)|=(2473844373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3128189269/10000000000 : ℝ)|^65 ≤ (21403793055647/100000000000000 : ℝ)^49
        have hw : |(3128189269/10000000000 : ℝ)|=(3128189269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-516644761/2500000000 : ℝ)*x 0 + (1445018709/10000000000 : ℝ)*x 1 + (8449076921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516644761/2500000000 : ℝ)^65 ≤ (2469965231993/20000000000000 : ℝ)^49 := by
    have hnat : (516644761 : ℕ)^65*20000000000000^49 ≤ 2469965231993^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516644761 2500000000 2469965231993 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445018709/10000000000 : ℝ)^65 ≤ (1536655219747/20000000000000 : ℝ)^49 := by
    have hnat : (1445018709 : ℕ)^65*20000000000000^49 ≤ 1536655219747^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445018709 10000000000 1536655219747 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8449076921/10000000000 : ℝ)^65 ≤ (15993379545823/20000000000000 : ℝ)^49 := by
    have hnat : (8449076921 : ℕ)^65*20000000000000^49 ≤ 15993379545823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8449076921 10000000000 15993379545823 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516644761/2500000000 : ℝ), (1445018709/10000000000 : ℝ), (8449076921/10000000000 : ℝ)] ![(2469965231993/20000000000000 : ℝ), (1536655219747/20000000000000 : ℝ), (15993379545823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516644761/2500000000 : ℝ)|^65 ≤ (2469965231993/20000000000000 : ℝ)^49
        have hw : |(-516644761/2500000000 : ℝ)|=(516644761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1445018709/10000000000 : ℝ)|^65 ≤ (1536655219747/20000000000000 : ℝ)^49
        have hw : |(1445018709/10000000000 : ℝ)|=(1445018709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8449076921/10000000000 : ℝ)|^65 ≤ (15993379545823/20000000000000 : ℝ)^49
        have hw : |(8449076921/10000000000 : ℝ)|=(8449076921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1867048203/10000000000 : ℝ)*x 0 + (-1653164123/10000000000 : ℝ)*x 1 + (1690686191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867048203/10000000000 : ℝ)^65 ≤ (5396789813581/50000000000000 : ℝ)^49 := by
    have hnat : (1867048203 : ℕ)^65*50000000000000^49 ≤ 5396789813581^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867048203 10000000000 5396789813581 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1653164123/10000000000 : ℝ)^65 ≤ (918485294291/10000000000000 : ℝ)^49 := by
    have hnat : (1653164123 : ℕ)^65*10000000000000^49 ≤ 918485294291^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653164123 10000000000 918485294291 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690686191/2000000000 : ℝ)^65 ≤ (80021567419007/100000000000000 : ℝ)^49 := by
    have hnat : (1690686191 : ℕ)^65*100000000000000^49 ≤ 80021567419007^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690686191 2000000000 80021567419007 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1867048203/10000000000 : ℝ), (-1653164123/10000000000 : ℝ), (1690686191/2000000000 : ℝ)] ![(5396789813581/50000000000000 : ℝ), (918485294291/10000000000000 : ℝ), (80021567419007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1867048203/10000000000 : ℝ)|^65 ≤ (5396789813581/50000000000000 : ℝ)^49
        have hw : |(1867048203/10000000000 : ℝ)|=(1867048203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1653164123/10000000000 : ℝ)|^65 ≤ (918485294291/10000000000000 : ℝ)^49
        have hw : |(-1653164123/10000000000 : ℝ)|=(1653164123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1690686191/2000000000 : ℝ)|^65 ≤ (80021567419007/100000000000000 : ℝ)^49
        have hw : |(1690686191/2000000000 : ℝ)|=(1690686191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3516336151/10000000000 : ℝ)*x 0 + (8050662819/10000000000 : ℝ)*x 1 + (-105891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3516336151/10000000000 : ℝ)^65 ≤ (12498129078121/50000000000000 : ℝ)^49 := by
    have hnat : (3516336151 : ℕ)^65*50000000000000^49 ≤ 12498129078121^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3516336151 10000000000 12498129078121 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8050662819/10000000000 : ℝ)^65 ≤ (937546458731/1250000000000 : ℝ)^49 := by
    have hnat : (8050662819 : ℕ)^65*1250000000000^49 ≤ 937546458731^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8050662819 10000000000 937546458731 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105891/10000000000 : ℝ)^65 ≤ (25137567/100000000000000 : ℝ)^49 := by
    have hnat : (105891 : ℕ)^65*100000000000000^49 ≤ 25137567^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105891 10000000000 25137567 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3516336151/10000000000 : ℝ), (8050662819/10000000000 : ℝ), (-105891/10000000000 : ℝ)] ![(12498129078121/50000000000000 : ℝ), (937546458731/1250000000000 : ℝ), (25137567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3516336151/10000000000 : ℝ)|^65 ≤ (12498129078121/50000000000000 : ℝ)^49
        have hw : |(3516336151/10000000000 : ℝ)|=(3516336151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8050662819/10000000000 : ℝ)|^65 ≤ (937546458731/1250000000000 : ℝ)^49
        have hw : |(8050662819/10000000000 : ℝ)|=(8050662819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105891/10000000000 : ℝ)|^65 ≤ (25137567/100000000000000 : ℝ)^49
        have hw : |(-105891/10000000000 : ℝ)|=(105891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (622022241/2000000000 : ℝ)*x 0 + (7401419893/10000000000 : ℝ)*x 1 + (396109673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (622022241/2000000000 : ℝ)^65 ≤ (21239863816327/100000000000000 : ℝ)^49 := by
    have hnat : (622022241 : ℕ)^65*100000000000000^49 ≤ 21239863816327^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622022241 2000000000 21239863816327 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7401419893/10000000000 : ℝ)^65 ≤ (33543811461467/50000000000000 : ℝ)^49 := by
    have hnat : (7401419893 : ℕ)^65*50000000000000^49 ≤ 33543811461467^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7401419893 10000000000 33543811461467 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396109673/2000000000 : ℝ)^65 ≤ (11672513249101/100000000000000 : ℝ)^49 := by
    have hnat : (396109673 : ℕ)^65*100000000000000^49 ≤ 11672513249101^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396109673 2000000000 11672513249101 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(622022241/2000000000 : ℝ), (7401419893/10000000000 : ℝ), (396109673/2000000000 : ℝ)] ![(21239863816327/100000000000000 : ℝ), (33543811461467/50000000000000 : ℝ), (11672513249101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(622022241/2000000000 : ℝ)|^65 ≤ (21239863816327/100000000000000 : ℝ)^49
        have hw : |(622022241/2000000000 : ℝ)|=(622022241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7401419893/10000000000 : ℝ)|^65 ≤ (33543811461467/50000000000000 : ℝ)^49
        have hw : |(7401419893/10000000000 : ℝ)|=(7401419893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396109673/2000000000 : ℝ)|^65 ≤ (11672513249101/100000000000000 : ℝ)^49
        have hw : |(396109673/2000000000 : ℝ)|=(396109673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-166578953/1000000000 : ℝ)*x 0 + (1872410979/10000000000 : ℝ)*x 1 + (8442732717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166578953/1000000000 : ℝ)^65 ≤ (2319504826869/25000000000000 : ℝ)^49 := by
    have hnat : (166578953 : ℕ)^65*25000000000000^49 ≤ 2319504826869^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166578953 1000000000 2319504826869 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872410979/10000000000 : ℝ)^65 ≤ (10834724941747/100000000000000 : ℝ)^49 := by
    have hnat : (1872410979 : ℕ)^65*100000000000000^49 ≤ 10834724941747^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872410979 10000000000 10834724941747 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8442732717/10000000000 : ℝ)^65 ≤ (79887255731077/100000000000000 : ℝ)^49 := by
    have hnat : (8442732717 : ℕ)^65*100000000000000^49 ≤ 79887255731077^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8442732717 10000000000 79887255731077 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166578953/1000000000 : ℝ), (1872410979/10000000000 : ℝ), (8442732717/10000000000 : ℝ)] ![(2319504826869/25000000000000 : ℝ), (10834724941747/100000000000000 : ℝ), (79887255731077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166578953/1000000000 : ℝ)|^65 ≤ (2319504826869/25000000000000 : ℝ)^49
        have hw : |(-166578953/1000000000 : ℝ)|=(166578953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1872410979/10000000000 : ℝ)|^65 ≤ (10834724941747/100000000000000 : ℝ)^49
        have hw : |(1872410979/10000000000 : ℝ)|=(1872410979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8442732717/10000000000 : ℝ)|^65 ≤ (79887255731077/100000000000000 : ℝ)^49
        have hw : |(8442732717/10000000000 : ℝ)|=(8442732717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (145278419/1000000000 : ℝ)*x 0 + (-128926189/625000000 : ℝ)*x 1 + (422354193/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (145278419/1000000000 : ℝ)^65 ≤ (1934524024481/25000000000000 : ℝ)^49 := by
    have hnat : (145278419 : ℕ)^65*25000000000000^49 ≤ 1934524024481^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145278419 1000000000 1934524024481 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128926189/625000000 : ℝ)^65 ≤ (1503909687/12207031250 : ℝ)^49 := by
    have hnat : (128926189 : ℕ)^65*12207031250^49 ≤ 1503909687^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128926189 625000000 1503909687 12207031250 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422354193/500000000 : ℝ)^65 ≤ (79941875723071/100000000000000 : ℝ)^49 := by
    have hnat : (422354193 : ℕ)^65*100000000000000^49 ≤ 79941875723071^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422354193 500000000 79941875723071 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(145278419/1000000000 : ℝ), (-128926189/625000000 : ℝ), (422354193/500000000 : ℝ)] ![(1934524024481/25000000000000 : ℝ), (1503909687/12207031250 : ℝ), (79941875723071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(145278419/1000000000 : ℝ)|^65 ≤ (1934524024481/25000000000000 : ℝ)^49
        have hw : |(145278419/1000000000 : ℝ)|=(145278419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128926189/625000000 : ℝ)|^65 ≤ (1503909687/12207031250 : ℝ)^49
        have hw : |(-128926189/625000000 : ℝ)|=(128926189/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422354193/500000000 : ℝ)|^65 ≤ (79941875723071/100000000000000 : ℝ)^49
        have hw : |(422354193/500000000 : ℝ)|=(422354193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4035808779/5000000000 : ℝ)*x 0 + (697765399/2000000000 : ℝ)*x 1 + (-16457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035808779/5000000000 : ℝ)^65 ≤ (15052559482933/20000000000000 : ℝ)^49 := by
    have hnat : (4035808779 : ℕ)^65*20000000000000^49 ≤ 15052559482933^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035808779 5000000000 15052559482933 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697765399/2000000000 : ℝ)^65 ≤ (24737184582231/100000000000000 : ℝ)^49 := by
    have hnat : (697765399 : ℕ)^65*100000000000000^49 ≤ 24737184582231^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697765399 2000000000 24737184582231 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16457/2000000000 : ℝ)^65 ≤ (17989423/100000000000000 : ℝ)^49 := by
    have hnat : (16457 : ℕ)^65*100000000000000^49 ≤ 17989423^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16457 2000000000 17989423 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035808779/5000000000 : ℝ), (697765399/2000000000 : ℝ), (-16457/2000000000 : ℝ)] ![(15052559482933/20000000000000 : ℝ), (24737184582231/100000000000000 : ℝ), (17989423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035808779/5000000000 : ℝ)|^65 ≤ (15052559482933/20000000000000 : ℝ)^49
        have hw : |(4035808779/5000000000 : ℝ)|=(4035808779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(697765399/2000000000 : ℝ)|^65 ≤ (24737184582231/100000000000000 : ℝ)^49
        have hw : |(697765399/2000000000 : ℝ)|=(697765399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16457/2000000000 : ℝ)|^65 ≤ (17989423/100000000000000 : ℝ)^49
        have hw : |(-16457/2000000000 : ℝ)|=(16457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3681504619/5000000000 : ℝ)*x 0 + (1579484177/5000000000 : ℝ)*x 1 + (1982813499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3681504619/5000000000 : ℝ)^65 ≤ (66626169584161/100000000000000 : ℝ)^49 := by
    have hnat : (3681504619 : ℕ)^65*100000000000000^49 ≤ 66626169584161^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681504619 5000000000 66626169584161 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1579484177/5000000000 : ℝ)^65 ≤ (10841802505491/50000000000000 : ℝ)^49 := by
    have hnat : (1579484177 : ℕ)^65*50000000000000^49 ≤ 10841802505491^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579484177 5000000000 10841802505491 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982813499/10000000000 : ℝ)^65 ≤ (1169022539431/10000000000000 : ℝ)^49 := by
    have hnat : (1982813499 : ℕ)^65*10000000000000^49 ≤ 1169022539431^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982813499 10000000000 1169022539431 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3681504619/5000000000 : ℝ), (1579484177/5000000000 : ℝ), (1982813499/10000000000 : ℝ)] ![(66626169584161/100000000000000 : ℝ), (10841802505491/50000000000000 : ℝ), (1169022539431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3681504619/5000000000 : ℝ)|^65 ≤ (66626169584161/100000000000000 : ℝ)^49
        have hw : |(3681504619/5000000000 : ℝ)|=(3681504619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1579484177/5000000000 : ℝ)|^65 ≤ (10841802505491/50000000000000 : ℝ)^49
        have hw : |(1579484177/5000000000 : ℝ)|=(1579484177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1982813499/10000000000 : ℝ)|^65 ≤ (1169022539431/10000000000000 : ℝ)^49
        have hw : |(1982813499/10000000000 : ℝ)|=(1982813499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1389924793/2500000000 : ℝ)*x 0 + (337642263/2000000000 : ℝ)*x 1 + (2722956091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1389924793/2500000000 : ℝ)^65 ≤ (45898948434017/100000000000000 : ℝ)^49 := by
    have hnat : (1389924793 : ℕ)^65*100000000000000^49 ≤ 45898948434017^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389924793 2500000000 45898948434017 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337642263/2000000000 : ℝ)^65 ≤ (4722022077677/50000000000000 : ℝ)^49 := by
    have hnat : (337642263 : ℕ)^65*50000000000000^49 ≤ 4722022077677^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337642263 2000000000 4722022077677 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722956091/5000000000 : ℝ)^65 ≤ (44657007399579/100000000000000 : ℝ)^49 := by
    have hnat : (2722956091 : ℕ)^65*100000000000000^49 ≤ 44657007399579^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722956091 5000000000 44657007399579 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1389924793/2500000000 : ℝ), (337642263/2000000000 : ℝ), (2722956091/5000000000 : ℝ)] ![(45898948434017/100000000000000 : ℝ), (4722022077677/50000000000000 : ℝ), (44657007399579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1389924793/2500000000 : ℝ)|^65 ≤ (45898948434017/100000000000000 : ℝ)^49
        have hw : |(-1389924793/2500000000 : ℝ)|=(1389924793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337642263/2000000000 : ℝ)|^65 ≤ (4722022077677/50000000000000 : ℝ)^49
        have hw : |(337642263/2000000000 : ℝ)|=(337642263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722956091/5000000000 : ℝ)|^65 ≤ (44657007399579/100000000000000 : ℝ)^49
        have hw : |(2722956091/5000000000 : ℝ)|=(2722956091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (545827531/5000000000 : ℝ)*x 0 + (-5442671433/10000000000 : ℝ)*x 1 + (742188713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545827531/5000000000 : ℝ)^65 ≤ (5296523218159/100000000000000 : ℝ)^49 := by
    have hnat : (545827531 : ℕ)^65*100000000000000^49 ≤ 5296523218159^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545827531 5000000000 5296523218159 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442671433/10000000000 : ℝ)^65 ≤ (8924351799191/20000000000000 : ℝ)^49 := by
    have hnat : (5442671433 : ℕ)^65*20000000000000^49 ≤ 8924351799191^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442671433 10000000000 8924351799191 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742188713/1250000000 : ℝ)^65 ≤ (50081717771037/100000000000000 : ℝ)^49 := by
    have hnat : (742188713 : ℕ)^65*100000000000000^49 ≤ 50081717771037^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742188713 1250000000 50081717771037 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545827531/5000000000 : ℝ), (-5442671433/10000000000 : ℝ), (742188713/1250000000 : ℝ)] ![(5296523218159/100000000000000 : ℝ), (8924351799191/20000000000000 : ℝ), (50081717771037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545827531/5000000000 : ℝ)|^65 ≤ (5296523218159/100000000000000 : ℝ)^49
        have hw : |(545827531/5000000000 : ℝ)|=(545827531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5442671433/10000000000 : ℝ)|^65 ≤ (8924351799191/20000000000000 : ℝ)^49
        have hw : |(-5442671433/10000000000 : ℝ)|=(5442671433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(742188713/1250000000 : ℝ)|^65 ≤ (50081717771037/100000000000000 : ℝ)^49
        have hw : |(742188713/1250000000 : ℝ)|=(742188713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6291041911/10000000000 : ℝ)*x 0 + (5529496023/10000000000 : ℝ)*x 1 + (28533819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6291041911/10000000000 : ℝ)^65 ≤ (54075349964773/100000000000000 : ℝ)^49 := by
    have hnat : (6291041911 : ℕ)^65*100000000000000^49 ≤ 54075349964773^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6291041911 10000000000 54075349964773 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529496023/10000000000 : ℝ)^65 ≤ (72909561759/160000000000 : ℝ)^49 := by
    have hnat : (5529496023 : ℕ)^65*160000000000^49 ≤ 72909561759^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529496023 10000000000 72909561759 160000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28533819/2000000000 : ℝ)^65 ≤ (356173923771/100000000000000 : ℝ)^49 := by
    have hnat : (28533819 : ℕ)^65*100000000000000^49 ≤ 356173923771^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28533819 2000000000 356173923771 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6291041911/10000000000 : ℝ), (5529496023/10000000000 : ℝ), (28533819/2000000000 : ℝ)] ![(54075349964773/100000000000000 : ℝ), (72909561759/160000000000 : ℝ), (356173923771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6291041911/10000000000 : ℝ)|^65 ≤ (54075349964773/100000000000000 : ℝ)^49
        have hw : |(6291041911/10000000000 : ℝ)|=(6291041911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529496023/10000000000 : ℝ)|^65 ≤ (72909561759/160000000000 : ℝ)^49
        have hw : |(5529496023/10000000000 : ℝ)|=(5529496023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28533819/2000000000 : ℝ)|^65 ≤ (356173923771/100000000000000 : ℝ)^49
        have hw : |(28533819/2000000000 : ℝ)|=(28533819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s2_s2_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1509136189/5000000000 : ℝ)*x 0 + (5529496023/10000000000 : ℝ)*x 1 + (4436045589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1509136189/5000000000 : ℝ)^65 ≤ (20411909335539/100000000000000 : ℝ)^49 := by
    have hnat : (1509136189 : ℕ)^65*100000000000000^49 ≤ 20411909335539^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509136189 5000000000 20411909335539 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529496023/10000000000 : ℝ)^65 ≤ (72909561759/160000000000 : ℝ)^49 := by
    have hnat : (5529496023 : ℕ)^65*160000000000^49 ≤ 72909561759^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529496023 10000000000 72909561759 160000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436045589/10000000000 : ℝ)^65 ≤ (6803922910981/20000000000000 : ℝ)^49 := by
    have hnat : (4436045589 : ℕ)^65*20000000000000^49 ≤ 6803922910981^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436045589 10000000000 6803922910981 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1509136189/5000000000 : ℝ), (5529496023/10000000000 : ℝ), (4436045589/10000000000 : ℝ)] ![(20411909335539/100000000000000 : ℝ), (72909561759/160000000000 : ℝ), (6803922910981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1509136189/5000000000 : ℝ)|^65 ≤ (20411909335539/100000000000000 : ℝ)^49
        have hw : |(1509136189/5000000000 : ℝ)|=(1509136189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529496023/10000000000 : ℝ)|^65 ≤ (72909561759/160000000000 : ℝ)^49
        have hw : |(5529496023/10000000000 : ℝ)|=(5529496023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4436045589/10000000000 : ℝ)|^65 ≤ (6803922910981/20000000000000 : ℝ)^49
        have hw : |(4436045589/10000000000 : ℝ)|=(4436045589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301057_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((45641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4507/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4507/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((83321/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(83321/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20817/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20817/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8859/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8859/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (45641/50000 : ℝ) ^ (129/32 : ℝ) ≤ (553850574681716661/800000000000000000 : ℝ) := by
    have hpowers : (45641/50000 : ℝ)^129 ≤ (553850574681716661/800000000000000000 : ℝ)^32 := by
      have hnat : (45641 : ℕ)^129*800000000000000000^32 ≤ 553850574681716661^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45641 50000 553850574681716661 800000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45641/50000 : ℝ)) (X := (553850574681716661/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (1353850574681716661/800000000000000000 : ℝ) ≤ (1139403094232389/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1353850574681716661/800000000000000000 : ℝ)^32 ≤ (1139403094232389/1000000000000000 : ℝ)^129 := by
      have hnat : (1353850574681716661 : ℕ)^32*1000000000000000^129 ≤ 1139403094232389^129*800000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1353850574681716661 800000000000000000 1139403094232389 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1139403094232389/1000000000000000 : ℝ)) (X := (1353850574681716661/800000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (953850574681716661/400000000000000000 : ℝ) ≤ (1550720995085053/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (953850574681716661/400000000000000000 : ℝ)^32 ≤ (1550720995085053/1250000000000000 : ℝ)^129 := by
      have hnat : (953850574681716661 : ℕ)^32*1250000000000000^129 ≤ 1550720995085053^129*400000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        953850574681716661 400000000000000000 1550720995085053 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1550720995085053/1250000000000000 : ℝ)) (X := (953850574681716661/400000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(139403094232389/912820000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(505868509178267/4564100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (45641/50000 : ℝ)) (alpha := (139403094232389/912820000000000 : ℝ)) (beta := (505868509178267/4564100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (45641/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(139403094232389/912820000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(505868509178267/4564100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (91033/100000 : ℝ) ^ (129/32 : ℝ) ≤ (13694632446008067521/20000000000000000000 : ℝ) := by
    have hpowers : (91033/100000 : ℝ)^129 ≤ (13694632446008067521/20000000000000000000 : ℝ)^32 := by
      have hnat : (91033 : ℕ)^129*20000000000000000000^32 ≤ 13694632446008067521^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91033 100000 13694632446008067521 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91033/100000 : ℝ)) (X := (13694632446008067521/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (33694632446008067521/20000000000000000000 : ℝ) ≤ (5690673556905793/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (33694632446008067521/20000000000000000000 : ℝ)^32 ≤ (5690673556905793/5000000000000000 : ℝ)^129 := by
      have hnat : (33694632446008067521 : ℕ)^32*5000000000000000^129 ≤ 5690673556905793^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33694632446008067521 20000000000000000000 5690673556905793 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5690673556905793/5000000000000000 : ℝ)) (X := (33694632446008067521/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (23694632446008067521/10000000000000000000 : ℝ) ≤ (12386152654578637/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (23694632446008067521/10000000000000000000 : ℝ)^32 ≤ (12386152654578637/10000000000000000 : ℝ)^129 := by
      have hnat : (23694632446008067521 : ℕ)^32*10000000000000000^129 ≤ 12386152654578637^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23694632446008067521 10000000000000000000 12386152654578637 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12386152654578637/10000000000000000 : ℝ)) (X := (23694632446008067521/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(690673556905793/4551650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1004805540767051/9103300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (91033/100000 : ℝ)) (alpha := (690673556905793/4551650000000000 : ℝ)) (beta := (1004805540767051/9103300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (91033/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(690673556905793/4551650000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1004805540767051/9103300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (4507/10000 : ℝ) ^ (129/32 : ℝ) ≤ (4024706531085425937/100000000000000000000 : ℝ) := by
    have hpowers : (4507/10000 : ℝ)^129 ≤ (4024706531085425937/100000000000000000000 : ℝ)^32 := by
      have hnat : (4507 : ℕ)^129*100000000000000000000^32 ≤ 4024706531085425937^32*10000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4507 10000 4024706531085425937 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4507/10000 : ℝ)) (X := (4024706531085425937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (104024706531085425937/100000000000000000000 : ℝ) ≤ (2019672305033497/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (104024706531085425937/100000000000000000000 : ℝ)^32 ≤ (2019672305033497/2000000000000000 : ℝ)^129 := by
      have hnat : (104024706531085425937 : ℕ)^32*2000000000000000^129 ≤ 2019672305033497^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104024706531085425937 100000000000000000000 2019672305033497 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2019672305033497/2000000000000000 : ℝ)) (X := (104024706531085425937/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (54024706531085425937/50000000000000000000 : ℝ) ≤ (10193901745659939/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (54024706531085425937/50000000000000000000 : ℝ)^32 ≤ (10193901745659939/10000000000000000 : ℝ)^129 := by
      have hnat : (54024706531085425937 : ℕ)^32*10000000000000000^129 ≤ 10193901745659939^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54024706531085425937 50000000000000000000 10193901745659939 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10193901745659939/10000000000000000 : ℝ)) (X := (54024706531085425937/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(19672305033497/901400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(47770110246227/2253500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (4507/10000 : ℝ)) (alpha := (19672305033497/901400000000000 : ℝ)) (beta := (47770110246227/2253500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4507/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(19672305033497/901400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(47770110246227/2253500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-156434893/500000000 : ℝ)*X 0 0+(1562549459/5000000000 : ℝ)*X 0 1+(6564544439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((3126543983/10000000000 : ℝ)*X 1 0+(-1561473759/5000000000 : ℝ)*X 1 1+(656792309/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((370460341/625000000 : ℝ)*X 2 0+(5932385717/10000000000 : ℝ)*X 2 1+(3830807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2471750891/5000000000 : ℝ)*X 0 0+(2473844373/5000000000 : ℝ)*X 0 1+(3128189269/10000000000 : ℝ)*X 0 2+(2471750891/5000000000 : ℝ)*X 1 0+(2473844373/5000000000 : ℝ)*X 1 1+(3128189269/10000000000 : ℝ)*X 1 2+(2471750891/5000000000 : ℝ)*X 2 0+(2473844373/5000000000 : ℝ)*X 2 1+(3128189269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-516644761/2500000000 : ℝ)*X 0 0+(1445018709/10000000000 : ℝ)*X 0 1+(8449076921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1867048203/10000000000 : ℝ)*X 1 0+(-1653164123/10000000000 : ℝ)*X 1 1+(1690686191/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3516336151/10000000000 : ℝ)*X 2 0+(8050662819/10000000000 : ℝ)*X 2 1+(-105891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((622022241/2000000000 : ℝ)*X 0 0+(7401419893/10000000000 : ℝ)*X 0 1+(396109673/2000000000 : ℝ)*X 0 2+(622022241/2000000000 : ℝ)*X 1 0+(7401419893/10000000000 : ℝ)*X 1 1+(396109673/2000000000 : ℝ)*X 1 2+(622022241/2000000000 : ℝ)*X 2 0+(7401419893/10000000000 : ℝ)*X 2 1+(396109673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-166578953/1000000000 : ℝ)*X 0 0+(1872410979/10000000000 : ℝ)*X 0 1+(8442732717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((145278419/1000000000 : ℝ)*X 1 0+(-128926189/625000000 : ℝ)*X 1 1+(422354193/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((4035808779/5000000000 : ℝ)*X 2 0+(697765399/2000000000 : ℝ)*X 2 1+(-16457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3681504619/5000000000 : ℝ)*X 0 0+(1579484177/5000000000 : ℝ)*X 0 1+(1982813499/10000000000 : ℝ)*X 0 2+(3681504619/5000000000 : ℝ)*X 1 0+(1579484177/5000000000 : ℝ)*X 1 1+(1982813499/10000000000 : ℝ)*X 1 2+(3681504619/5000000000 : ℝ)*X 2 0+(1579484177/5000000000 : ℝ)*X 2 1+(1982813499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1389924793/2500000000 : ℝ)*X 0 0+(337642263/2000000000 : ℝ)*X 0 1+(2722956091/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((545827531/5000000000 : ℝ)*X 1 0+(-5442671433/10000000000 : ℝ)*X 1 1+(742188713/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((6291041911/10000000000 : ℝ)*X 2 0+(5529496023/10000000000 : ℝ)*X 2 1+(28533819/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1509136189/5000000000 : ℝ)*X 0 0+(5529496023/10000000000 : ℝ)*X 0 1+(4436045589/10000000000 : ℝ)*X 0 2+(1509136189/5000000000 : ℝ)*X 1 0+(5529496023/10000000000 : ℝ)*X 1 1+(4436045589/10000000000 : ℝ)*X 1 2+(1509136189/5000000000 : ℝ)*X 2 0+(5529496023/10000000000 : ℝ)*X 2 1+(4436045589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((83321/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(83321/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41753709942137784130041543049479/2340731381071375000000000000000000000 : ℝ) := by norm_num
    linear_combination (211498789809/250000000000 : ℝ)*(base7) + (1148409/1000000000000 : ℝ)*(base50) + (442827/200000000000 : ℝ)*(base59) + (239814503463/125000000000 : ℝ)*(major_s2_0) + (239814503463/125000000000 : ℝ)*(major_s2_1) + (239814503463/125000000000 : ℝ)*(major_s2_2) + (24281/3906250000 : ℝ)*(sp_s2_0) + (1009415747953/500000000000 : ℝ)*(sp_s2_7) + (2018960952851/1000000000000 : ℝ)*(sp_s2_8) + (100949161547/50000000000 : ℝ)*(sp_s2_9) + (2142950887013/1000000000000 : ℝ)*(sp_s2_13) + (72759549/500000000000 : ℝ)*(sp_s2_14) + (2784761/125000000000 : ℝ)*(sp_s2_15) + (4892341/1000000000000 : ℝ)*(sp_s2_27) + (1296960620119/1000000000000 : ℝ)*(f.failure) + (100949161547/50000000000 : ℝ)*(f.sum) + (8690990276198334233/20514286550000000000000000000000 : ℝ)*base63 + (1040629490011/17605468750000000000000000 : ℝ)*base64 + (1991314004885449/2275825000000000000000000000 : ℝ)*base66 + (194453091759/112675000000000000000000000 : ℝ)*base69 + (5262566163976023289/51425996750000000000000000000000 : ℝ)*base70 + (1090863326246789/2282050000000000000000000000 : ℝ)*base73 + (863997554056277/4551650000000000000000000000 : ℝ)*base75 + (32560569344141/114102500000000000000000000 : ℝ)*base76 + (46861610088474809803/103870928825000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (20739/25000000000000000 : ℝ)*base87 + (20739/25000000000000000 : ℝ)*base89 + (20739/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20817/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20817/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (157558335387600632318380473381879/9362925524285500000000000000000000000 : ℝ) := by norm_num
    linear_combination (422911928927/500000000000 : ℝ)*(base7) + (203001/125000000000 : ℝ)*(base40) + (120453/200000000000 : ℝ)*(base59) + (3541292333/500000000000 : ℝ)*(base60) + (1923749644879/1000000000000 : ℝ)*(major_s2_0) + (1923749644879/1000000000000 : ℝ)*(major_s2_1) + (1923749644879/1000000000000 : ℝ)*(major_s2_2) + (4547643/500000000000 : ℝ)*(sp_s2_1) + (436233/62500000000 : ℝ)*(sp_s2_6) + (33814541/200000000000 : ℝ)*(sp_s2_8) + (81040730747/40000000000 : ℝ)*(sp_s2_14) + (506460025171/250000000000 : ℝ)*(sp_s2_15) + (81040730747/40000000000 : ℝ)*(sp_s2_16) + (2146315542899/1000000000000 : ℝ)*(sp_s2_20) + (1300498664773/1000000000000 : ℝ)*(f.failure) + (81040730747/40000000000 : ℝ)*(f.sum) + (7012481021270712123/82057146200000000000000000000000 : ℝ)*base62 + (1156986734847817/2253500000000000000000000000 : ℝ)*base65 + (1922863269092811/9103300000000000000000000000 : ℝ)*base66 + (96125359467803/901400000000000000000000000 : ℝ)*base68 + (53149827216788511761/51425996750000000000000000000000 : ℝ)*base71 + (3158759299255387/4564100000000000000000000000 : ℝ)*base72 + (1291156639620773/4551650000000000000000000000 : ℝ)*base74 + (470634492966493/912820000000000000000000000 : ℝ)*base77 + (86878881716365876741/207741857650000000000000000000000 : ℝ)*base78 + (4687/25000000000000000 : ℝ)*base86 + (4687/25000000000000000 : ℝ)*base88 + (4687/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8859/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8859/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (407464634021794654147868607/51935464412500000000000000000000 : ℝ) := by norm_num
    linear_combination (387947995957/500000000000 : ℝ)*(base5) + (292157881939/1000000000000 : ℝ)*(base7) + (16068861/1000000000000 : ℝ)*(base8) + (1623813/100000000000 : ℝ)*(base16) + (9599734259/125000000000 : ℝ)*(base50) + (803403252451/1000000000000 : ℝ)*(base59) + (662600568567/500000000000 : ℝ)*(major_s2_0) + (662600568567/500000000000 : ℝ)*(major_s2_1) + (662600568567/500000000000 : ℝ)*(major_s2_2) + (933827/1000000000000 : ℝ)*(sp_s2_2) + (1574565651257/1000000000000 : ℝ)*(sp_s2_21) + (393641370497/250000000000 : ℝ)*(sp_s2_22) + (1175238389103/500000000000 : ℝ)*(sp_s2_23) + (41212810317/100000000000 : ℝ)*(sp_s2_27) + (447933106573/500000000000 : ℝ)*(f.failure) + (787290860059/500000000000 : ℝ)*(f.sum) + (5499015351559139059/41028573100000000000000000000000 : ℝ)*base62 + (244032007151/70421875000000000000000000 : ℝ)*base65 + (2768851364131757/4551650000000000000000000000 : ℝ)*base67 + (35469983185081/450700000000000000000000000 : ℝ)*base69 + (7650982555672937497/25712998375000000000000000000000 : ℝ)*base70 + (190505281357579/2282050000000000000000000000 : ℝ)*base73 + (103131266651813/284478125000000000000000000 : ℝ)*base74 + (3661803735881/114102500000000000000000000 : ℝ)*base76 + (19697883642366634491/51935464412500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1113/12500000000000000 : ℝ)*base87 + (1113/12500000000000000 : ℝ)*base89 + (1113/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((45641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4507/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4507/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((83321/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(83321/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20817/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20817/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8859/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8859/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301057_s2 p hpa hpb X hX hprev1

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311058_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:00:32.223504+00:00
-- url     : https://prove2.me/submissions/1615664c-1356-4e6a-9307-09ec987bccd8

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
theorem collision_support_c311058_s1_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3207079281/10000000000 : ℝ)*x 0 + (313088133/1000000000 : ℝ)*x 1 + (-3112164321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3207079281/10000000000 : ℝ)^9 ≤ (11586924710747/50000000000000 : ℝ)^7 := by
    have hnat : (3207079281 : ℕ)^9*50000000000000^7 ≤ 11586924710747^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3207079281 10000000000 11586924710747 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313088133/1000000000 : ℝ)^9 ≤ (4493671771231/20000000000000 : ℝ)^7 := by
    have hnat : (313088133 : ℕ)^9*20000000000000^7 ≤ 4493671771231^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313088133 1000000000 4493671771231 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3112164321/5000000000 : ℝ)^9 ≤ (54357791714349/100000000000000 : ℝ)^7 := by
    have hnat : (3112164321 : ℕ)^9*100000000000000^7 ≤ 54357791714349^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112164321 5000000000 54357791714349 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3207079281/10000000000 : ℝ), (313088133/1000000000 : ℝ), (-3112164321/5000000000 : ℝ)] ![(11586924710747/50000000000000 : ℝ), (4493671771231/20000000000000 : ℝ), (54357791714349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3207079281/10000000000 : ℝ)|^9 ≤ (11586924710747/50000000000000 : ℝ)^7
        have hw : |(-3207079281/10000000000 : ℝ)|=(3207079281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313088133/1000000000 : ℝ)|^9 ≤ (4493671771231/20000000000000 : ℝ)^7
        have hw : |(313088133/1000000000 : ℝ)|=(313088133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3112164321/5000000000 : ℝ)|^9 ≤ (54357791714349/100000000000000 : ℝ)^7
        have hw : |(-3112164321/5000000000 : ℝ)|=(3112164321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3205245499/10000000000 : ℝ)*x 0 + (-62238163/200000000 : ℝ)*x 1 + (-1248283329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3205245499/10000000000 : ℝ)^9 ≤ (5789203575561/25000000000000 : ℝ)^7 := by
    have hnat : (3205245499 : ℕ)^9*25000000000000^7 ≤ 5789203575561^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3205245499 10000000000 5789203575561 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62238163/200000000 : ℝ)^9 ≤ (22293449654211/100000000000000 : ℝ)^7 := by
    have hnat : (62238163 : ℕ)^9*100000000000000^7 ≤ 22293449654211^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62238163 200000000 22293449654211 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248283329/2000000000 : ℝ)^9 ≤ (54549736029527/100000000000000 : ℝ)^7 := by
    have hnat : (1248283329 : ℕ)^9*100000000000000^7 ≤ 54549736029527^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248283329 2000000000 54549736029527 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3205245499/10000000000 : ℝ), (-62238163/200000000 : ℝ), (-1248283329/2000000000 : ℝ)] ![(5789203575561/25000000000000 : ℝ), (22293449654211/100000000000000 : ℝ), (54549736029527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3205245499/10000000000 : ℝ)|^9 ≤ (5789203575561/25000000000000 : ℝ)^7
        have hw : |(3205245499/10000000000 : ℝ)|=(3205245499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62238163/200000000 : ℝ)|^9 ≤ (22293449654211/100000000000000 : ℝ)^7
        have hw : |(-62238163/200000000 : ℝ)|=(62238163/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1248283329/2000000000 : ℝ)|^9 ≤ (54549736029527/100000000000000 : ℝ)^7
        have hw : |(-1248283329/2000000000 : ℝ)|=(1248283329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5862057439/10000000000 : ℝ)*x 0 + (5077772167/10000000000 : ℝ)*x 1 + (1380011939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5862057439/10000000000 : ℝ)^9 ≤ (2516220319659/5000000000000 : ℝ)^7 := by
    have hnat : (5862057439 : ℕ)^9*5000000000000^7 ≤ 2516220319659^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5862057439 10000000000 2516220319659 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077772167/10000000000 : ℝ)^9 ≤ (1307464374293/3125000000000 : ℝ)^7 := by
    have hnat : (5077772167 : ℕ)^9*3125000000000^7 ≤ 1307464374293^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077772167 10000000000 1307464374293 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380011939/10000000000 : ℝ)^9 ≤ (7836733617849/100000000000000 : ℝ)^7 := by
    have hnat : (1380011939 : ℕ)^9*100000000000000^7 ≤ 7836733617849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380011939 10000000000 7836733617849 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5862057439/10000000000 : ℝ), (5077772167/10000000000 : ℝ), (1380011939/10000000000 : ℝ)] ![(2516220319659/5000000000000 : ℝ), (1307464374293/3125000000000 : ℝ), (7836733617849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5862057439/10000000000 : ℝ)|^9 ≤ (2516220319659/5000000000000 : ℝ)^7
        have hw : |(5862057439/10000000000 : ℝ)|=(5862057439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077772167/10000000000 : ℝ)|^9 ≤ (1307464374293/3125000000000 : ℝ)^7
        have hw : |(5077772167/10000000000 : ℝ)|=(5077772167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380011939/10000000000 : ℝ)|^9 ≤ (7836733617849/100000000000000 : ℝ)^7
        have hw : |(1380011939/10000000000 : ℝ)|=(1380011939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-666814933/2500000000 : ℝ)*x 0 + (570370113/2500000000 : ℝ)*x 1 + (-7303044449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666814933/2500000000 : ℝ)^9 ≤ (731381480541/4000000000000 : ℝ)^7 := by
    have hnat : (666814933 : ℕ)^9*4000000000000^7 ≤ 731381480541^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666814933 2500000000 731381480541 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570370113/2500000000 : ℝ)^9 ≤ (186964917733/1250000000000 : ℝ)^7 := by
    have hnat : (570370113 : ℕ)^9*1250000000000^7 ≤ 186964917733^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570370113 2500000000 186964917733 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7303044449/10000000000 : ℝ)^9 ≤ (106813231283/160000000000 : ℝ)^7 := by
    have hnat : (7303044449 : ℕ)^9*160000000000^7 ≤ 106813231283^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7303044449 10000000000 106813231283 160000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-666814933/2500000000 : ℝ), (570370113/2500000000 : ℝ), (-7303044449/10000000000 : ℝ)] ![(731381480541/4000000000000 : ℝ), (186964917733/1250000000000 : ℝ), (106813231283/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-666814933/2500000000 : ℝ)|^9 ≤ (731381480541/4000000000000 : ℝ)^7
        have hw : |(-666814933/2500000000 : ℝ)|=(666814933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(570370113/2500000000 : ℝ)|^9 ≤ (186964917733/1250000000000 : ℝ)^7
        have hw : |(570370113/2500000000 : ℝ)|=(570370113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7303044449/10000000000 : ℝ)|^9 ≤ (106813231283/160000000000 : ℝ)^7
        have hw : |(-7303044449/10000000000 : ℝ)|=(7303044449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (567444561/2000000000 : ℝ)*x 0 + (-224651587/1000000000 : ℝ)*x 1 + (-7199251417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567444561/2000000000 : ℝ)^9 ≤ (4948998146849/25000000000000 : ℝ)^7 := by
    have hnat : (567444561 : ℕ)^9*25000000000000^7 ≤ 4948998146849^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567444561 2000000000 4948998146849 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224651587/1000000000 : ℝ)^9 ≤ (458222605039/3125000000000 : ℝ)^7 := by
    have hnat : (224651587 : ℕ)^9*3125000000000^7 ≤ 458222605039^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224651587 1000000000 458222605039 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7199251417/10000000000 : ℝ)^9 ≤ (13108176807283/20000000000000 : ℝ)^7 := by
    have hnat : (7199251417 : ℕ)^9*20000000000000^7 ≤ 13108176807283^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7199251417 10000000000 13108176807283 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(567444561/2000000000 : ℝ), (-224651587/1000000000 : ℝ), (-7199251417/10000000000 : ℝ)] ![(4948998146849/25000000000000 : ℝ), (458222605039/3125000000000 : ℝ), (13108176807283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(567444561/2000000000 : ℝ)|^9 ≤ (4948998146849/25000000000000 : ℝ)^7
        have hw : |(567444561/2000000000 : ℝ)|=(567444561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224651587/1000000000 : ℝ)|^9 ≤ (458222605039/3125000000000 : ℝ)^7
        have hw : |(-224651587/1000000000 : ℝ)|=(224651587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7199251417/10000000000 : ℝ)|^9 ≤ (13108176807283/20000000000000 : ℝ)^7
        have hw : |(-7199251417/10000000000 : ℝ)|=(7199251417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2494085597/5000000000 : ℝ)*x 0 + (1195266269/2000000000 : ℝ)*x 1 + (1336259251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2494085597/5000000000 : ℝ)^9 ≤ (638938274603/1562500000000 : ℝ)^7 := by
    have hnat : (2494085597 : ℕ)^9*1562500000000^7 ≤ 638938274603^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494085597 5000000000 638938274603 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195266269/2000000000 : ℝ)^9 ≤ (51589207792767/100000000000000 : ℝ)^7 := by
    have hnat : (1195266269 : ℕ)^9*100000000000000^7 ≤ 51589207792767^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195266269 2000000000 51589207792767 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1336259251/10000000000 : ℝ)^9 ≤ (7518742607713/100000000000000 : ℝ)^7 := by
    have hnat : (1336259251 : ℕ)^9*100000000000000^7 ≤ 7518742607713^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336259251 10000000000 7518742607713 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2494085597/5000000000 : ℝ), (1195266269/2000000000 : ℝ), (1336259251/10000000000 : ℝ)] ![(638938274603/1562500000000 : ℝ), (51589207792767/100000000000000 : ℝ), (7518742607713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2494085597/5000000000 : ℝ)|^9 ≤ (638938274603/1562500000000 : ℝ)^7
        have hw : |(2494085597/5000000000 : ℝ)|=(2494085597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195266269/2000000000 : ℝ)|^9 ≤ (51589207792767/100000000000000 : ℝ)^7
        have hw : |(1195266269/2000000000 : ℝ)|=(1195266269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1336259251/10000000000 : ℝ)|^9 ≤ (7518742607713/100000000000000 : ℝ)^7
        have hw : |(1336259251/10000000000 : ℝ)|=(1336259251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (791012203/2500000000 : ℝ)*x 0 + (327159261/400000000 : ℝ)*x 1 + (-356047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (791012203/2500000000 : ℝ)^9 ≤ (11387424609779/50000000000000 : ℝ)^7 := by
    have hnat : (791012203 : ℕ)^9*50000000000000^7 ≤ 11387424609779^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791012203 2500000000 11387424609779 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327159261/400000000 : ℝ)^9 ≤ (1930617141707/2500000000000 : ℝ)^7 := by
    have hnat : (327159261 : ℕ)^9*2500000000000^7 ≤ 1930617141707^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327159261 400000000 1930617141707 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356047/5000000000 : ℝ)^9 ≤ (465101769/100000000000000 : ℝ)^7 := by
    have hnat : (356047 : ℕ)^9*100000000000000^7 ≤ 465101769^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356047 5000000000 465101769 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(791012203/2500000000 : ℝ), (327159261/400000000 : ℝ), (-356047/5000000000 : ℝ)] ![(11387424609779/50000000000000 : ℝ), (1930617141707/2500000000000 : ℝ), (465101769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(791012203/2500000000 : ℝ)|^9 ≤ (11387424609779/50000000000000 : ℝ)^7
        have hw : |(791012203/2500000000 : ℝ)|=(791012203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327159261/400000000 : ℝ)|^9 ≤ (1930617141707/2500000000000 : ℝ)^7
        have hw : |(327159261/400000000 : ℝ)|=(327159261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356047/5000000000 : ℝ)|^9 ≤ (465101769/100000000000000 : ℝ)^7
        have hw : |(-356047/5000000000 : ℝ)|=(356047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2629549761/10000000000 : ℝ)*x 0 + (2823126511/10000000000 : ℝ)*x 1 + (-3463757417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629549761/10000000000 : ℝ)^9 ≤ (4488210621379/25000000000000 : ℝ)^7 := by
    have hnat : (2629549761 : ℕ)^9*25000000000000^7 ≤ 4488210621379^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629549761 10000000000 4488210621379 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2823126511/10000000000 : ℝ)^9 ≤ (4917407061537/25000000000000 : ℝ)^7 := by
    have hnat : (2823126511 : ℕ)^9*25000000000000^7 ≤ 4917407061537^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823126511 10000000000 4917407061537 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3463757417/5000000000 : ℝ)^9 ≤ (779719115647/1250000000000 : ℝ)^7 := by
    have hnat : (3463757417 : ℕ)^9*1250000000000^7 ≤ 779719115647^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3463757417 5000000000 779719115647 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2629549761/10000000000 : ℝ), (2823126511/10000000000 : ℝ), (-3463757417/5000000000 : ℝ)] ![(4488210621379/25000000000000 : ℝ), (4917407061537/25000000000000 : ℝ), (779719115647/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2629549761/10000000000 : ℝ)|^9 ≤ (4488210621379/25000000000000 : ℝ)^7
        have hw : |(-2629549761/10000000000 : ℝ)|=(2629549761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2823126511/10000000000 : ℝ)|^9 ≤ (4917407061537/25000000000000 : ℝ)^7
        have hw : |(2823126511/10000000000 : ℝ)|=(2823126511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3463757417/5000000000 : ℝ)|^9 ≤ (779719115647/1250000000000 : ℝ)^7
        have hw : |(-3463757417/5000000000 : ℝ)|=(3463757417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2674671697/10000000000 : ℝ)*x 0 + (-2905435567/10000000000 : ℝ)*x 1 + (-341453287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674671697/10000000000 : ℝ)^9 ≤ (4587472624483/25000000000000 : ℝ)^7 := by
    have hnat : (2674671697 : ℕ)^9*25000000000000^7 ≤ 4587472624483^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674671697 10000000000 4587472624483 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2905435567/10000000000 : ℝ)^9 ≤ (5102500343941/25000000000000 : ℝ)^7 := by
    have hnat : (2905435567 : ℕ)^9*25000000000000^7 ≤ 5102500343941^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905435567 10000000000 5102500343941 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341453287/500000000 : ℝ)^9 ≤ (30620054058213/50000000000000 : ℝ)^7 := by
    have hnat : (341453287 : ℕ)^9*50000000000000^7 ≤ 30620054058213^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341453287 500000000 30620054058213 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674671697/10000000000 : ℝ), (-2905435567/10000000000 : ℝ), (-341453287/500000000 : ℝ)] ![(4587472624483/25000000000000 : ℝ), (5102500343941/25000000000000 : ℝ), (30620054058213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674671697/10000000000 : ℝ)|^9 ≤ (4587472624483/25000000000000 : ℝ)^7
        have hw : |(2674671697/10000000000 : ℝ)|=(2674671697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2905435567/10000000000 : ℝ)|^9 ≤ (5102500343941/25000000000000 : ℝ)^7
        have hw : |(-2905435567/10000000000 : ℝ)|=(2905435567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341453287/500000000 : ℝ)|^9 ≤ (30620054058213/50000000000000 : ℝ)^7
        have hw : |(-341453287/500000000 : ℝ)|=(341453287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6341347557/10000000000 : ℝ)*x 0 + (4929028887/10000000000 : ℝ)*x 1 + (206665691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6341347557/10000000000 : ℝ)^9 ≤ (6959403455497/12500000000000 : ℝ)^7 := by
    have hnat : (6341347557 : ℕ)^9*12500000000000^7 ≤ 6959403455497^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6341347557 10000000000 6959403455497 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4929028887/10000000000 : ℝ)^9 ≤ (8053949301229/20000000000000 : ℝ)^7 := by
    have hnat : (4929028887 : ℕ)^9*20000000000000^7 ≤ 8053949301229^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929028887 10000000000 8053949301229 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206665691/2500000000 : ℝ)^9 ≤ (2027512920073/50000000000000 : ℝ)^7 := by
    have hnat : (206665691 : ℕ)^9*50000000000000^7 ≤ 2027512920073^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206665691 2500000000 2027512920073 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6341347557/10000000000 : ℝ), (4929028887/10000000000 : ℝ), (206665691/2500000000 : ℝ)] ![(6959403455497/12500000000000 : ℝ), (8053949301229/20000000000000 : ℝ), (2027512920073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6341347557/10000000000 : ℝ)|^9 ≤ (6959403455497/12500000000000 : ℝ)^7
        have hw : |(6341347557/10000000000 : ℝ)|=(6341347557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4929028887/10000000000 : ℝ)|^9 ≤ (8053949301229/20000000000000 : ℝ)^7
        have hw : |(4929028887/10000000000 : ℝ)|=(4929028887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206665691/2500000000 : ℝ)|^9 ≤ (2027512920073/50000000000000 : ℝ)^7
        have hw : |(206665691/2500000000 : ℝ)|=(206665691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3244042279/10000000000 : ℝ)*x 0 + (1596283561/5000000000 : ℝ)*x 1 + (-1228541959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3244042279/10000000000 : ℝ)^9 ≤ (23517813165457/100000000000000 : ℝ)^7 := by
    have hnat : (3244042279 : ℕ)^9*100000000000000^7 ≤ 23517813165457^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3244042279 10000000000 23517813165457 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596283561/5000000000 : ℝ)^9 ≤ (23039113360931/100000000000000 : ℝ)^7 := by
    have hnat : (1596283561 : ℕ)^9*100000000000000^7 ≤ 23039113360931^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596283561 5000000000 23039113360931 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228541959/2000000000 : ℝ)^9 ≤ (53443073466923/100000000000000 : ℝ)^7 := by
    have hnat : (1228541959 : ℕ)^9*100000000000000^7 ≤ 53443073466923^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228541959 2000000000 53443073466923 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3244042279/10000000000 : ℝ), (1596283561/5000000000 : ℝ), (-1228541959/2000000000 : ℝ)] ![(23517813165457/100000000000000 : ℝ), (23039113360931/100000000000000 : ℝ), (53443073466923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3244042279/10000000000 : ℝ)|^9 ≤ (23517813165457/100000000000000 : ℝ)^7
        have hw : |(-3244042279/10000000000 : ℝ)|=(3244042279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1596283561/5000000000 : ℝ)|^9 ≤ (23039113360931/100000000000000 : ℝ)^7
        have hw : |(1596283561/5000000000 : ℝ)|=(1596283561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1228541959/2000000000 : ℝ)|^9 ≤ (53443073466923/100000000000000 : ℝ)^7
        have hw : |(-1228541959/2000000000 : ℝ)|=(1228541959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3336640351/10000000000 : ℝ)*x 0 + (-1607063099/5000000000 : ℝ)*x 1 + (-6047126447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3336640351/10000000000 : ℝ)^9 ≤ (24384400488799/100000000000000 : ℝ)^7 := by
    have hnat : (3336640351 : ℕ)^9*100000000000000^7 ≤ 24384400488799^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3336640351 10000000000 24384400488799 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1607063099/5000000000 : ℝ)^9 ≤ (11619669209531/50000000000000 : ℝ)^7 := by
    have hnat : (1607063099 : ℕ)^9*50000000000000^7 ≤ 11619669209531^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607063099 5000000000 11619669209531 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6047126447/10000000000 : ℝ)^9 ≤ (26188130539823/50000000000000 : ℝ)^7 := by
    have hnat : (6047126447 : ℕ)^9*50000000000000^7 ≤ 26188130539823^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6047126447 10000000000 26188130539823 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3336640351/10000000000 : ℝ), (-1607063099/5000000000 : ℝ), (-6047126447/10000000000 : ℝ)] ![(24384400488799/100000000000000 : ℝ), (11619669209531/50000000000000 : ℝ), (26188130539823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3336640351/10000000000 : ℝ)|^9 ≤ (24384400488799/100000000000000 : ℝ)^7
        have hw : |(3336640351/10000000000 : ℝ)|=(3336640351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1607063099/5000000000 : ℝ)|^9 ≤ (11619669209531/50000000000000 : ℝ)^7
        have hw : |(-1607063099/5000000000 : ℝ)|=(1607063099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6047126447/10000000000 : ℝ)|^9 ≤ (26188130539823/50000000000000 : ℝ)^7
        have hw : |(-6047126447/10000000000 : ℝ)|=(6047126447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1706725971/2500000000 : ℝ)*x 0 + (2062161507/5000000000 : ℝ)*x 1 + (615248973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706725971/2500000000 : ℝ)^9 ≤ (61215183628483/100000000000000 : ℝ)^7 := by
    have hnat : (1706725971 : ℕ)^9*100000000000000^7 ≤ 61215183628483^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706725971 2500000000 61215183628483 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062161507/5000000000 : ℝ)^9 ≤ (32022367319187/100000000000000 : ℝ)^7 := by
    have hnat : (2062161507 : ℕ)^9*100000000000000^7 ≤ 32022367319187^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062161507 5000000000 32022367319187 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615248973/5000000000 : ℝ)^9 ≤ (3381224520073/50000000000000 : ℝ)^7 := by
    have hnat : (615248973 : ℕ)^9*50000000000000^7 ≤ 3381224520073^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615248973 5000000000 3381224520073 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1706725971/2500000000 : ℝ), (2062161507/5000000000 : ℝ), (615248973/5000000000 : ℝ)] ![(61215183628483/100000000000000 : ℝ), (32022367319187/100000000000000 : ℝ), (3381224520073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1706725971/2500000000 : ℝ)|^9 ≤ (61215183628483/100000000000000 : ℝ)^7
        have hw : |(1706725971/2500000000 : ℝ)|=(1706725971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062161507/5000000000 : ℝ)|^9 ≤ (32022367319187/100000000000000 : ℝ)^7
        have hw : |(2062161507/5000000000 : ℝ)|=(2062161507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615248973/5000000000 : ℝ)|^9 ≤ (3381224520073/50000000000000 : ℝ)^7
        have hw : |(615248973/5000000000 : ℝ)|=(615248973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311058_s1_s1_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2515597841/10000000000 : ℝ)*x 0 + (8654187317/10000000000 : ℝ)*x 1 + (-732423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2515597841/10000000000 : ℝ)^9 ≤ (3391765679723/20000000000000 : ℝ)^7 := by
    have hnat : (2515597841 : ℕ)^9*20000000000000^7 ≤ 3391765679723^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515597841 10000000000 3391765679723 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8654187317/10000000000 : ℝ)^9 ≤ (41520344673067/50000000000000 : ℝ)^7 := by
    have hnat : (8654187317 : ℕ)^9*50000000000000^7 ≤ 41520344673067^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8654187317 10000000000 41520344673067 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732423/10000000000 : ℝ)^9 ≤ (120560601/25000000000000 : ℝ)^7 := by
    have hnat : (732423 : ℕ)^9*25000000000000^7 ≤ 120560601^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732423 10000000000 120560601 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2515597841/10000000000 : ℝ), (8654187317/10000000000 : ℝ), (-732423/10000000000 : ℝ)] ![(3391765679723/20000000000000 : ℝ), (41520344673067/50000000000000 : ℝ), (120560601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2515597841/10000000000 : ℝ)|^9 ≤ (3391765679723/20000000000000 : ℝ)^7
        have hw : |(2515597841/10000000000 : ℝ)|=(2515597841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8654187317/10000000000 : ℝ)|^9 ≤ (41520344673067/50000000000000 : ℝ)^7
        have hw : |(8654187317/10000000000 : ℝ)|=(8654187317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-732423/10000000000 : ℝ)|^9 ≤ (120560601/25000000000000 : ℝ)^7
        have hw : |(-732423/10000000000 : ℝ)|=(732423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311058_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((8813/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8813/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8159/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8159/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-74123/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-74123/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8447/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8447/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59047/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-33431/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-33431/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
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
  have s1_pow0 : (8813/10000 : ℝ) ^ (71/16 : ℝ) ≤ (891880679246094707/1562500000000000000 : ℝ) := by
    have hpowers : (8813/10000 : ℝ)^71 ≤ (891880679246094707/1562500000000000000 : ℝ)^16 := by
      have hnat : (8813 : ℕ)^71*1562500000000000000^16 ≤ 891880679246094707^16*10000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8813 10000 891880679246094707 1562500000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8813/10000 : ℝ)) (X := (891880679246094707/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2454380679246094707/1562500000000000000 : ℝ) ≤ (86494106023533/78125000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2454380679246094707/1562500000000000000 : ℝ)^16 ≤ (86494106023533/78125000000000 : ℝ)^71 := by
      have hnat : (2454380679246094707 : ℕ)^16*78125000000000^71 ≤ 86494106023533^71*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2454380679246094707 1562500000000000000 86494106023533 78125000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (86494106023533/78125000000000 : ℝ)) (X := (2454380679246094707/1562500000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1673130679246094707/781250000000000000 : ℝ) ≤ (11872246904752499/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1673130679246094707/781250000000000000 : ℝ)^16 ≤ (11872246904752499/10000000000000000 : ℝ)^71 := by
      have hnat : (1673130679246094707 : ℕ)^16*10000000000000000^71 ≤ 11872246904752499^71*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1673130679246094707 781250000000000000 11872246904752499 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11872246904752499/10000000000000000 : ℝ)) (X := (1673130679246094707/781250000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8369106023533/68851562500000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(32040053349611/352520000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (8813/10000 : ℝ)) (alpha := (8369106023533/68851562500000 : ℝ)) (beta := (32040053349611/352520000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8813/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8369106023533/68851562500000 : ℝ)*((1 : ℝ)*pair X 0 1)+(32040053349611/352520000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8159/10000 : ℝ) ^ (71/16 : ℝ) ≤ (40540480403274510377/100000000000000000000 : ℝ) := by
    have hpowers : (8159/10000 : ℝ)^71 ≤ (40540480403274510377/100000000000000000000 : ℝ)^16 := by
      have hnat : (8159 : ℕ)^71*100000000000000000000^16 ≤ 40540480403274510377^16*10000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8159 10000 40540480403274510377 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8159/10000 : ℝ)) (X := (40540480403274510377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (140540480403274510377/100000000000000000000 : ℝ) ≤ (5398553003634927/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (140540480403274510377/100000000000000000000 : ℝ)^16 ≤ (5398553003634927/5000000000000000 : ℝ)^71 := by
      have hnat : (140540480403274510377 : ℕ)^16*5000000000000000^71 ≤ 5398553003634927^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140540480403274510377 100000000000000000000 5398553003634927 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5398553003634927/5000000000000000 : ℝ)) (X := (140540480403274510377/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (90540480403274510377/50000000000000000000 : ℝ) ≤ (2286347155747003/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (90540480403274510377/50000000000000000000 : ℝ)^16 ≤ (2286347155747003/2000000000000000 : ℝ)^71 := by
      have hnat : (90540480403274510377 : ℕ)^16*2000000000000000^71 ≤ 2286347155747003^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90540480403274510377 50000000000000000000 2286347155747003 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2286347155747003/2000000000000000 : ℝ)) (X := (90540480403274510377/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(398553003634927/4079500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(634629771465161/8159000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (8159/10000 : ℝ)) (alpha := (398553003634927/4079500000000000 : ℝ)) (beta := (634629771465161/8159000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8159/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(398553003634927/4079500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(634629771465161/8159000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (74123/100000 : ℝ) ^ (71/16 : ℝ) ≤ (13239951371482346151/50000000000000000000 : ℝ) := by
    have hpowers : (74123/100000 : ℝ)^71 ≤ (13239951371482346151/50000000000000000000 : ℝ)^16 := by
      have hnat : (74123 : ℕ)^71*50000000000000000000^16 ≤ 13239951371482346151^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74123 100000 13239951371482346151 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74123/100000 : ℝ)) (X := (13239951371482346151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (63239951371482346151/50000000000000000000 : ℝ) ≤ (10543644775502447/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (63239951371482346151/50000000000000000000 : ℝ)^16 ≤ (10543644775502447/10000000000000000 : ℝ)^71 := by
      have hnat : (63239951371482346151 : ℕ)^16*10000000000000000^71 ≤ 10543644775502447^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63239951371482346151 50000000000000000000 10543644775502447 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10543644775502447/10000000000000000 : ℝ)) (X := (63239951371482346151/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (38239951371482346151/25000000000000000000 : ℝ) ≤ (11005122715032967/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (38239951371482346151/25000000000000000000 : ℝ)^16 ≤ (11005122715032967/10000000000000000 : ℝ)^71 := by
      have hnat : (38239951371482346151 : ℕ)^16*10000000000000000^71 ≤ 11005122715032967^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38239951371482346151 25000000000000000000 11005122715032967 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11005122715032967/10000000000000000 : ℝ)) (X := (38239951371482346151/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(543644775502447/7412300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(11536948488263/185307500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (74123/100000 : ℝ)) (alpha := (543644775502447/7412300000000000 : ℝ)) (beta := (11536948488263/185307500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (74123/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(543644775502447/7412300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(11536948488263/185307500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3207079281/10000000000 : ℝ)*X 0 0+(313088133/1000000000 : ℝ)*X 0 1+(-3112164321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3205245499/10000000000 : ℝ)*X 1 0+(-62238163/200000000 : ℝ)*X 1 1+(-1248283329/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5862057439/10000000000 : ℝ)*X 2 0+(5077772167/10000000000 : ℝ)*X 2 1+(1380011939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-666814933/2500000000 : ℝ)*X 0 0+(570370113/2500000000 : ℝ)*X 0 1+(-7303044449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((567444561/2000000000 : ℝ)*X 1 0+(-224651587/1000000000 : ℝ)*X 1 1+(-7199251417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2494085597/5000000000 : ℝ)*X 2 0+(1195266269/2000000000 : ℝ)*X 2 1+(1336259251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((791012203/2500000000 : ℝ)*X 0 0+(327159261/400000000 : ℝ)*X 0 1+(-356047/5000000000 : ℝ)*X 0 2+(791012203/2500000000 : ℝ)*X 1 0+(327159261/400000000 : ℝ)*X 1 1+(-356047/5000000000 : ℝ)*X 1 2+(791012203/2500000000 : ℝ)*X 2 0+(327159261/400000000 : ℝ)*X 2 1+(-356047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2629549761/10000000000 : ℝ)*X 0 0+(2823126511/10000000000 : ℝ)*X 0 1+(-3463757417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2674671697/10000000000 : ℝ)*X 1 0+(-2905435567/10000000000 : ℝ)*X 1 1+(-341453287/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6341347557/10000000000 : ℝ)*X 2 0+(4929028887/10000000000 : ℝ)*X 2 1+(206665691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-3244042279/10000000000 : ℝ)*X 0 0+(1596283561/5000000000 : ℝ)*X 0 1+(-1228541959/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3336640351/10000000000 : ℝ)*X 1 0+(-1607063099/5000000000 : ℝ)*X 1 1+(-6047126447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1706725971/2500000000 : ℝ)*X 2 0+(2062161507/5000000000 : ℝ)*X 2 1+(615248973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2515597841/10000000000 : ℝ)*X 0 0+(8654187317/10000000000 : ℝ)*X 0 1+(-732423/10000000000 : ℝ)*X 0 2+(2515597841/10000000000 : ℝ)*X 1 0+(8654187317/10000000000 : ℝ)*X 1 1+(-732423/10000000000 : ℝ)*X 1 2+(2515597841/10000000000 : ℝ)*X 2 0+(8654187317/10000000000 : ℝ)*X 2 1+(-732423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311058_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((8447/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8447/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (269238208324461497575820876373/19035121806575000000000000000000000 : ℝ) := by norm_num
    linear_combination (175356918667/250000000000 : ℝ)*(base7) + (163947676493/500000000000 : ℝ)*(base60) + (163030324127/50000000000 : ℝ)*(major_s1_0) + (163030324127/50000000000 : ℝ)*(major_s1_1) + (163030324127/50000000000 : ℝ)*(major_s1_2) + (662053/40000000000 : ℝ)*(sp_s1_2) + (4117096376373/1000000000000 : ℝ)*(sp_s1_7) + (1029277787481/250000000000 : ℝ)*(sp_s1_8) + (4117157415837/1000000000000 : ℝ)*(sp_s1_9) + (537075133359/200000000000 : ℝ)*(sp_s1_13) + (45044379/500000000000 : ℝ)*(sp_s1_14) + (75315207/1000000000000 : ℝ)*(sp_s1_15) + (12497969/1000000000000 : ℝ)*(sp_s1_16) + (3363161/200000000000 : ℝ)*(sp_s1_27) + (495991201983/250000000000 : ℝ)*(f.failure) + (4117186465131/1000000000000 : ℝ)*(f.sum) + (15410908488123987889/30238477850000000000000000000000 : ℝ)*base63 + (272465739491159/370615000000000000000000000 : ℝ)*base65 + (69143778404823/407950000000000000000000000 : ℝ)*base66 + (427208765989/592984000000000000000000 : ℝ)*base69 + (330982032925376691/666577550000000000000000000000 : ℝ)*base71 + (7221284367543/44065000000000000000000000 : ℝ)*base72 + (103277140074313/407950000000000000000000000 : ℝ)*base75 + (63284822289753/440650000000000000000000000 : ℝ)*base77 + (75034516644834931/3595263350000000000000000000000 : ℝ)*base79 + (521/6250000000000000 : ℝ)*base87 + (521/6250000000000000 : ℝ)*base89 + (521/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59047/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2090890866839845511896402546989/95175609032875000000000000000000000 : ℝ) := by norm_num
    linear_combination (3614717175519/1000000000000 : ℝ)*(base5) + (256605224387/500000000000 : ℝ)*(base7) + (2908460206093/1000000000000 : ℝ)*(base60) + (637158034409/125000000000 : ℝ)*(major_s1_0) + (637158034409/125000000000 : ℝ)*(major_s1_1) + (637158034409/125000000000 : ℝ)*(major_s1_2) + (13951/2500000000 : ℝ)*(sp_s1_0) + (47398599/500000000000 : ℝ)*(sp_s1_1) + (617031/62500000000 : ℝ)*(sp_s1_2) + (30651951/200000000000 : ℝ)*(sp_s1_8) + (6785667711119/1000000000000 : ℝ)*(sp_s1_14) + (3392712617283/500000000000 : ℝ)*(sp_s1_15) + (81252856823/7812500000 : ℝ)*(sp_s1_16) + (7460599/500000000000 : ℝ)*(sp_s1_23) + (1550753363373/500000000000 : ℝ)*(f.failure) + (6785673291519/1000000000000 : ℝ)*(f.sum) + (74659477168943666291/151192389250000000000000000000000 : ℝ)*base63 + (258815780803637/741230000000000000000000000 : ℝ)*base65 + (64739918108137/509937500000000000000000000 : ℝ)*base67 + (1319173595581123/3706150000000000000000000000 : ℝ)*base69 + (200154922853394833/416610968750000000000000000000 : ℝ)*base71 + (10291299298803/88130000000000000000000000 : ℝ)*base73 + (25205574940293/509937500000000000000000000 : ℝ)*base75 + (35009840232083/550812500000000000000000000 : ℝ)*base77 + (10083163447907289/1123519796875000000000000000000 : ℝ)*base79 + (6451/12500000000000000 : ℝ)*base87 + (6451/12500000000000000 : ℝ)*base89 + (6451/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-33431/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-33431/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21407208339085072982909103/3332887750000000000000000000000 : ℝ) := by norm_num
    linear_combination (142461097027/1000000000000 : ℝ)*(base7) + (23349/1000000000000 : ℝ)*(base15) + (2009/31250000000 : ℝ)*(base44) + (286397179583/1000000000000 : ℝ)*(base60) + (4183117031849/1000000000000 : ℝ)*(major_s1_0) + (4183116967561/1000000000000 : ℝ)*(major_s1_1) + (4183117031849/1000000000000 : ℝ)*(major_s1_2) + (92864223/1000000000000 : ℝ)*(sp_s1_2) + (88215481/500000000000 : ℝ)*(sp_s1_13) + (33403249/1000000000000 : ℝ)*(sp_s1_16) + (5735637513467/1000000000000 : ℝ)*(sp_s1_21) + (5735637425829/1000000000000 : ℝ)*(sp_s1_22) + (1147102249199/200000000000 : ℝ)*(sp_s1_23) + (1343782379213/500000000000 : ℝ)*(sp_s1_27) + (318160019581/125000000000 : ℝ)*(f.failure) + (5735637513467/1000000000000 : ℝ)*(f.sum) + (3998737641154586111/21598912750000000000000000000000 : ℝ)*base62 + (1531902695071/10589000000000000000000000 : ℝ)*base64 + (2071302791290779/8159000000000000000000000000 : ℝ)*base66 + (575826250713861/1058900000000000000000000000 : ℝ)*base69 + (1144504362896843931/1666443875000000000000000000000 : ℝ)*base70 + (31539796539519/50360000000000000000000000 : ℝ)*base72 + (420367279842047/4079500000000000000000000000 : ℝ)*base75 + (7183790820029/157375000000000000000000000 : ℝ)*base76 + (327244259658129757/5136090500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1789/1562500000000000 : ℝ)*base86 + (1789/1562500000000000 : ℝ)*base88 + (1789/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((8813/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8813/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8159/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8159/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-74123/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-74123/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8447/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8447/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59047/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-33431/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-33431/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311058_s1 p hpa hpb X hX hprev0

#print axioms solution

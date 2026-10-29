-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316048_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:05:55.382714+00:00
-- url     : https://prove2.me/submissions/4a8bc163-5859-4fa6-9cfd-ff07220a0d9f

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
theorem collision_support_c316048_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2900134443/10000000000 : ℝ)*x 0 + (579840881/2000000000 : ℝ)*x 1 + (-323689671/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2900134443/10000000000 : ℝ)^39 ≤ (10535552865449/50000000000000 : ℝ)^31 := by
    have hnat : (2900134443 : ℕ)^39*50000000000000^31 ≤ 10535552865449^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900134443 10000000000 10535552865449 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579840881/2000000000 : ℝ)^39 ≤ (21062605028163/100000000000000 : ℝ)^31 := by
    have hnat : (579840881 : ℕ)^39*100000000000000^31 ≤ 21062605028163^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579840881 2000000000 21062605028163 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323689671/500000000 : ℝ)^39 ≤ (2314651569529/4000000000000 : ℝ)^31 := by
    have hnat : (323689671 : ℕ)^39*4000000000000^31 ≤ 2314651569529^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323689671 500000000 2314651569529 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2900134443/10000000000 : ℝ), (579840881/2000000000 : ℝ), (-323689671/500000000 : ℝ)] ![(10535552865449/50000000000000 : ℝ), (21062605028163/100000000000000 : ℝ), (2314651569529/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2900134443/10000000000 : ℝ)|^39 ≤ (10535552865449/50000000000000 : ℝ)^31
        have hw : |(-2900134443/10000000000 : ℝ)|=(2900134443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(579840881/2000000000 : ℝ)|^39 ≤ (21062605028163/100000000000000 : ℝ)^31
        have hw : |(579840881/2000000000 : ℝ)|=(579840881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323689671/500000000 : ℝ)|^39 ≤ (2314651569529/4000000000000 : ℝ)^31
        have hw : |(-323689671/500000000 : ℝ)|=(323689671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (730266579/2000000000 : ℝ)*x 0 + (-3650161957/10000000000 : ℝ)*x 1 + (-1294791717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730266579/2000000000 : ℝ)^39 ≤ (703842809743/2500000000000 : ℝ)^31 := by
    have hnat : (730266579 : ℕ)^39*2500000000000^31 ≤ 703842809743^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730266579 2000000000 703842809743 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3650161957/10000000000 : ℝ)^39 ≤ (5628470871581/20000000000000 : ℝ)^31 := by
    have hnat : (3650161957 : ℕ)^39*20000000000000^31 ≤ 5628470871581^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650161957 10000000000 5628470871581 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294791717/2500000000 : ℝ)^39 ≤ (21851966622591/50000000000000 : ℝ)^31 := by
    have hnat : (1294791717 : ℕ)^39*50000000000000^31 ≤ 21851966622591^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294791717 2500000000 21851966622591 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(730266579/2000000000 : ℝ), (-3650161957/10000000000 : ℝ), (-1294791717/2500000000 : ℝ)] ![(703842809743/2500000000000 : ℝ), (5628470871581/20000000000000 : ℝ), (21851966622591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(730266579/2000000000 : ℝ)|^39 ≤ (703842809743/2500000000000 : ℝ)^31
        have hw : |(730266579/2000000000 : ℝ)|=(730266579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3650161957/10000000000 : ℝ)|^39 ≤ (5628470871581/20000000000000 : ℝ)^31
        have hw : |(-3650161957/10000000000 : ℝ)|=(3650161957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1294791717/2500000000 : ℝ)|^39 ≤ (21851966622591/50000000000000 : ℝ)^31
        have hw : |(-1294791717/2500000000 : ℝ)|=(1294791717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (335263353/625000000 : ℝ)*x 0 + (5365742409/10000000000 : ℝ)*x 1 + (285265671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335263353/625000000 : ℝ)^39 ≤ (11419344880149/25000000000000 : ℝ)^31 := by
    have hnat : (335263353 : ℕ)^39*25000000000000^31 ≤ 11419344880149^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335263353 625000000 11419344880149 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5365742409/10000000000 : ℝ)^39 ≤ (22846878623111/50000000000000 : ℝ)^31 := by
    have hnat : (5365742409 : ℕ)^39*50000000000000^31 ≤ 22846878623111^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365742409 10000000000 22846878623111 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285265671/2000000000 : ℝ)^39 ≤ (8628863214581/100000000000000 : ℝ)^31 := by
    have hnat : (285265671 : ℕ)^39*100000000000000^31 ≤ 8628863214581^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285265671 2000000000 8628863214581 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335263353/625000000 : ℝ), (5365742409/10000000000 : ℝ), (285265671/2000000000 : ℝ)] ![(11419344880149/25000000000000 : ℝ), (22846878623111/50000000000000 : ℝ), (8628863214581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335263353/625000000 : ℝ)|^39 ≤ (11419344880149/25000000000000 : ℝ)^31
        have hw : |(335263353/625000000 : ℝ)|=(335263353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5365742409/10000000000 : ℝ)|^39 ≤ (22846878623111/50000000000000 : ℝ)^31
        have hw : |(5365742409/10000000000 : ℝ)|=(5365742409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285265671/2000000000 : ℝ)|^39 ≤ (8628863214581/100000000000000 : ℝ)^31
        have hw : |(285265671/2000000000 : ℝ)|=(285265671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5097115561/10000000000 : ℝ)*x 0 + (25492841/50000000 : ℝ)*x 1 + (-2132898363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5097115561/10000000000 : ℝ)^39 ≤ (21417329479931/50000000000000 : ℝ)^31 := by
    have hnat : (5097115561 : ℕ)^39*50000000000000^31 ≤ 21417329479931^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097115561 10000000000 21417329479931 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25492841/50000000 : ℝ)^39 ≤ (42850017410827/100000000000000 : ℝ)^31 := by
    have hnat : (25492841 : ℕ)^39*100000000000000^31 ≤ 42850017410827^31*50000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25492841 50000000 42850017410827 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132898363/10000000000 : ℝ)^39 ≤ (223676931469/1562500000000 : ℝ)^31 := by
    have hnat : (2132898363 : ℕ)^39*1562500000000^31 ≤ 223676931469^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132898363 10000000000 223676931469 1562500000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5097115561/10000000000 : ℝ), (25492841/50000000 : ℝ), (-2132898363/10000000000 : ℝ)] ![(21417329479931/50000000000000 : ℝ), (42850017410827/100000000000000 : ℝ), (223676931469/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5097115561/10000000000 : ℝ)|^39 ≤ (21417329479931/50000000000000 : ℝ)^31
        have hw : |(5097115561/10000000000 : ℝ)|=(5097115561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25492841/50000000 : ℝ)|^39 ≤ (42850017410827/100000000000000 : ℝ)^31
        have hw : |(25492841/50000000 : ℝ)|=(25492841/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132898363/10000000000 : ℝ)|^39 ≤ (223676931469/1562500000000 : ℝ)^31
        have hw : |(-2132898363/10000000000 : ℝ)|=(2132898363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2850441093/10000000000 : ℝ)*x 0 + (21470597/80000000 : ℝ)*x 1 + (-6686545141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2850441093/10000000000 : ℝ)^39 ≤ (20617889964909/100000000000000 : ℝ)^31 := by
    have hnat : (2850441093 : ℕ)^39*100000000000000^31 ≤ 20617889964909^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850441093 10000000000 20617889964909 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21470597/80000000 : ℝ)^39 ≤ (4778326856387/25000000000000 : ℝ)^31 := by
    have hnat : (21470597 : ℕ)^39*25000000000000^31 ≤ 4778326856387^31*80000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21470597 80000000 4778326856387 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6686545141/10000000000 : ℝ)^39 ≤ (12053760517429/20000000000000 : ℝ)^31 := by
    have hnat : (6686545141 : ℕ)^39*20000000000000^31 ≤ 12053760517429^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6686545141 10000000000 12053760517429 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2850441093/10000000000 : ℝ), (21470597/80000000 : ℝ), (-6686545141/10000000000 : ℝ)] ![(20617889964909/100000000000000 : ℝ), (4778326856387/25000000000000 : ℝ), (12053760517429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2850441093/10000000000 : ℝ)|^39 ≤ (20617889964909/100000000000000 : ℝ)^31
        have hw : |(-2850441093/10000000000 : ℝ)|=(2850441093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21470597/80000000 : ℝ)|^39 ≤ (4778326856387/25000000000000 : ℝ)^31
        have hw : |(21470597/80000000 : ℝ)|=(21470597/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6686545141/10000000000 : ℝ)|^39 ≤ (12053760517429/20000000000000 : ℝ)^31
        have hw : |(-6686545141/10000000000 : ℝ)|=(6686545141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (445884559/1250000000 : ℝ)*x 0 + (-3358570609/10000000000 : ℝ)*x 1 + (-689593147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445884559/1250000000 : ℝ)^39 ≤ (5467768729559/20000000000000 : ℝ)^31 := by
    have hnat : (445884559 : ℕ)^39*20000000000000^31 ≤ 5467768729559^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445884559 1250000000 5467768729559 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3358570609/10000000000 : ℝ)^39 ≤ (5068760424879/20000000000000 : ℝ)^31 := by
    have hnat : (3358570609 : ℕ)^39*20000000000000^31 ≤ 5068760424879^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3358570609 10000000000 5068760424879 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689593147/1250000000 : ℝ)^39 ≤ (2365867710427/5000000000000 : ℝ)^31 := by
    have hnat : (689593147 : ℕ)^39*5000000000000^31 ≤ 2365867710427^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689593147 1250000000 2365867710427 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445884559/1250000000 : ℝ), (-3358570609/10000000000 : ℝ), (-689593147/1250000000 : ℝ)] ![(5467768729559/20000000000000 : ℝ), (5068760424879/20000000000000 : ℝ), (2365867710427/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445884559/1250000000 : ℝ)|^39 ≤ (5467768729559/20000000000000 : ℝ)^31
        have hw : |(445884559/1250000000 : ℝ)|=(445884559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3358570609/10000000000 : ℝ)|^39 ≤ (5068760424879/20000000000000 : ℝ)^31
        have hw : |(-3358570609/10000000000 : ℝ)|=(3358570609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-689593147/1250000000 : ℝ)|^39 ≤ (2365867710427/5000000000000 : ℝ)^31
        have hw : |(-689593147/1250000000 : ℝ)|=(689593147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (655020689/1250000000 : ℝ)*x 0 + (1428652837/2500000000 : ℝ)*x 1 + (1094679187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655020689/1250000000 : ℝ)^39 ≤ (44352480017033/100000000000000 : ℝ)^31 := by
    have hnat : (655020689 : ℕ)^39*100000000000000^31 ≤ 44352480017033^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655020689 1250000000 44352480017033 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428652837/2500000000 : ℝ)^39 ≤ (9892443649567/20000000000000 : ℝ)^31 := by
    have hnat : (1428652837 : ℕ)^39*20000000000000^31 ≤ 9892443649567^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428652837 2500000000 9892443649567 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094679187/10000000000 : ℝ)^39 ≤ (3092650861273/50000000000000 : ℝ)^31 := by
    have hnat : (1094679187 : ℕ)^39*50000000000000^31 ≤ 3092650861273^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094679187 10000000000 3092650861273 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655020689/1250000000 : ℝ), (1428652837/2500000000 : ℝ), (1094679187/10000000000 : ℝ)] ![(44352480017033/100000000000000 : ℝ), (9892443649567/20000000000000 : ℝ), (3092650861273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655020689/1250000000 : ℝ)|^39 ≤ (44352480017033/100000000000000 : ℝ)^31
        have hw : |(655020689/1250000000 : ℝ)|=(655020689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428652837/2500000000 : ℝ)|^39 ≤ (9892443649567/20000000000000 : ℝ)^31
        have hw : |(1428652837/2500000000 : ℝ)|=(1428652837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094679187/10000000000 : ℝ)|^39 ≤ (3092650861273/50000000000000 : ℝ)^31
        have hw : |(1094679187/10000000000 : ℝ)|=(1094679187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_12 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5069205787/10000000000 : ℝ)*x 0 + (5528172889/10000000000 : ℝ)*x 1 + (-401551261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5069205787/10000000000 : ℝ)^39 ≤ (8507958863403/20000000000000 : ℝ)^31 := by
    have hnat : (5069205787 : ℕ)^39*20000000000000^31 ≤ 8507958863403^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069205787 10000000000 8507958863403 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528172889/10000000000 : ℝ)^39 ≤ (47440697567801/100000000000000 : ℝ)^31 := by
    have hnat : (5528172889 : ℕ)^39*100000000000000^31 ≤ 47440697567801^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528172889 10000000000 47440697567801 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401551261/2500000000 : ℝ)^39 ≤ (2504877026617/25000000000000 : ℝ)^31 := by
    have hnat : (401551261 : ℕ)^39*25000000000000^31 ≤ 2504877026617^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401551261 2500000000 2504877026617 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5069205787/10000000000 : ℝ), (5528172889/10000000000 : ℝ), (-401551261/2500000000 : ℝ)] ![(8507958863403/20000000000000 : ℝ), (47440697567801/100000000000000 : ℝ), (2504877026617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5069205787/10000000000 : ℝ)|^39 ≤ (8507958863403/20000000000000 : ℝ)^31
        have hw : |(5069205787/10000000000 : ℝ)|=(5069205787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528172889/10000000000 : ℝ)|^39 ≤ (47440697567801/100000000000000 : ℝ)^31
        have hw : |(5528172889/10000000000 : ℝ)|=(5528172889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-401551261/2500000000 : ℝ)|^39 ≤ (2504877026617/25000000000000 : ℝ)^31
        have hw : |(-401551261/2500000000 : ℝ)|=(401551261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1342377759/5000000000 : ℝ)*x 0 + (284952599/1000000000 : ℝ)*x 1 + (-6686543929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342377759/5000000000 : ℝ)^39 ≤ (19121648150971/100000000000000 : ℝ)^31 := by
    have hnat : (1342377759 : ℕ)^39*100000000000000^31 ≤ 19121648150971^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342377759 5000000000 19121648150971 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284952599/1000000000 : ℝ)^39 ≤ (10304781497001/50000000000000 : ℝ)^31 := by
    have hnat : (284952599 : ℕ)^39*50000000000000^31 ≤ 10304781497001^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284952599 1000000000 10304781497001 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6686543929/10000000000 : ℝ)^39 ≤ (30134394421839/50000000000000 : ℝ)^31 := by
    have hnat : (6686543929 : ℕ)^39*50000000000000^31 ≤ 30134394421839^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6686543929 10000000000 30134394421839 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1342377759/5000000000 : ℝ), (284952599/1000000000 : ℝ), (-6686543929/10000000000 : ℝ)] ![(19121648150971/100000000000000 : ℝ), (10304781497001/50000000000000 : ℝ), (30134394421839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1342377759/5000000000 : ℝ)|^39 ≤ (19121648150971/100000000000000 : ℝ)^31
        have hw : |(-1342377759/5000000000 : ℝ)|=(1342377759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284952599/1000000000 : ℝ)|^39 ≤ (10304781497001/50000000000000 : ℝ)^31
        have hw : |(284952599/1000000000 : ℝ)|=(284952599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6686543929/10000000000 : ℝ)|^39 ≤ (30134394421839/50000000000000 : ℝ)^31
        have hw : |(-6686543929/10000000000 : ℝ)|=(6686543929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (134389367/400000000 : ℝ)*x 0 + (-3565929853/10000000000 : ℝ)*x 1 + (-5516745981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134389367/400000000 : ℝ)^39 ≤ (12677424387701/50000000000000 : ℝ)^31 := by
    have hnat : (134389367 : ℕ)^39*50000000000000^31 ≤ 12677424387701^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134389367 400000000 12677424387701 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3565929853/10000000000 : ℝ)^39 ≤ (27327788316707/100000000000000 : ℝ)^31 := by
    have hnat : (3565929853 : ℕ)^39*100000000000000^31 ≤ 27327788316707^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3565929853 10000000000 27327788316707 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516745981/10000000000 : ℝ)^39 ≤ (4731736289487/10000000000000 : ℝ)^31 := by
    have hnat : (5516745981 : ℕ)^39*10000000000000^31 ≤ 4731736289487^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516745981 10000000000 4731736289487 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134389367/400000000 : ℝ), (-3565929853/10000000000 : ℝ), (-5516745981/10000000000 : ℝ)] ![(12677424387701/50000000000000 : ℝ), (27327788316707/100000000000000 : ℝ), (4731736289487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134389367/400000000 : ℝ)|^39 ≤ (12677424387701/50000000000000 : ℝ)^31
        have hw : |(134389367/400000000 : ℝ)|=(134389367/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3565929853/10000000000 : ℝ)|^39 ≤ (27327788316707/100000000000000 : ℝ)^31
        have hw : |(-3565929853/10000000000 : ℝ)|=(3565929853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5516745981/10000000000 : ℝ)|^39 ≤ (4731736289487/10000000000000 : ℝ)^31
        have hw : |(-5516745981/10000000000 : ℝ)|=(5516745981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (571309459/1000000000 : ℝ)*x 0 + (5241716313/10000000000 : ℝ)*x 1 + (547339707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (571309459/1000000000 : ℝ)^39 ≤ (49445702766979/100000000000000 : ℝ)^31 := by
    have hnat : (571309459 : ℕ)^39*100000000000000^31 ≤ 49445702766979^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571309459 1000000000 49445702766979 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241716313/10000000000 : ℝ)^39 ≤ (5546124234031/12500000000000 : ℝ)^31 := by
    have hnat : (5241716313 : ℕ)^39*12500000000000^31 ≤ 5546124234031^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241716313 10000000000 5546124234031 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547339707/5000000000 : ℝ)^39 ≤ (1546325834043/25000000000000 : ℝ)^31 := by
    have hnat : (547339707 : ℕ)^39*25000000000000^31 ≤ 1546325834043^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547339707 5000000000 1546325834043 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(571309459/1000000000 : ℝ), (5241716313/10000000000 : ℝ), (547339707/5000000000 : ℝ)] ![(49445702766979/100000000000000 : ℝ), (5546124234031/12500000000000 : ℝ), (1546325834043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(571309459/1000000000 : ℝ)|^39 ≤ (49445702766979/100000000000000 : ℝ)^31
        have hw : |(571309459/1000000000 : ℝ)|=(571309459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241716313/10000000000 : ℝ)|^39 ≤ (5546124234031/12500000000000 : ℝ)^31
        have hw : |(5241716313/10000000000 : ℝ)|=(5241716313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547339707/5000000000 : ℝ)|^39 ≤ (1546325834043/25000000000000 : ℝ)^31
        have hw : |(547339707/5000000000 : ℝ)|=(547339707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_18 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (221068239/400000000 : ℝ)*x 0 + (1267676581/2500000000 : ℝ)*x 1 + (-1606204303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221068239/400000000 : ℝ)^39 ≤ (9484972192119/20000000000000 : ℝ)^31 := by
    have hnat : (221068239 : ℕ)^39*20000000000000^31 ≤ 9484972192119^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221068239 400000000 9484972192119 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267676581/2500000000 : ℝ)^39 ≤ (5319454592807/12500000000000 : ℝ)^31 := by
    have hnat : (1267676581 : ℕ)^39*12500000000000^31 ≤ 5319454592807^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267676581 2500000000 5319454592807 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1606204303/10000000000 : ℝ)^39 ≤ (10019502291243/100000000000000 : ℝ)^31 := by
    have hnat : (1606204303 : ℕ)^39*100000000000000^31 ≤ 10019502291243^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606204303 10000000000 10019502291243 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(221068239/400000000 : ℝ), (1267676581/2500000000 : ℝ), (-1606204303/10000000000 : ℝ)] ![(9484972192119/20000000000000 : ℝ), (5319454592807/12500000000000 : ℝ), (10019502291243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(221068239/400000000 : ℝ)|^39 ≤ (9484972192119/20000000000000 : ℝ)^31
        have hw : |(221068239/400000000 : ℝ)|=(221068239/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267676581/2500000000 : ℝ)|^39 ≤ (5319454592807/12500000000000 : ℝ)^31
        have hw : |(1267676581/2500000000 : ℝ)|=(1267676581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1606204303/10000000000 : ℝ)|^39 ≤ (10019502291243/100000000000000 : ℝ)^31
        have hw : |(-1606204303/10000000000 : ℝ)|=(1606204303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3013721709/10000000000 : ℝ)*x 0 + (2831316777/10000000000 : ℝ)*x 1 + (-1608996053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3013721709/10000000000 : ℝ)^39 ≤ (884582092773/4000000000000 : ℝ)^31 := by
    have hnat : (3013721709 : ℕ)^39*4000000000000^31 ≤ 884582092773^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013721709 10000000000 884582092773 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831316777/10000000000 : ℝ)^39 ≤ (20444012135673/100000000000000 : ℝ)^31 := by
    have hnat : (2831316777 : ℕ)^39*100000000000000^31 ≤ 20444012135673^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831316777 10000000000 20444012135673 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1608996053/2500000000 : ℝ)^39 ≤ (28720717766147/50000000000000 : ℝ)^31 := by
    have hnat : (1608996053 : ℕ)^39*50000000000000^31 ≤ 28720717766147^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608996053 2500000000 28720717766147 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3013721709/10000000000 : ℝ), (2831316777/10000000000 : ℝ), (-1608996053/2500000000 : ℝ)] ![(884582092773/4000000000000 : ℝ), (20444012135673/100000000000000 : ℝ), (28720717766147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3013721709/10000000000 : ℝ)|^39 ≤ (884582092773/4000000000000 : ℝ)^31
        have hw : |(-3013721709/10000000000 : ℝ)|=(3013721709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831316777/10000000000 : ℝ)|^39 ≤ (20444012135673/100000000000000 : ℝ)^31
        have hw : |(2831316777/10000000000 : ℝ)|=(2831316777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1608996053/2500000000 : ℝ)|^39 ≤ (28720717766147/50000000000000 : ℝ)^31
        have hw : |(-1608996053/2500000000 : ℝ)|=(1608996053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1771811371/5000000000 : ℝ)*x 0 + (-186196291/500000000 : ℝ)*x 1 + (-5209615287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1771811371/5000000000 : ℝ)^39 ≤ (27112893127903/100000000000000 : ℝ)^31 := by
    have hnat : (1771811371 : ℕ)^39*100000000000000^31 ≤ 27112893127903^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771811371 5000000000 27112893127903 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186196291/500000000 : ℝ)^39 ≤ (28859686392531/100000000000000 : ℝ)^31 := by
    have hnat : (186196291 : ℕ)^39*100000000000000^31 ≤ 28859686392531^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186196291 500000000 28859686392531 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5209615287/10000000000 : ℝ)^39 ≤ (44027420464641/100000000000000 : ℝ)^31 := by
    have hnat : (5209615287 : ℕ)^39*100000000000000^31 ≤ 44027420464641^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209615287 10000000000 44027420464641 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1771811371/5000000000 : ℝ), (-186196291/500000000 : ℝ), (-5209615287/10000000000 : ℝ)] ![(27112893127903/100000000000000 : ℝ), (28859686392531/100000000000000 : ℝ), (44027420464641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1771811371/5000000000 : ℝ)|^39 ≤ (27112893127903/100000000000000 : ℝ)^31
        have hw : |(1771811371/5000000000 : ℝ)|=(1771811371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186196291/500000000 : ℝ)|^39 ≤ (28859686392531/100000000000000 : ℝ)^31
        have hw : |(-186196291/500000000 : ℝ)|=(186196291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5209615287/10000000000 : ℝ)|^39 ≤ (44027420464641/100000000000000 : ℝ)^31
        have hw : |(-5209615287/10000000000 : ℝ)|=(5209615287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (271619723/500000000 : ℝ)*x 0 + (5327791449/10000000000 : ℝ)*x 1 + (1383408891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271619723/500000000 : ℝ)^39 ≤ (290056079399/625000000000 : ℝ)^31 := by
    have hnat : (271619723 : ℕ)^39*625000000000^31 ≤ 290056079399^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271619723 500000000 290056079399 625000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5327791449/10000000000 : ℝ)^39 ≤ (45287542667669/100000000000000 : ℝ)^31 := by
    have hnat : (5327791449 : ℕ)^39*100000000000000^31 ≤ 45287542667669^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327791449 10000000000 45287542667669 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383408891/10000000000 : ℝ)^39 ≤ (4151742305273/50000000000000 : ℝ)^31 := by
    have hnat : (1383408891 : ℕ)^39*50000000000000^31 ≤ 4151742305273^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383408891 10000000000 4151742305273 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271619723/500000000 : ℝ), (5327791449/10000000000 : ℝ), (1383408891/10000000000 : ℝ)] ![(290056079399/625000000000 : ℝ), (45287542667669/100000000000000 : ℝ), (4151742305273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271619723/500000000 : ℝ)|^39 ≤ (290056079399/625000000000 : ℝ)^31
        have hw : |(271619723/500000000 : ℝ)|=(271619723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5327791449/10000000000 : ℝ)|^39 ≤ (45287542667669/100000000000000 : ℝ)^31
        have hw : |(5327791449/10000000000 : ℝ)|=(5327791449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1383408891/10000000000 : ℝ)|^39 ≤ (4151742305273/50000000000000 : ℝ)^31
        have hw : |(1383408891/10000000000 : ℝ)|=(1383408891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316048_s1_s1_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4935836081/10000000000 : ℝ)*x 0 + (5207414823/10000000000 : ℝ)*x 1 + (-2197087721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4935836081/10000000000 : ℝ)^39 ≤ (41136563942039/100000000000000 : ℝ)^31 := by
    have hnat : (4935836081 : ℕ)^39*100000000000000^31 ≤ 41136563942039^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4935836081 10000000000 41136563942039 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207414823/10000000000 : ℝ)^39 ≤ (8800805221709/20000000000000 : ℝ)^31 := by
    have hnat : (5207414823 : ℕ)^39*20000000000000^31 ≤ 8800805221709^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207414823 10000000000 8800805221709 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197087721/10000000000 : ℝ)^39 ≤ (3714852482677/25000000000000 : ℝ)^31 := by
    have hnat : (2197087721 : ℕ)^39*25000000000000^31 ≤ 3714852482677^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197087721 10000000000 3714852482677 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4935836081/10000000000 : ℝ), (5207414823/10000000000 : ℝ), (-2197087721/10000000000 : ℝ)] ![(41136563942039/100000000000000 : ℝ), (8800805221709/20000000000000 : ℝ), (3714852482677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4935836081/10000000000 : ℝ)|^39 ≤ (41136563942039/100000000000000 : ℝ)^31
        have hw : |(4935836081/10000000000 : ℝ)|=(4935836081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207414823/10000000000 : ℝ)|^39 ≤ (8800805221709/20000000000000 : ℝ)^31
        have hw : |(5207414823/10000000000 : ℝ)|=(5207414823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197087721/10000000000 : ℝ)|^39 ≤ (3714852482677/25000000000000 : ℝ)^31
        have hw : |(-2197087721/10000000000 : ℝ)|=(2197087721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316048_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((18173/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18173/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36291/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36291/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5113/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5113/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13633/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13633/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27257/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27257/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-623/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-623/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (18173/25000 : ℝ) ^ (19/4 : ℝ) ≤ (21981708030162559043/100000000000000000000 : ℝ) := by
    have hpowers : (18173/25000 : ℝ)^19 ≤ (21981708030162559043/100000000000000000000 : ℝ)^4 := by
      have hnat : (18173 : ℕ)^19*100000000000000000000^4 ≤ 21981708030162559043^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18173 25000 21981708030162559043 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18173/25000 : ℝ)) (X := (21981708030162559043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (121981708030162559043/100000000000000000000 : ℝ) ≤ (10427190486481121/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (121981708030162559043/100000000000000000000 : ℝ)^4 ≤ (10427190486481121/10000000000000000 : ℝ)^19 := by
      have hnat : (121981708030162559043 : ℕ)^4*10000000000000000^19 ≤ 10427190486481121^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121981708030162559043 100000000000000000000 10427190486481121 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10427190486481121/10000000000000000 : ℝ)) (X := (121981708030162559043/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (71981708030162559043/50000000000000000000 : ℝ) ≤ (337416458186009/312500000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (71981708030162559043/50000000000000000000 : ℝ)^4 ≤ (337416458186009/312500000000000 : ℝ)^19 := by
      have hnat : (71981708030162559043 : ℕ)^4*312500000000000^19 ≤ 337416458186009^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71981708030162559043 50000000000000000000 337416458186009 312500000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (337416458186009/312500000000000 : ℝ)) (X := (71981708030162559043/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(427190486481121/7269200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(370136175471167/7269200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (18173/25000 : ℝ)) (alpha := (427190486481121/7269200000000000 : ℝ)) (beta := (370136175471167/7269200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18173/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(427190486481121/7269200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(370136175471167/7269200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (36291/50000 : ℝ) ^ (19/4 : ℝ) ≤ (10912077122043712979/50000000000000000000 : ℝ) := by
    have hpowers : (36291/50000 : ℝ)^19 ≤ (10912077122043712979/50000000000000000000 : ℝ)^4 := by
      have hnat : (36291 : ℕ)^19*50000000000000000000^4 ≤ 10912077122043712979^4*50000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36291 50000 10912077122043712979 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36291/50000 : ℝ)) (X := (10912077122043712979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (60912077122043712979/50000000000000000000 : ℝ) ≤ (10424353682221161/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (60912077122043712979/50000000000000000000 : ℝ)^4 ≤ (10424353682221161/10000000000000000 : ℝ)^19 := by
      have hnat : (60912077122043712979 : ℕ)^4*10000000000000000^19 ≤ 10424353682221161^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60912077122043712979 50000000000000000000 10424353682221161 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10424353682221161/10000000000000000 : ℝ)) (X := (60912077122043712979/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (35912077122043712979/25000000000000000000 : ℝ) ≤ (10792346942381421/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (35912077122043712979/25000000000000000000 : ℝ)^4 ≤ (10792346942381421/10000000000000000 : ℝ)^19 := by
      have hnat : (35912077122043712979 : ℕ)^4*10000000000000000^19 ≤ 10792346942381421^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35912077122043712979 25000000000000000000 10792346942381421 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10792346942381421/10000000000000000 : ℝ)) (X := (35912077122043712979/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(424353682221161/7258200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6133221002671/120970000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (36291/50000 : ℝ)) (alpha := (424353682221161/7258200000000000 : ℝ)) (beta := (6133221002671/120970000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (36291/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(424353682221161/7258200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6133221002671/120970000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5113/25000 : ℝ) ^ (19/4 : ℝ) ≤ (53210210164103283/100000000000000000000 : ℝ) := by
    have hpowers : (5113/25000 : ℝ)^19 ≤ (53210210164103283/100000000000000000000 : ℝ)^4 := by
      have hnat : (5113 : ℕ)^19*100000000000000000000^4 ≤ 53210210164103283^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5113 25000 53210210164103283 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5113/25000 : ℝ)) (X := (53210210164103283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100053210210164103283/100000000000000000000 : ℝ) ≤ (2500279994933797/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (100053210210164103283/100000000000000000000 : ℝ)^4 ≤ (2500279994933797/2500000000000000 : ℝ)^19 := by
      have hnat : (100053210210164103283 : ℕ)^4*2500000000000000^19 ≤ 2500279994933797^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053210210164103283 100000000000000000000 2500279994933797 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500279994933797/2500000000000000 : ℝ)) (X := (100053210210164103283/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50053210210164103283/50000000000000000000 : ℝ) ≤ (1000223948933749/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50053210210164103283/50000000000000000000 : ℝ)^4 ≤ (1000223948933749/1000000000000000 : ℝ)^19 := by
      have hnat : (50053210210164103283 : ℕ)^4*1000000000000000^19 ≤ 1000223948933749^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053210210164103283 50000000000000000000 1000223948933749 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000223948933749/1000000000000000 : ℝ)) (X := (50053210210164103283/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(279994933797/511300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(559754801151/1022600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (5113/25000 : ℝ)) (alpha := (279994933797/511300000000000 : ℝ)) (beta := (559754801151/1022600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5113/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(279994933797/511300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(559754801151/1022600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2900134443/10000000000 : ℝ)*X 0 0+(579840881/2000000000 : ℝ)*X 0 1+(-323689671/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((730266579/2000000000 : ℝ)*X 1 0+(-3650161957/10000000000 : ℝ)*X 1 1+(-1294791717/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((335263353/625000000 : ℝ)*X 2 0+(5365742409/10000000000 : ℝ)*X 2 1+(285265671/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5097115561/10000000000 : ℝ)*X 0 0+(25492841/50000000 : ℝ)*X 0 1+(-2132898363/10000000000 : ℝ)*X 0 2+(5097115561/10000000000 : ℝ)*X 1 0+(25492841/50000000 : ℝ)*X 1 1+(-2132898363/10000000000 : ℝ)*X 1 2+(5097115561/10000000000 : ℝ)*X 2 0+(25492841/50000000 : ℝ)*X 2 1+(-2132898363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2850441093/10000000000 : ℝ)*X 0 0+(21470597/80000000 : ℝ)*X 0 1+(-6686545141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((445884559/1250000000 : ℝ)*X 1 0+(-3358570609/10000000000 : ℝ)*X 1 1+(-689593147/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((655020689/1250000000 : ℝ)*X 2 0+(1428652837/2500000000 : ℝ)*X 2 1+(1094679187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((5069205787/10000000000 : ℝ)*X 0 0+(5528172889/10000000000 : ℝ)*X 0 1+(-401551261/2500000000 : ℝ)*X 0 2+(5069205787/10000000000 : ℝ)*X 1 0+(5528172889/10000000000 : ℝ)*X 1 1+(-401551261/2500000000 : ℝ)*X 1 2+(5069205787/10000000000 : ℝ)*X 2 0+(5528172889/10000000000 : ℝ)*X 2 1+(-401551261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1342377759/5000000000 : ℝ)*X 0 0+(284952599/1000000000 : ℝ)*X 0 1+(-6686543929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((134389367/400000000 : ℝ)*X 1 0+(-3565929853/10000000000 : ℝ)*X 1 1+(-5516745981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((571309459/1000000000 : ℝ)*X 2 0+(5241716313/10000000000 : ℝ)*X 2 1+(547339707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((221068239/400000000 : ℝ)*X 0 0+(1267676581/2500000000 : ℝ)*X 0 1+(-1606204303/10000000000 : ℝ)*X 0 2+(221068239/400000000 : ℝ)*X 1 0+(1267676581/2500000000 : ℝ)*X 1 1+(-1606204303/10000000000 : ℝ)*X 1 2+(221068239/400000000 : ℝ)*X 2 0+(1267676581/2500000000 : ℝ)*X 2 1+(-1606204303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-3013721709/10000000000 : ℝ)*X 0 0+(2831316777/10000000000 : ℝ)*X 0 1+(-1608996053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1771811371/5000000000 : ℝ)*X 1 0+(-186196291/500000000 : ℝ)*X 1 1+(-5209615287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((271619723/500000000 : ℝ)*X 2 0+(5327791449/10000000000 : ℝ)*X 2 1+(1383408891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((4935836081/10000000000 : ℝ)*X 0 0+(5207414823/10000000000 : ℝ)*X 0 1+(-2197087721/10000000000 : ℝ)*X 0 2+(4935836081/10000000000 : ℝ)*X 1 0+(5207414823/10000000000 : ℝ)*X 1 1+(-2197087721/10000000000 : ℝ)*X 1 2+(4935836081/10000000000 : ℝ)*X 2 0+(5207414823/10000000000 : ℝ)*X 2 1+(-2197087721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316048_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((13633/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13633/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (209767734292938188113666341087/11240356872530000000000000000000000 : ℝ) := by norm_num
    linear_combination (112624471231/125000000000 : ℝ)*(base39) + (6565298831541/1000000000000 : ℝ)*(base59) + (1230500654843/500000000000 : ℝ)*(base60) + (2716073982477/200000000000 : ℝ)*(major_s1_0) + (2716073982477/200000000000 : ℝ)*(major_s1_1) + (2716073982477/200000000000 : ℝ)*(major_s1_2) + (734399919/1000000000000 : ℝ)*(sp_s1_0) + (8114531/62500000000 : ℝ)*(sp_s1_2) + (9749299005669/500000000000 : ℝ)*(sp_s1_7) + (9749508529137/500000000000 : ℝ)*(sp_s1_8) + (487480064469/25000000000 : ℝ)*(sp_s1_9) + (3830529293233/500000000000 : ℝ)*(sp_s1_12) + (315352983/1000000000000 : ℝ)*(sp_s1_14) + (34260637/100000000000 : ℝ)*(sp_s1_25) + (1915350298209/250000000000 : ℝ)*(f.failure) + (2437416551407/125000000000 : ℝ)*(f.sum) + (192000122872487017/2474078440000000000000000000000 : ℝ)*base63 + (3659485503493/40904000000000000000000000 : ℝ)*base65 + (67500511078129/120970000000000000000000000 : ℝ)*base67 + (42973414927859/102260000000000000000000000 : ℝ)*base68 + (4278406231426666431/7433483920000000000000000000000 : ℝ)*base71 + (1355449516276923/1453840000000000000000000000 : ℝ)*base73 + (14372390725479/483880000000000000000000000 : ℝ)*base75 + (14331625530313/290768000000000000000000000 : ℝ)*base77 + (1862624214838617327/3517420496000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (7713/25000000000000000 : ℝ)*base87 + (7713/25000000000000000 : ℝ)*base89 + (7713/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27257/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27257/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (267866325941374404530991952923/56201784362650000000000000000000000 : ℝ) := by norm_num
    linear_combination (450490577993/500000000000 : ℝ)*(base39) + (6646339170947/1000000000000 : ℝ)*(base59) + (2787358123617/1000000000000 : ℝ)*(base60) + (3394988418327/250000000000 : ℝ)*(major_s1_0) + (3394988418327/250000000000 : ℝ)*(major_s1_1) + (3394988418327/250000000000 : ℝ)*(major_s1_2) + (1423257/62500000000 : ℝ)*(sp_s1_1) + (1691031/20000000000 : ℝ)*(sp_s1_6) + (117847879/1000000000000 : ℝ)*(sp_s1_8) + (7402259/500000000000 : ℝ)*(sp_s1_9) + (19498739387421/1000000000000 : ℝ)*(sp_s1_13) + (19498598767431/1000000000000 : ℝ)*(sp_s1_14) + (19498724582903/1000000000000 : ℝ)*(sp_s1_15) + (3830540909461/500000000000 : ℝ)*(sp_s1_18) + (957645796309/125000000000 : ℝ)*(f.failure) + (19498739387421/1000000000000 : ℝ)*(f.sum) + (901220435077166241/3092598050000000000000000000000 : ℝ)*base63 + (68572914697047/255650000000000000000000000 : ℝ)*base64 + (16941432346543/120970000000000000000000000 : ℝ)*base66 + (8614354999817/255650000000000000000000000 : ℝ)*base69 + (103679266663884471/9291854900000000000000000000000 : ℝ)*base70 + (1116898309479919/1817300000000000000000000000 : ℝ)*base73 + (128919832066839/604850000000000000000000000 : ℝ)*base75 + (410774371762937/1817300000000000000000000000 : ℝ)*base77 + (3627707701911315913/21983878100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (5587/12500000000000000 : ℝ)*base86 + (5587/12500000000000000 : ℝ)*base88 + (5587/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-623/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-623/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2631038780951216409462786187191/224807137450600000000000000000000000 : ℝ) := by norm_num
    linear_combination (175484377963/500000000000 : ℝ)*(base39) + (4349537/1000000000000 : ℝ)*(base40) + (1409818825341/1000000000000 : ℝ)*(base59) + (4712883501387/1000000000000 : ℝ)*(major_s1_0) + (4712883501387/1000000000000 : ℝ)*(major_s1_1) + (4712883501387/1000000000000 : ℝ)*(major_s1_2) + (1840071/7812500000 : ℝ)*(sp_s1_1) + (71448453/250000000000 : ℝ)*(sp_s1_6) + (91308471/500000000000 : ℝ)*(sp_s1_9) + (74658001/1000000000000 : ℝ)*(sp_s1_12) + (6766977552137/1000000000000 : ℝ)*(sp_s1_19) + (135334840461/20000000000 : ℝ)*(sp_s1_20) + (1691698733799/250000000000 : ℝ)*(sp_s1_21) + (2658425097637/1000000000000 : ℝ)*(sp_s1_25) + (2658785549449/1000000000000 : ℝ)*(f.failure) + (6766977552137/1000000000000 : ℝ)*(f.sum) + (6760924747844294529/12370392200000000000000000000000 : ℝ)*base62 + (178825681711577/1022600000000000000000000000 : ℝ)*base64 + (172350353503/6048500000000000000000000 : ℝ)*base67 + (386059545243319/511300000000000000000000000 : ℝ)*base68 + (1541077479524316209/37167419600000000000000000000000 : ℝ)*base71 + (7481217311700749/7269200000000000000000000000 : ℝ)*base73 + (2085032733380431/2419400000000000000000000000 : ℝ)*base74 + (6622950199236373/7269200000000000000000000000 : ℝ)*base76 + (46474040372689906053/87935512400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (18607/100000000000000000 : ℝ)*base86 + (18607/100000000000000000 : ℝ)*base88 + (18607/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((18173/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18173/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36291/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36291/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5113/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5113/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13633/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13633/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27257/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27257/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-623/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-623/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316048_s1 p hpa hpb X hX hprev0

#print axioms solution

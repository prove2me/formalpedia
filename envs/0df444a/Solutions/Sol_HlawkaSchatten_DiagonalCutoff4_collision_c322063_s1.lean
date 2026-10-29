-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c322063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:47:31.355467+00:00
-- url     : https://prove2.me/submissions/735d9187-9699-44ef-a045-b2fd2c62061d

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
theorem collision_support_c322063_s1_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-114259071/1250000000 : ℝ)*x 0 + (21764519/40000000 : ℝ)*x 1 + (1377416419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114259071/1250000000 : ℝ)^83 ≤ (2581229751681/50000000000000 : ℝ)^67 := by
    have hnat : (114259071 : ℕ)^83*50000000000000^67 ≤ 2581229751681^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114259071 1250000000 2581229751681 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21764519/40000000 : ℝ)^83 ≤ (11762782474653/25000000000000 : ℝ)^67 := by
    have hnat : (21764519 : ℕ)^83*25000000000000^67 ≤ 11762782474653^67*40000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21764519 40000000 11762782474653 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377416419/2500000000 : ℝ)^83 ≤ (4778641058689/10000000000000 : ℝ)^67 := by
    have hnat : (1377416419 : ℕ)^83*10000000000000^67 ≤ 4778641058689^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377416419 2500000000 4778641058689 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114259071/1250000000 : ℝ), (21764519/40000000 : ℝ), (1377416419/2500000000 : ℝ)] ![(2581229751681/50000000000000 : ℝ), (11762782474653/25000000000000 : ℝ), (4778641058689/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114259071/1250000000 : ℝ)|^83 ≤ (2581229751681/50000000000000 : ℝ)^67
        have hw : |(-114259071/1250000000 : ℝ)|=(114259071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21764519/40000000 : ℝ)|^83 ≤ (11762782474653/25000000000000 : ℝ)^67
        have hw : |(21764519/40000000 : ℝ)|=(21764519/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377416419/2500000000 : ℝ)|^83 ≤ (4778641058689/10000000000000 : ℝ)^67
        have hw : |(1377416419/2500000000 : ℝ)|=(1377416419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5440879533/10000000000 : ℝ)*x 0 + (-910459089/10000000000 : ℝ)*x 1 + (689033361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5440879533/10000000000 : ℝ)^83 ≤ (47048449504269/100000000000000 : ℝ)^67 := by
    have hnat : (5440879533 : ℕ)^83*100000000000000^67 ≤ 47048449504269^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440879533 10000000000 47048449504269 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910459089/10000000000 : ℝ)^83 ≤ (5137189834141/100000000000000 : ℝ)^67 := by
    have hnat : (910459089 : ℕ)^83*100000000000000^67 ≤ 5137189834141^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910459089 10000000000 5137189834141 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689033361/1250000000 : ℝ)^83 ≤ (4781436064277/10000000000000 : ℝ)^67 := by
    have hnat : (689033361 : ℕ)^83*10000000000000^67 ≤ 4781436064277^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689033361 1250000000 4781436064277 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5440879533/10000000000 : ℝ), (-910459089/10000000000 : ℝ), (689033361/1250000000 : ℝ)] ![(47048449504269/100000000000000 : ℝ), (5137189834141/100000000000000 : ℝ), (4781436064277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5440879533/10000000000 : ℝ)|^83 ≤ (47048449504269/100000000000000 : ℝ)^67
        have hw : |(5440879533/10000000000 : ℝ)|=(5440879533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910459089/10000000000 : ℝ)|^83 ≤ (5137189834141/100000000000000 : ℝ)^67
        have hw : |(-910459089/10000000000 : ℝ)|=(910459089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689033361/1250000000 : ℝ)|^83 ≤ (4781436064277/10000000000000 : ℝ)^67
        have hw : |(689033361/1250000000 : ℝ)|=(689033361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2737656999/5000000000 : ℝ)*x 0 + (550208519/1000000000 : ℝ)*x 1 + (-873111333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737656999/5000000000 : ℝ)^83 ≤ (23708798690437/50000000000000 : ℝ)^67 := by
    have hnat : (2737656999 : ℕ)^83*50000000000000^67 ≤ 23708798690437^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737656999 5000000000 23708798690437 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550208519/1000000000 : ℝ)^83 ≤ (4770497614467/10000000000000 : ℝ)^67 := by
    have hnat : (550208519 : ℕ)^83*10000000000000^67 ≤ 4770497614467^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550208519 1000000000 4770497614467 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873111333/10000000000 : ℝ)^83 ≤ (487742645993/10000000000000 : ℝ)^67 := by
    have hnat : (873111333 : ℕ)^83*10000000000000^67 ≤ 487742645993^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873111333 10000000000 487742645993 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737656999/5000000000 : ℝ), (550208519/1000000000 : ℝ), (-873111333/10000000000 : ℝ)] ![(23708798690437/50000000000000 : ℝ), (4770497614467/10000000000000 : ℝ), (487742645993/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737656999/5000000000 : ℝ)|^83 ≤ (23708798690437/50000000000000 : ℝ)^67
        have hw : |(2737656999/5000000000 : ℝ)|=(2737656999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550208519/1000000000 : ℝ)|^83 ≤ (4770497614467/10000000000000 : ℝ)^67
        have hw : |(550208519/1000000000 : ℝ)|=(550208519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-873111333/10000000000 : ℝ)|^83 ≤ (487742645993/10000000000000 : ℝ)^67
        have hw : |(-873111333/10000000000 : ℝ)|=(873111333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4204871659/10000000000 : ℝ)*x 0 + (2068409887/5000000000 : ℝ)*x 1 + (2008274303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204871659/10000000000 : ℝ)^83 ≤ (34190279729857/100000000000000 : ℝ)^67 := by
    have hnat : (4204871659 : ℕ)^83*100000000000000^67 ≤ 34190279729857^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204871659 10000000000 34190279729857 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068409887/5000000000 : ℝ)^83 ≤ (8376533024827/25000000000000 : ℝ)^67 := by
    have hnat : (2068409887 : ℕ)^83*25000000000000^67 ≤ 8376533024827^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068409887 5000000000 8376533024827 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008274303/5000000000 : ℝ)^83 ≤ (6460717630441/20000000000000 : ℝ)^67 := by
    have hnat : (2008274303 : ℕ)^83*20000000000000^67 ≤ 6460717630441^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008274303 5000000000 6460717630441 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204871659/10000000000 : ℝ), (2068409887/5000000000 : ℝ), (2008274303/5000000000 : ℝ)] ![(34190279729857/100000000000000 : ℝ), (8376533024827/25000000000000 : ℝ), (6460717630441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204871659/10000000000 : ℝ)|^83 ≤ (34190279729857/100000000000000 : ℝ)^67
        have hw : |(4204871659/10000000000 : ℝ)|=(4204871659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068409887/5000000000 : ℝ)|^83 ≤ (8376533024827/25000000000000 : ℝ)^67
        have hw : |(2068409887/5000000000 : ℝ)|=(2068409887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008274303/5000000000 : ℝ)|^83 ≤ (6460717630441/20000000000000 : ℝ)^67
        have hw : |(2008274303/5000000000 : ℝ)|=(2008274303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-462842543/5000000000 : ℝ)*x 0 + (432009677/1000000000 : ℝ)*x 1 + (6567537573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462842543/5000000000 : ℝ)^83 ≤ (1310957260411/25000000000000 : ℝ)^67 := by
    have hnat : (462842543 : ℕ)^83*25000000000000^67 ≤ 1310957260411^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462842543 5000000000 1310957260411 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432009677/1000000000 : ℝ)^83 ≤ (707093974571/2000000000000 : ℝ)^67 := by
    have hnat : (432009677 : ℕ)^83*2000000000000^67 ≤ 707093974571^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432009677 1000000000 707093974571 2000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6567537573/10000000000 : ℝ)^83 ≤ (29700736106237/50000000000000 : ℝ)^67 := by
    have hnat : (6567537573 : ℕ)^83*50000000000000^67 ≤ 29700736106237^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6567537573 10000000000 29700736106237 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462842543/5000000000 : ℝ), (432009677/1000000000 : ℝ), (6567537573/10000000000 : ℝ)] ![(1310957260411/25000000000000 : ℝ), (707093974571/2000000000000 : ℝ), (29700736106237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462842543/5000000000 : ℝ)|^83 ≤ (1310957260411/25000000000000 : ℝ)^67
        have hw : |(-462842543/5000000000 : ℝ)|=(462842543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432009677/1000000000 : ℝ)|^83 ≤ (707093974571/2000000000000 : ℝ)^67
        have hw : |(432009677/1000000000 : ℝ)|=(432009677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6567537573/10000000000 : ℝ)|^83 ≤ (29700736106237/50000000000000 : ℝ)^67
        have hw : |(6567537573/10000000000 : ℝ)|=(6567537573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4755603903/10000000000 : ℝ)*x 0 + (-38366019/2000000000 : ℝ)*x 1 + (657026367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4755603903/10000000000 : ℝ)^83 ≤ (39821761121069/100000000000000 : ℝ)^67 := by
    have hnat : (4755603903 : ℕ)^83*100000000000000^67 ≤ 39821761121069^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755603903 10000000000 39821761121069 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38366019/2000000000 : ℝ)^83 ≤ (373110106423/50000000000000 : ℝ)^67 := by
    have hnat : (38366019 : ℕ)^83*50000000000000^67 ≤ 373110106423^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38366019 2000000000 373110106423 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657026367/1000000000 : ℝ)^83 ≤ (59432018663443/100000000000000 : ℝ)^67 := by
    have hnat : (657026367 : ℕ)^83*100000000000000^67 ≤ 59432018663443^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657026367 1000000000 59432018663443 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4755603903/10000000000 : ℝ), (-38366019/2000000000 : ℝ), (657026367/1000000000 : ℝ)] ![(39821761121069/100000000000000 : ℝ), (373110106423/50000000000000 : ℝ), (59432018663443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4755603903/10000000000 : ℝ)|^83 ≤ (39821761121069/100000000000000 : ℝ)^67
        have hw : |(4755603903/10000000000 : ℝ)|=(4755603903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38366019/2000000000 : ℝ)|^83 ≤ (373110106423/50000000000000 : ℝ)^67
        have hw : |(-38366019/2000000000 : ℝ)|=(38366019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657026367/1000000000 : ℝ)|^83 ≤ (59432018663443/100000000000000 : ℝ)^67
        have hw : |(657026367/1000000000 : ℝ)|=(657026367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4460929949/10000000000 : ℝ)*x 0 + (274627699/400000000 : ℝ)*x 1 + (-63982529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460929949/10000000000 : ℝ)^83 ≤ (18393996570323/50000000000000 : ℝ)^67 := by
    have hnat : (4460929949 : ℕ)^83*50000000000000^67 ≤ 18393996570323^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460929949 10000000000 18393996570323 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274627699/400000000 : ℝ)^83 ≤ (62760095215799/100000000000000 : ℝ)^67 := by
    have hnat : (274627699 : ℕ)^83*100000000000000^67 ≤ 62760095215799^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274627699 400000000 62760095215799 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63982529/5000000000 : ℝ)^83 ≤ (451911634809/100000000000000 : ℝ)^67 := by
    have hnat : (63982529 : ℕ)^83*100000000000000^67 ≤ 451911634809^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63982529 5000000000 451911634809 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460929949/10000000000 : ℝ), (274627699/400000000 : ℝ), (-63982529/5000000000 : ℝ)] ![(18393996570323/50000000000000 : ℝ), (62760095215799/100000000000000 : ℝ), (451911634809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460929949/10000000000 : ℝ)|^83 ≤ (18393996570323/50000000000000 : ℝ)^67
        have hw : |(4460929949/10000000000 : ℝ)|=(4460929949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274627699/400000000 : ℝ)|^83 ≤ (62760095215799/100000000000000 : ℝ)^67
        have hw : |(274627699/400000000 : ℝ)|=(274627699/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63982529/5000000000 : ℝ)|^83 ≤ (451911634809/100000000000000 : ℝ)^67
        have hw : |(-63982529/5000000000 : ℝ)|=(63982529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2171554711/5000000000 : ℝ)*x 0 + (6101183367/10000000000 : ℝ)*x 1 + (1582666641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171554711/5000000000 : ℝ)^83 ≤ (17794075847431/50000000000000 : ℝ)^67 := by
    have hnat : (2171554711 : ℕ)^83*50000000000000^67 ≤ 17794075847431^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171554711 5000000000 17794075847431 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6101183367/10000000000 : ℝ)^83 ≤ (54221269076219/100000000000000 : ℝ)^67 := by
    have hnat : (6101183367 : ℕ)^83*100000000000000^67 ≤ 54221269076219^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6101183367 10000000000 54221269076219 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1582666641/10000000000 : ℝ)^83 ≤ (10190579210361/100000000000000 : ℝ)^67 := by
    have hnat : (1582666641 : ℕ)^83*100000000000000^67 ≤ 10190579210361^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582666641 10000000000 10190579210361 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171554711/5000000000 : ℝ), (6101183367/10000000000 : ℝ), (1582666641/10000000000 : ℝ)] ![(17794075847431/50000000000000 : ℝ), (54221269076219/100000000000000 : ℝ), (10190579210361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171554711/5000000000 : ℝ)|^83 ≤ (17794075847431/50000000000000 : ℝ)^67
        have hw : |(2171554711/5000000000 : ℝ)|=(2171554711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6101183367/10000000000 : ℝ)|^83 ≤ (54221269076219/100000000000000 : ℝ)^67
        have hw : |(6101183367/10000000000 : ℝ)|=(6101183367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1582666641/10000000000 : ℝ)|^83 ≤ (10190579210361/100000000000000 : ℝ)^67
        have hw : |(1582666641/10000000000 : ℝ)|=(1582666641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-196884383/10000000000 : ℝ)*x 0 + (4721101873/10000000000 : ℝ)*x 1 + (6599978597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196884383/10000000000 : ℝ)^83 ≤ (96331594573/12500000000000 : ℝ)^67 := by
    have hnat : (196884383 : ℕ)^83*12500000000000^67 ≤ 96331594573^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196884383 10000000000 96331594573 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4721101873/10000000000 : ℝ)^83 ≤ (9866042721513/25000000000000 : ℝ)^67 := by
    have hnat : (4721101873 : ℕ)^83*25000000000000^67 ≤ 9866042721513^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4721101873 10000000000 9866042721513 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6599978597/10000000000 : ℝ)^83 ≤ (14941294086989/25000000000000 : ℝ)^67 := by
    have hnat : (6599978597 : ℕ)^83*25000000000000^67 ≤ 14941294086989^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6599978597 10000000000 14941294086989 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196884383/10000000000 : ℝ), (4721101873/10000000000 : ℝ), (6599978597/10000000000 : ℝ)] ![(96331594573/12500000000000 : ℝ), (9866042721513/25000000000000 : ℝ), (14941294086989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196884383/10000000000 : ℝ)|^83 ≤ (96331594573/12500000000000 : ℝ)^67
        have hw : |(-196884383/10000000000 : ℝ)|=(196884383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4721101873/10000000000 : ℝ)|^83 ≤ (9866042721513/25000000000000 : ℝ)^67
        have hw : |(4721101873/10000000000 : ℝ)|=(4721101873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6599978597/10000000000 : ℝ)|^83 ≤ (14941294086989/25000000000000 : ℝ)^67
        have hw : |(6599978597/10000000000 : ℝ)|=(6599978597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2133152593/5000000000 : ℝ)*x 0 + (-946996747/10000000000 : ℝ)*x 1 + (412670601/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133152593/5000000000 : ℝ)^83 ≤ (34810167151481/100000000000000 : ℝ)^67 := by
    have hnat : (2133152593 : ℕ)^83*100000000000000^67 ≤ 34810167151481^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133152593 5000000000 34810167151481 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946996747/10000000000 : ℝ)^83 ≤ (5393794480861/100000000000000 : ℝ)^67 := by
    have hnat : (946996747 : ℕ)^83*100000000000000^67 ≤ 5393794480861^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946996747 10000000000 5393794480861 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412670601/625000000 : ℝ)^83 ≤ (59796038355253/100000000000000 : ℝ)^67 := by
    have hnat : (412670601 : ℕ)^83*100000000000000^67 ≤ 59796038355253^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412670601 625000000 59796038355253 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133152593/5000000000 : ℝ), (-946996747/10000000000 : ℝ), (412670601/625000000 : ℝ)] ![(34810167151481/100000000000000 : ℝ), (5393794480861/100000000000000 : ℝ), (59796038355253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133152593/5000000000 : ℝ)|^83 ≤ (34810167151481/100000000000000 : ℝ)^67
        have hw : |(2133152593/5000000000 : ℝ)|=(2133152593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946996747/10000000000 : ℝ)|^83 ≤ (5393794480861/100000000000000 : ℝ)^67
        have hw : |(-946996747/10000000000 : ℝ)|=(946996747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412670601/625000000 : ℝ)|^83 ≤ (59796038355253/100000000000000 : ℝ)^67
        have hw : |(412670601/625000000 : ℝ)|=(412670601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3280011573/5000000000 : ℝ)*x 0 + (4785563653/10000000000 : ℝ)*x 1 + (-18742373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3280011573/5000000000 : ℝ)^83 ≤ (59317287264411/100000000000000 : ℝ)^67 := by
    have hnat : (3280011573 : ℕ)^83*100000000000000^67 ≤ 59317287264411^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3280011573 5000000000 59317287264411 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4785563653/10000000000 : ℝ)^83 ≤ (4013277681679/10000000000000 : ℝ)^67 := by
    have hnat : (4785563653 : ℕ)^83*10000000000000^67 ≤ 4013277681679^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785563653 10000000000 4013277681679 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18742373/1250000000 : ℝ)^83 ≤ (549935899943/100000000000000 : ℝ)^67 := by
    have hnat : (18742373 : ℕ)^83*100000000000000^67 ≤ 549935899943^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18742373 1250000000 549935899943 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3280011573/5000000000 : ℝ), (4785563653/10000000000 : ℝ), (-18742373/1250000000 : ℝ)] ![(59317287264411/100000000000000 : ℝ), (4013277681679/10000000000000 : ℝ), (549935899943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3280011573/5000000000 : ℝ)|^83 ≤ (59317287264411/100000000000000 : ℝ)^67
        have hw : |(3280011573/5000000000 : ℝ)|=(3280011573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4785563653/10000000000 : ℝ)|^83 ≤ (4013277681679/10000000000000 : ℝ)^67
        have hw : |(4785563653/10000000000 : ℝ)|=(4785563653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18742373/1250000000 : ℝ)|^83 ≤ (549935899943/100000000000000 : ℝ)^67
        have hw : |(-18742373/1250000000 : ℝ)|=(18742373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6923054989/10000000000 : ℝ)*x 0 + (1708300479/5000000000 : ℝ)*x 1 + (1577901399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6923054989/10000000000 : ℝ)^83 ≤ (1268206379601/2000000000000 : ℝ)^67 := by
    have hnat : (6923054989 : ℕ)^83*2000000000000^67 ≤ 1268206379601^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6923054989 10000000000 1268206379601 2000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708300479/5000000000 : ℝ)^83 ≤ (13218549053949/50000000000000 : ℝ)^67 := by
    have hnat : (1708300479 : ℕ)^83*50000000000000^67 ≤ 13218549053949^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708300479 5000000000 13218549053949 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577901399/10000000000 : ℝ)^83 ≤ (1269072862893/12500000000000 : ℝ)^67 := by
    have hnat : (1577901399 : ℕ)^83*12500000000000^67 ≤ 1269072862893^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577901399 10000000000 1269072862893 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6923054989/10000000000 : ℝ), (1708300479/5000000000 : ℝ), (1577901399/10000000000 : ℝ)] ![(1268206379601/2000000000000 : ℝ), (13218549053949/50000000000000 : ℝ), (1269072862893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6923054989/10000000000 : ℝ)|^83 ≤ (1268206379601/2000000000000 : ℝ)^67
        have hw : |(6923054989/10000000000 : ℝ)|=(6923054989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1708300479/5000000000 : ℝ)|^83 ≤ (13218549053949/50000000000000 : ℝ)^67
        have hw : |(1708300479/5000000000 : ℝ)|=(1708300479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577901399/10000000000 : ℝ)|^83 ≤ (1269072862893/12500000000000 : ℝ)^67
        have hw : |(1577901399/10000000000 : ℝ)|=(1577901399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-74830063/5000000000 : ℝ)*x 0 + (6156274791/10000000000 : ℝ)*x 1 + (651662709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74830063/5000000000 : ℝ)^83 ≤ (548669160169/100000000000000 : ℝ)^67 := by
    have hnat : (74830063 : ℕ)^83*100000000000000^67 ≤ 548669160169^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74830063 5000000000 548669160169 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6156274791/10000000000 : ℝ)^83 ≤ (27414219191853/50000000000000 : ℝ)^67 := by
    have hnat : (6156274791 : ℕ)^83*50000000000000^67 ≤ 27414219191853^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6156274791 10000000000 27414219191853 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651662709/1250000000 : ℝ)^83 ≤ (1394465388857/3125000000000 : ℝ)^67 := by
    have hnat : (651662709 : ℕ)^83*3125000000000^67 ≤ 1394465388857^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651662709 1250000000 1394465388857 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74830063/5000000000 : ℝ), (6156274791/10000000000 : ℝ), (651662709/1250000000 : ℝ)] ![(548669160169/100000000000000 : ℝ), (27414219191853/50000000000000 : ℝ), (1394465388857/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74830063/5000000000 : ℝ)|^83 ≤ (548669160169/100000000000000 : ℝ)^67
        have hw : |(-74830063/5000000000 : ℝ)|=(74830063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6156274791/10000000000 : ℝ)|^83 ≤ (27414219191853/50000000000000 : ℝ)^67
        have hw : |(6156274791/10000000000 : ℝ)|=(6156274791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651662709/1250000000 : ℝ)|^83 ≤ (1394465388857/3125000000000 : ℝ)^67
        have hw : |(651662709/1250000000 : ℝ)|=(651662709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6593256381/10000000000 : ℝ)*x 0 + (-126680007/10000000000 : ℝ)*x 1 + (4759668297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6593256381/10000000000 : ℝ)^83 ≤ (59689776825081/100000000000000 : ℝ)^67 := by
    have hnat : (6593256381 : ℕ)^83*100000000000000^67 ≤ 59689776825081^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6593256381 10000000000 59689776825081 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126680007/10000000000 : ℝ)^83 ≤ (446296458687/100000000000000 : ℝ)^67 := by
    have hnat : (126680007 : ℕ)^83*100000000000000^67 ≤ 446296458687^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126680007 10000000000 446296458687 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4759668297/10000000000 : ℝ)^83 ≤ (2491495419471/6250000000000 : ℝ)^67 := by
    have hnat : (4759668297 : ℕ)^83*6250000000000^67 ≤ 2491495419471^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4759668297 10000000000 2491495419471 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6593256381/10000000000 : ℝ), (-126680007/10000000000 : ℝ), (4759668297/10000000000 : ℝ)] ![(59689776825081/100000000000000 : ℝ), (446296458687/100000000000000 : ℝ), (2491495419471/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6593256381/10000000000 : ℝ)|^83 ≤ (59689776825081/100000000000000 : ℝ)^67
        have hw : |(6593256381/10000000000 : ℝ)|=(6593256381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126680007/10000000000 : ℝ)|^83 ≤ (446296458687/100000000000000 : ℝ)^67
        have hw : |(-126680007/10000000000 : ℝ)|=(126680007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4759668297/10000000000 : ℝ)|^83 ≤ (2491495419471/6250000000000 : ℝ)^67
        have hw : |(4759668297/10000000000 : ℝ)|=(4759668297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (838578173/2000000000 : ℝ)*x 0 + (1335468833/2000000000 : ℝ)*x 1 + (-933126319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838578173/2000000000 : ℝ)^83 ≤ (8517409961113/25000000000000 : ℝ)^67 := by
    have hnat : (838578173 : ℕ)^83*25000000000000^67 ≤ 8517409961113^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838578173 2000000000 8517409961113 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335468833/2000000000 : ℝ)^83 ≤ (60634261492681/100000000000000 : ℝ)^67 := by
    have hnat : (1335468833 : ℕ)^83*100000000000000^67 ≤ 60634261492681^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335468833 2000000000 60634261492681 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933126319/10000000000 : ℝ)^83 ≤ (5296098651163/100000000000000 : ℝ)^67 := by
    have hnat : (933126319 : ℕ)^83*100000000000000^67 ≤ 5296098651163^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933126319 10000000000 5296098651163 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838578173/2000000000 : ℝ), (1335468833/2000000000 : ℝ), (-933126319/10000000000 : ℝ)] ![(8517409961113/25000000000000 : ℝ), (60634261492681/100000000000000 : ℝ), (5296098651163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838578173/2000000000 : ℝ)|^83 ≤ (8517409961113/25000000000000 : ℝ)^67
        have hw : |(838578173/2000000000 : ℝ)|=(838578173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1335468833/2000000000 : ℝ)|^83 ≤ (60634261492681/100000000000000 : ℝ)^67
        have hw : |(1335468833/2000000000 : ℝ)|=(1335468833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-933126319/10000000000 : ℝ)|^83 ≤ (5296098651163/100000000000000 : ℝ)^67
        have hw : |(-933126319/10000000000 : ℝ)|=(933126319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s1_s1_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7110007417/10000000000 : ℝ)*x 0 + (1271189571/5000000000 : ℝ)*x 1 + (2292834599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7110007417/10000000000 : ℝ)^83 ≤ (65538385450791/100000000000000 : ℝ)^67 := by
    have hnat : (7110007417 : ℕ)^83*100000000000000^67 ≤ 65538385450791^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7110007417 10000000000 65538385450791 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271189571/5000000000 : ℝ)^83 ≤ (3666385691879/20000000000000 : ℝ)^67 := by
    have hnat : (1271189571 : ℕ)^83*20000000000000^67 ≤ 3666385691879^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271189571 5000000000 3666385691879 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2292834599/10000000000 : ℝ)^83 ≤ (16129686078379/100000000000000 : ℝ)^67 := by
    have hnat : (2292834599 : ℕ)^83*100000000000000^67 ≤ 16129686078379^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292834599 10000000000 16129686078379 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7110007417/10000000000 : ℝ), (1271189571/5000000000 : ℝ), (2292834599/10000000000 : ℝ)] ![(65538385450791/100000000000000 : ℝ), (3666385691879/20000000000000 : ℝ), (16129686078379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7110007417/10000000000 : ℝ)|^83 ≤ (65538385450791/100000000000000 : ℝ)^67
        have hw : |(7110007417/10000000000 : ℝ)|=(7110007417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271189571/5000000000 : ℝ)|^83 ≤ (3666385691879/20000000000000 : ℝ)^67
        have hw : |(1271189571/5000000000 : ℝ)|=(1271189571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2292834599/10000000000 : ℝ)|^83 ≤ (16129686078379/100000000000000 : ℝ)^67
        have hw : |(2292834599/10000000000 : ℝ)|=(2292834599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322063_s1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17611/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17611/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70227/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33951/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33951/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22899/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22899/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9293/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9293/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (167697/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (17611/25000 : ℝ) ^ (41/8 : ℝ) ≤ (16603534277019225563/100000000000000000000 : ℝ) := by
    have hpowers : (17611/25000 : ℝ)^41 ≤ (16603534277019225563/100000000000000000000 : ℝ)^8 := by
      have hnat : (17611 : ℕ)^41*100000000000000000000^8 ≤ 16603534277019225563^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17611 25000 16603534277019225563 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17611/25000 : ℝ)) (X := (16603534277019225563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (116603534277019225563/100000000000000000000 : ℝ) ≤ (2576065661044589/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (116603534277019225563/100000000000000000000 : ℝ)^8 ≤ (2576065661044589/2500000000000000 : ℝ)^41 := by
      have hnat : (116603534277019225563 : ℕ)^8*2500000000000000^41 ≤ 2576065661044589^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116603534277019225563 100000000000000000000 2576065661044589 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2576065661044589/2500000000000000 : ℝ)) (X := (116603534277019225563/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (66603534277019225563/50000000000000000000 : ℝ) ≤ (5287714624495531/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (66603534277019225563/50000000000000000000 : ℝ)^8 ≤ (5287714624495531/5000000000000000 : ℝ)^41 := by
      have hnat : (66603534277019225563 : ℕ)^8*5000000000000000^41 ≤ 5287714624495531^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66603534277019225563 50000000000000000000 5287714624495531 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5287714624495531/5000000000000000 : ℝ)) (X := (66603534277019225563/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(76065661044589/1761100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(135583302406353/3522200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (17611/25000 : ℝ)) (alpha := (76065661044589/1761100000000000 : ℝ)) (beta := (135583302406353/3522200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17611/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(76065661044589/1761100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(135583302406353/3522200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (70227/100000 : ℝ) ^ (41/8 : ℝ) ≤ (2042883540463682773/12500000000000000000 : ℝ) := by
    have hpowers : (70227/100000 : ℝ)^41 ≤ (2042883540463682773/12500000000000000000 : ℝ)^8 := by
      have hnat : (70227 : ℕ)^41*12500000000000000000^8 ≤ 2042883540463682773^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70227 100000 2042883540463682773 12500000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70227/100000 : ℝ)) (X := (2042883540463682773/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (14542883540463682773/12500000000000000000 : ℝ) ≤ (5149883701172253/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (14542883540463682773/12500000000000000000 : ℝ)^8 ≤ (5149883701172253/5000000000000000 : ℝ)^41 := by
      have hnat : (14542883540463682773 : ℕ)^8*5000000000000000^41 ≤ 5149883701172253^41*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14542883540463682773 12500000000000000000 5149883701172253 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5149883701172253/5000000000000000 : ℝ)) (X := (14542883540463682773/12500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (8292883540463682773/6250000000000000000 : ℝ) ≤ (2113469362153753/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (8292883540463682773/6250000000000000000 : ℝ)^8 ≤ (2113469362153753/2000000000000000 : ℝ)^41 := by
      have hnat : (8292883540463682773 : ℕ)^8*2000000000000000^41 ≤ 2113469362153753^41*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8292883540463682773 6250000000000000000 2113469362153753 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2113469362153753/2000000000000000 : ℝ)) (X := (8292883540463682773/6250000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(149883701172253/3511350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(15739965201427/413100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (70227/100000 : ℝ)) (alpha := (149883701172253/3511350000000000 : ℝ)) (beta := (15739965201427/413100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (70227/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(149883701172253/3511350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(15739965201427/413100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (33951/50000 : ℝ) ^ (41/8 : ℝ) ≤ (2750604491396057751/20000000000000000000 : ℝ) := by
    have hpowers : (33951/50000 : ℝ)^41 ≤ (2750604491396057751/20000000000000000000 : ℝ)^8 := by
      have hnat : (33951 : ℕ)^41*20000000000000000000^8 ≤ 2750604491396057751^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33951 50000 2750604491396057751 20000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33951/50000 : ℝ)) (X := (2750604491396057751/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (22750604491396057751/20000000000000000000 : ℝ) ≤ (512731032359923/500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (22750604491396057751/20000000000000000000 : ℝ)^8 ≤ (512731032359923/500000000000000 : ℝ)^41 := by
      have hnat : (22750604491396057751 : ℕ)^8*500000000000000^41 ≤ 512731032359923^41*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22750604491396057751 20000000000000000000 512731032359923 500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (512731032359923/500000000000000 : ℝ)) (X := (22750604491396057751/20000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12750604491396057751/10000000000000000000 : ℝ) ≤ (10485553746104107/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (12750604491396057751/10000000000000000000 : ℝ)^8 ≤ (10485553746104107/10000000000000000 : ℝ)^41 := by
      have hnat : (12750604491396057751 : ℕ)^8*10000000000000000^41 ≤ 10485553746104107^41*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12750604491396057751 10000000000000000000 10485553746104107 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10485553746104107/10000000000000000 : ℝ)) (X := (12750604491396057751/10000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(12731032359923/339510000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(230933098905647/6790200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (33951/50000 : ℝ)) (alpha := (12731032359923/339510000000000 : ℝ)) (beta := (230933098905647/6790200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (33951/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(12731032359923/339510000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(230933098905647/6790200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-114259071/1250000000 : ℝ)*X 0 0+(21764519/40000000 : ℝ)*X 0 1+(1377416419/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5440879533/10000000000 : ℝ)*X 1 0+(-910459089/10000000000 : ℝ)*X 1 1+(689033361/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2737656999/5000000000 : ℝ)*X 2 0+(550208519/1000000000 : ℝ)*X 2 1+(-873111333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4204871659/10000000000 : ℝ)*X 0 0+(2068409887/5000000000 : ℝ)*X 0 1+(2008274303/5000000000 : ℝ)*X 0 2+(4204871659/10000000000 : ℝ)*X 1 0+(2068409887/5000000000 : ℝ)*X 1 1+(2008274303/5000000000 : ℝ)*X 1 2+(4204871659/10000000000 : ℝ)*X 2 0+(2068409887/5000000000 : ℝ)*X 2 1+(2008274303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-462842543/5000000000 : ℝ)*X 0 0+(432009677/1000000000 : ℝ)*X 0 1+(6567537573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4755603903/10000000000 : ℝ)*X 1 0+(-38366019/2000000000 : ℝ)*X 1 1+(657026367/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4460929949/10000000000 : ℝ)*X 2 0+(274627699/400000000 : ℝ)*X 2 1+(-63982529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2171554711/5000000000 : ℝ)*X 0 0+(6101183367/10000000000 : ℝ)*X 0 1+(1582666641/10000000000 : ℝ)*X 0 2+(2171554711/5000000000 : ℝ)*X 1 0+(6101183367/10000000000 : ℝ)*X 1 1+(1582666641/10000000000 : ℝ)*X 1 2+(2171554711/5000000000 : ℝ)*X 2 0+(6101183367/10000000000 : ℝ)*X 2 1+(1582666641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-196884383/10000000000 : ℝ)*X 0 0+(4721101873/10000000000 : ℝ)*X 0 1+(6599978597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2133152593/5000000000 : ℝ)*X 1 0+(-946996747/10000000000 : ℝ)*X 1 1+(412670601/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3280011573/5000000000 : ℝ)*X 2 0+(4785563653/10000000000 : ℝ)*X 2 1+(-18742373/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((6923054989/10000000000 : ℝ)*X 0 0+(1708300479/5000000000 : ℝ)*X 0 1+(1577901399/10000000000 : ℝ)*X 0 2+(6923054989/10000000000 : ℝ)*X 1 0+(1708300479/5000000000 : ℝ)*X 1 1+(1577901399/10000000000 : ℝ)*X 1 2+(6923054989/10000000000 : ℝ)*X 2 0+(1708300479/5000000000 : ℝ)*X 2 1+(1577901399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-74830063/5000000000 : ℝ)*X 0 0+(6156274791/10000000000 : ℝ)*X 0 1+(651662709/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6593256381/10000000000 : ℝ)*X 1 0+(-126680007/10000000000 : ℝ)*X 1 1+(4759668297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((838578173/2000000000 : ℝ)*X 2 0+(1335468833/2000000000 : ℝ)*X 2 1+(-933126319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7110007417/10000000000 : ℝ)*X 0 0+(1271189571/5000000000 : ℝ)*X 0 1+(2292834599/10000000000 : ℝ)*X 0 2+(7110007417/10000000000 : ℝ)*X 1 0+(1271189571/5000000000 : ℝ)*X 1 1+(2292834599/10000000000 : ℝ)*X 1 2+(7110007417/10000000000 : ℝ)*X 2 0+(1271189571/5000000000 : ℝ)*X 2 1+(2292834599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((22899/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22899/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (668118896284045591119121823273/38879166741525000000000000000000000 : ℝ) := by norm_num
    linear_combination (265197852713/1000000000000 : ℝ)*(base7) + (354409/200000000000 : ℝ)*(base50) + (76900330241/500000000000 : ℝ)*(base60) + (3237605779643/1000000000000 : ℝ)*(major_s1_0) + (3237605779643/1000000000000 : ℝ)*(major_s1_1) + (3237605779643/1000000000000 : ℝ)*(major_s1_2) + (32626241/1000000000000 : ℝ)*(sp_s1_0) + (5036467/1000000000000 : ℝ)*(sp_s1_6) + (1162295712589/250000000000 : ℝ)*(sp_s1_7) + (4649360012997/1000000000000 : ℝ)*(sp_s1_8) + (290584699327/62500000000 : ℝ)*(sp_s1_9) + (485698921669/250000000000 : ℝ)*(sp_s1_13) + (361341/2500000000 : ℝ)*(sp_s1_14) + (1205941/250000000000 : ℝ)*(sp_s1_23) + (167760287043/100000000000 : ℝ)*(f.failure) + (4649360012997/1000000000000 : ℝ)*(f.sum) + (30497854087817775053/39737947950000000000000000000000 : ℝ)*base63 + (1947652373908379/6790200000000000000000000000 : ℝ)*base64 + (73363274568259/413100000000000000000000000 : ℝ)*base66 + (211498523391973/339510000000000000000000000 : ℝ)*base69 + (7374088611146903623/23916442440000000000000000000000 : ℝ)*base70 + (175950343191781/3522200000000000000000000000 : ℝ)*base72 + (613198408027631/877837500000000000000000000 : ℝ)*base75 + (1365615462832627/1761100000000000000000000000 : ℝ)*base77 + (1905781901595234929/14550208200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (143/1000000000000000 : ℝ)*base86 + (143/1000000000000000 : ℝ)*base88 + (143/1000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9293/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9293/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (212336832209603963327268919141/15551666696610000000000000000000000 : ℝ) := by norm_num
    linear_combination (63832255729/200000000000 : ℝ)*(base7) + (8753/8000000000 : ℝ)*(base49) + (1554994682299/500000000000 : ℝ)*(major_s1_0) + (1554994682299/500000000000 : ℝ)*(major_s1_1) + (1554994682299/500000000000 : ℝ)*(major_s1_2) + (1225119/125000000000 : ℝ)*(sp_s1_1) + (1410859/1000000000000 : ℝ)*(sp_s1_2) + (81225757/1000000000000 : ℝ)*(sp_s1_8) + (4430087993273/1000000000000 : ℝ)*(sp_s1_14) + (2214999119373/500000000000 : ℝ)*(sp_s1_15) + (1107521963649/250000000000 : ℝ)*(sp_s1_16) + (1930602439189/1000000000000 : ℝ)*(sp_s1_20) + (1272181/1000000000000 : ℝ)*(sp_s1_21) + (35788831/1000000000000 : ℝ)*(sp_s1_27) + (2578363119/1600000000 : ℝ)*(f.failure) + (886017853091/200000000000 : ℝ)*(f.sum) + (129269874412706857/39737947950000000000000000000000 : ℝ)*base62 + (1538788031108813/3395100000000000000000000000 : ℝ)*base65 + (69999406673129/103275000000000000000000000 : ℝ)*base67 + (5217512333687/339510000000000000000000000 : ℝ)*base68 + (178763181121584017/11958221220000000000000000000000 : ℝ)*base70 + (207395401177473/1761100000000000000000000000 : ℝ)*base72 + (48107765019677/438918750000000000000000000 : ℝ)*base74 + (59578959716299/880550000000000000000000000 : ℝ)*base76 + (1374726858566544773/7275104100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (13/16000000000000 : ℝ)*base87 + (13/16000000000000 : ℝ)*base89 + (13/16000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5537167801612132383266207664281/466550000898300000000000000000000000 : ℝ) := by norm_num
    linear_combination (80279510869/250000000000 : ℝ)*(base7) + (93641550421/500000000000 : ℝ)*(base40) + (220001/125000000000 : ℝ)*(base49) + (2890404394231/1000000000000 : ℝ)*(major_s1_0) + (2890404394231/1000000000000 : ℝ)*(major_s1_1) + (2890404394231/1000000000000 : ℝ)*(major_s1_2) + (2787447/200000000000 : ℝ)*(sp_s1_1) + (36442781/1000000000000 : ℝ)*(sp_s1_2) + (93677769/1000000000000 : ℝ)*(sp_s1_9) + (1014733/50000000000 : ℝ)*(sp_s1_20) + (820721319851/200000000000 : ℝ)*(sp_s1_21) + (205179633101/50000000000 : ℝ)*(sp_s1_22) + (820695295741/200000000000 : ℝ)*(sp_s1_23) + (909397103391/500000000000 : ℝ)*(sp_s1_27) + (1497696457967/1000000000000 : ℝ)*(f.failure) + (820721319851/200000000000 : ℝ)*(f.sum) + (168978262473865487/310452718359375000000000000000 : ℝ)*base63 + (4427744148310877/6790200000000000000000000000 : ℝ)*base65 + (39325595353057/413100000000000000000000000 : ℝ)*base67 + (157442867780977/169755000000000000000000000 : ℝ)*base69 + (6530723275015316053/23916442440000000000000000000000 : ℝ)*base71 + (1861350722330383/3522200000000000000000000000 : ℝ)*base73 + (3453321902505913/3511350000000000000000000000 : ℝ)*base75 + (1162559957437519/1761100000000000000000000000 : ℝ)*base77 + (5459024667743841613/14550208200000000000000000000000 : ℝ)*base78 + (4867/10000000000000000 : ℝ)*base86 + (4867/10000000000000000 : ℝ)*base88 + (4867/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17611/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17611/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70227/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33951/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33951/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22899/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22899/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9293/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9293/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c322063_s1 p hpa hpb X hX hprev0

#print axioms solution

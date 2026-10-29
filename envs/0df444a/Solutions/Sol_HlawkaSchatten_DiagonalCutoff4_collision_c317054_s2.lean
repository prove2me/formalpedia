-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:55.933545+00:00
-- url     : https://prove2.me/submissions/1710d61e-f368-496a-ad7c-39090c81f9c3

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
theorem collision_support_c317054_s2_s2_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1347327537/10000000000 : ℝ)*x 0 + (141501253/312500000 : ℝ)*x 1 + (-1555759169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347327537/10000000000 : ℝ)^39 ≤ (64255616099/800000000000 : ℝ)^31 := by
    have hnat : (1347327537 : ℕ)^39*800000000000^31 ≤ 64255616099^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347327537 10000000000 64255616099 800000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141501253/312500000 : ℝ)^39 ≤ (36907354188379/100000000000000 : ℝ)^31 := by
    have hnat : (141501253 : ℕ)^39*100000000000000^31 ≤ 36907354188379^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141501253 312500000 36907354188379 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1555759169/2500000000 : ℝ)^39 ≤ (27530346894511/50000000000000 : ℝ)^31 := by
    have hnat : (1555759169 : ℕ)^39*50000000000000^31 ≤ 27530346894511^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555759169 2500000000 27530346894511 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1347327537/10000000000 : ℝ), (141501253/312500000 : ℝ), (-1555759169/2500000000 : ℝ)] ![(64255616099/800000000000 : ℝ), (36907354188379/100000000000000 : ℝ), (27530346894511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1347327537/10000000000 : ℝ)|^39 ≤ (64255616099/800000000000 : ℝ)^31
        have hw : |(-1347327537/10000000000 : ℝ)|=(1347327537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141501253/312500000 : ℝ)|^39 ≤ (36907354188379/100000000000000 : ℝ)^31
        have hw : |(141501253/312500000 : ℝ)|=(141501253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1555759169/2500000000 : ℝ)|^39 ≤ (27530346894511/50000000000000 : ℝ)^31
        have hw : |(-1555759169/2500000000 : ℝ)|=(1555759169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5066199297/10000000000 : ℝ)*x 0 + (1262236493/2500000000 : ℝ)*x 1 + (1116518533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5066199297/10000000000 : ℝ)^39 ≤ (2125402796327/5000000000000 : ℝ)^31 := by
    have hnat : (5066199297 : ℕ)^39*5000000000000^31 ≤ 2125402796327^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066199297 10000000000 2125402796327 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262236493/2500000000 : ℝ)^39 ≤ (42326013068713/100000000000000 : ℝ)^31 := by
    have hnat : (1262236493 : ℕ)^39*100000000000000^31 ≤ 42326013068713^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262236493 2500000000 42326013068713 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116518533/5000000000 : ℝ)^39 ≤ (7582965498621/50000000000000 : ℝ)^31 := by
    have hnat : (1116518533 : ℕ)^39*50000000000000^31 ≤ 7582965498621^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116518533 5000000000 7582965498621 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5066199297/10000000000 : ℝ), (1262236493/2500000000 : ℝ), (1116518533/5000000000 : ℝ)] ![(2125402796327/5000000000000 : ℝ), (42326013068713/100000000000000 : ℝ), (7582965498621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5066199297/10000000000 : ℝ)|^39 ≤ (2125402796327/5000000000000 : ℝ)^31
        have hw : |(5066199297/10000000000 : ℝ)|=(5066199297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1262236493/2500000000 : ℝ)|^39 ≤ (42326013068713/100000000000000 : ℝ)^31
        have hw : |(1262236493/2500000000 : ℝ)|=(1262236493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1116518533/5000000000 : ℝ)|^39 ≤ (7582965498621/50000000000000 : ℝ)^31
        have hw : |(1116518533/5000000000 : ℝ)|=(1116518533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2558522211/5000000000 : ℝ)*x 0 + (637819183/1250000000 : ℝ)*x 1 + (-525721827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2558522211/5000000000 : ℝ)^39 ≤ (43045461120179/100000000000000 : ℝ)^31 := by
    have hnat : (2558522211 : ℕ)^39*100000000000000^31 ≤ 43045461120179^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558522211 5000000000 43045461120179 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (637819183/1250000000 : ℝ)^39 ≤ (42892158578989/100000000000000 : ℝ)^31 := by
    have hnat : (637819183 : ℕ)^39*100000000000000^31 ≤ 42892158578989^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637819183 1250000000 42892158578989 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525721827/2500000000 : ℝ)^39 ≤ (14062380292417/100000000000000 : ℝ)^31 := by
    have hnat : (525721827 : ℕ)^39*100000000000000^31 ≤ 14062380292417^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525721827 2500000000 14062380292417 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2558522211/5000000000 : ℝ), (637819183/1250000000 : ℝ), (-525721827/2500000000 : ℝ)] ![(43045461120179/100000000000000 : ℝ), (42892158578989/100000000000000 : ℝ), (14062380292417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2558522211/5000000000 : ℝ)|^39 ≤ (43045461120179/100000000000000 : ℝ)^31
        have hw : |(2558522211/5000000000 : ℝ)|=(2558522211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(637819183/1250000000 : ℝ)|^39 ≤ (42892158578989/100000000000000 : ℝ)^31
        have hw : |(637819183/1250000000 : ℝ)|=(637819183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525721827/2500000000 : ℝ)|^39 ≤ (14062380292417/100000000000000 : ℝ)^31
        have hw : |(-525721827/2500000000 : ℝ)|=(525721827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1329617753/10000000000 : ℝ)*x 0 + (4439460191/10000000000 : ℝ)*x 1 + (-1579041009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1329617753/10000000000 : ℝ)^39 ≤ (7899357828647/100000000000000 : ℝ)^31 := by
    have hnat : (1329617753 : ℕ)^39*100000000000000^31 ≤ 7899357828647^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329617753 10000000000 7899357828647 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4439460191/10000000000 : ℝ)^39 ≤ (7200266840253/20000000000000 : ℝ)^31 := by
    have hnat : (4439460191 : ℕ)^39*20000000000000^31 ≤ 7200266840253^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439460191 10000000000 7200266840253 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1579041009/2500000000 : ℝ)^39 ≤ (56099307956843/100000000000000 : ℝ)^31 := by
    have hnat : (1579041009 : ℕ)^39*100000000000000^31 ≤ 56099307956843^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579041009 2500000000 56099307956843 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1329617753/10000000000 : ℝ), (4439460191/10000000000 : ℝ), (-1579041009/2500000000 : ℝ)] ![(7899357828647/100000000000000 : ℝ), (7200266840253/20000000000000 : ℝ), (56099307956843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1329617753/10000000000 : ℝ)|^39 ≤ (7899357828647/100000000000000 : ℝ)^31
        have hw : |(-1329617753/10000000000 : ℝ)|=(1329617753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4439460191/10000000000 : ℝ)|^39 ≤ (7200266840253/20000000000000 : ℝ)^31
        have hw : |(4439460191/10000000000 : ℝ)|=(4439460191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1579041009/2500000000 : ℝ)|^39 ≤ (56099307956843/100000000000000 : ℝ)^31
        have hw : |(-1579041009/2500000000 : ℝ)|=(1579041009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (339293637/625000000 : ℝ)*x 0 + (-2126065573/10000000000 : ℝ)*x 1 + (-2383447349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339293637/625000000 : ℝ)^39 ≤ (2318462499617/5000000000000 : ℝ)^31 := by
    have hnat : (339293637 : ℕ)^39*5000000000000^31 ≤ 2318462499617^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339293637 625000000 2318462499617 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126065573/10000000000 : ℝ)^39 ≤ (2851530660507/20000000000000 : ℝ)^31 := by
    have hnat : (2126065573 : ℕ)^39*20000000000000^31 ≤ 2851530660507^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126065573 10000000000 2851530660507 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383447349/5000000000 : ℝ)^39 ≤ (39373096695261/100000000000000 : ℝ)^31 := by
    have hnat : (2383447349 : ℕ)^39*100000000000000^31 ≤ 39373096695261^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383447349 5000000000 39373096695261 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339293637/625000000 : ℝ), (-2126065573/10000000000 : ℝ), (-2383447349/5000000000 : ℝ)] ![(2318462499617/5000000000000 : ℝ), (2851530660507/20000000000000 : ℝ), (39373096695261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339293637/625000000 : ℝ)|^39 ≤ (2318462499617/5000000000000 : ℝ)^31
        have hw : |(339293637/625000000 : ℝ)|=(339293637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126065573/10000000000 : ℝ)|^39 ≤ (2851530660507/20000000000000 : ℝ)^31
        have hw : |(-2126065573/10000000000 : ℝ)|=(2126065573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2383447349/5000000000 : ℝ)|^39 ≤ (39373096695261/100000000000000 : ℝ)^31
        have hw : |(-2383447349/5000000000 : ℝ)|=(2383447349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5016877657/10000000000 : ℝ)*x 0 + (5244512739/10000000000 : ℝ)*x 1 + (512327879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5016877657/10000000000 : ℝ)^39 ≤ (41988081269359/100000000000000 : ℝ)^31 := by
    have hnat : (5016877657 : ℕ)^39*100000000000000^31 ≤ 41988081269359^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016877657 10000000000 41988081269359 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244512739/10000000000 : ℝ)^39 ≤ (22199387536473/50000000000000 : ℝ)^31 := by
    have hnat : (5244512739 : ℕ)^39*50000000000000^31 ≤ 22199387536473^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244512739 10000000000 22199387536473 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512327879/2500000000 : ℝ)^39 ≤ (6806571821919/50000000000000 : ℝ)^31 := by
    have hnat : (512327879 : ℕ)^39*50000000000000^31 ≤ 6806571821919^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512327879 2500000000 6806571821919 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5016877657/10000000000 : ℝ), (5244512739/10000000000 : ℝ), (512327879/2500000000 : ℝ)] ![(41988081269359/100000000000000 : ℝ), (22199387536473/50000000000000 : ℝ), (6806571821919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5016877657/10000000000 : ℝ)|^39 ≤ (41988081269359/100000000000000 : ℝ)^31
        have hw : |(5016877657/10000000000 : ℝ)|=(5016877657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244512739/10000000000 : ℝ)|^39 ≤ (22199387536473/50000000000000 : ℝ)^31
        have hw : |(5244512739/10000000000 : ℝ)|=(5244512739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512327879/2500000000 : ℝ)|^39 ≤ (6806571821919/50000000000000 : ℝ)^31
        have hw : |(512327879/2500000000 : ℝ)|=(512327879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2553270897/5000000000 : ℝ)*x 0 + (529889529/1000000000 : ℝ)*x 1 + (-1864482667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2553270897/5000000000 : ℝ)^39 ≤ (429343406723/1000000000000 : ℝ)^31 := by
    have hnat : (2553270897 : ℕ)^39*1000000000000^31 ≤ 429343406723^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553270897 5000000000 429343406723 1000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529889529/1000000000 : ℝ)^39 ≤ (44978747763703/100000000000000 : ℝ)^31 := by
    have hnat : (529889529 : ℕ)^39*100000000000000^31 ≤ 44978747763703^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529889529 1000000000 44978747763703 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864482667/10000000000 : ℝ)^39 ≤ (483476461939/4000000000000 : ℝ)^31 := by
    have hnat : (1864482667 : ℕ)^39*4000000000000^31 ≤ 483476461939^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864482667 10000000000 483476461939 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2553270897/5000000000 : ℝ), (529889529/1000000000 : ℝ), (-1864482667/10000000000 : ℝ)] ![(429343406723/1000000000000 : ℝ), (44978747763703/100000000000000 : ℝ), (483476461939/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2553270897/5000000000 : ℝ)|^39 ≤ (429343406723/1000000000000 : ℝ)^31
        have hw : |(2553270897/5000000000 : ℝ)|=(2553270897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529889529/1000000000 : ℝ)|^39 ≤ (44978747763703/100000000000000 : ℝ)^31
        have hw : |(529889529/1000000000 : ℝ)|=(529889529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1864482667/10000000000 : ℝ)|^39 ≤ (483476461939/4000000000000 : ℝ)^31
        have hw : |(-1864482667/10000000000 : ℝ)|=(1864482667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-604594607/5000000000 : ℝ)*x 0 + (4538992597/10000000000 : ℝ)*x 1 + (-6304615127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (604594607/5000000000 : ℝ)^39 ≤ (701000924867/10000000000000 : ℝ)^31 := by
    have hnat : (604594607 : ℕ)^39*10000000000000^31 ≤ 701000924867^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604594607 5000000000 701000924867 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538992597/10000000000 : ℝ)^39 ≤ (37019699332831/100000000000000 : ℝ)^31 := by
    have hnat : (4538992597 : ℕ)^39*100000000000000^31 ≤ 37019699332831^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538992597 10000000000 37019699332831 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6304615127/10000000000 : ℝ)^39 ≤ (55970291398137/100000000000000 : ℝ)^31 := by
    have hnat : (6304615127 : ℕ)^39*100000000000000^31 ≤ 55970291398137^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6304615127 10000000000 55970291398137 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-604594607/5000000000 : ℝ), (4538992597/10000000000 : ℝ), (-6304615127/10000000000 : ℝ)] ![(701000924867/10000000000000 : ℝ), (37019699332831/100000000000000 : ℝ), (55970291398137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-604594607/5000000000 : ℝ)|^39 ≤ (701000924867/10000000000000 : ℝ)^31
        have hw : |(-604594607/5000000000 : ℝ)|=(604594607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538992597/10000000000 : ℝ)|^39 ≤ (37019699332831/100000000000000 : ℝ)^31
        have hw : |(4538992597/10000000000 : ℝ)|=(4538992597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6304615127/10000000000 : ℝ)|^39 ≤ (55970291398137/100000000000000 : ℝ)^31
        have hw : |(-6304615127/10000000000 : ℝ)|=(6304615127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5334209073/10000000000 : ℝ)*x 0 + (-2238260451/10000000000 : ℝ)*x 1 + (-4772681963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334209073/10000000000 : ℝ)^39 ≤ (45356182497361/100000000000000 : ℝ)^31 := by
    have hnat : (5334209073 : ℕ)^39*100000000000000^31 ≤ 45356182497361^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334209073 10000000000 45356182497361 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238260451/10000000000 : ℝ)^39 ≤ (7605287292011/50000000000000 : ℝ)^31 := by
    have hnat : (2238260451 : ℕ)^39*50000000000000^31 ≤ 7605287292011^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238260451 10000000000 7605287292011 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772681963/10000000000 : ℝ)^39 ≤ (7886648582121/20000000000000 : ℝ)^31 := by
    have hnat : (4772681963 : ℕ)^39*20000000000000^31 ≤ 7886648582121^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772681963 10000000000 7886648582121 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334209073/10000000000 : ℝ), (-2238260451/10000000000 : ℝ), (-4772681963/10000000000 : ℝ)] ![(45356182497361/100000000000000 : ℝ), (7605287292011/50000000000000 : ℝ), (7886648582121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334209073/10000000000 : ℝ)|^39 ≤ (45356182497361/100000000000000 : ℝ)^31
        have hw : |(5334209073/10000000000 : ℝ)|=(5334209073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2238260451/10000000000 : ℝ)|^39 ≤ (7605287292011/50000000000000 : ℝ)^31
        have hw : |(-2238260451/10000000000 : ℝ)|=(2238260451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4772681963/10000000000 : ℝ)|^39 ≤ (7886648582121/20000000000000 : ℝ)^31
        have hw : |(-4772681963/10000000000 : ℝ)|=(4772681963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5265328357/10000000000 : ℝ)*x 0 + (500039623/1000000000 : ℝ)*x 1 + (255440531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265328357/10000000000 : ℝ)^39 ≤ (44620584606161/100000000000000 : ℝ)^31 := by
    have hnat : (5265328357 : ℕ)^39*100000000000000^31 ≤ 44620584606161^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265328357 10000000000 44620584606161 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500039623/1000000000 : ℝ)^39 ≤ (41814618626687/100000000000000 : ℝ)^31 := by
    have hnat : (500039623 : ℕ)^39*100000000000000^31 ≤ 41814618626687^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500039623 1000000000 41814618626687 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255440531/1250000000 : ℝ)^39 ≤ (13564796751563/100000000000000 : ℝ)^31 := by
    have hnat : (255440531 : ℕ)^39*100000000000000^31 ≤ 13564796751563^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255440531 1250000000 13564796751563 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265328357/10000000000 : ℝ), (500039623/1000000000 : ℝ), (255440531/1250000000 : ℝ)] ![(44620584606161/100000000000000 : ℝ), (41814618626687/100000000000000 : ℝ), (13564796751563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265328357/10000000000 : ℝ)|^39 ≤ (44620584606161/100000000000000 : ℝ)^31
        have hw : |(5265328357/10000000000 : ℝ)|=(5265328357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500039623/1000000000 : ℝ)|^39 ≤ (41814618626687/100000000000000 : ℝ)^31
        have hw : |(500039623/1000000000 : ℝ)|=(500039623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(255440531/1250000000 : ℝ)|^39 ≤ (13564796751563/100000000000000 : ℝ)^31
        have hw : |(255440531/1250000000 : ℝ)|=(255440531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5302302951/10000000000 : ℝ)*x 0 + (5079907821/10000000000 : ℝ)*x 1 + (-1894477831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302302951/10000000000 : ℝ)^39 ≤ (45015140721169/100000000000000 : ℝ)^31 := by
    have hnat : (5302302951 : ℕ)^39*100000000000000^31 ≤ 45015140721169^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302302951 10000000000 45015140721169 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079907821/10000000000 : ℝ)^39 ≤ (21326405548847/50000000000000 : ℝ)^31 := by
    have hnat : (5079907821 : ℕ)^39*50000000000000^31 ≤ 21326405548847^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079907821 10000000000 21326405548847 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894477831/10000000000 : ℝ)^39 ≤ (3083012040041/25000000000000 : ℝ)^31 := by
    have hnat : (1894477831 : ℕ)^39*25000000000000^31 ≤ 3083012040041^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894477831 10000000000 3083012040041 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302302951/10000000000 : ℝ), (5079907821/10000000000 : ℝ), (-1894477831/10000000000 : ℝ)] ![(45015140721169/100000000000000 : ℝ), (21326405548847/50000000000000 : ℝ), (3083012040041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302302951/10000000000 : ℝ)|^39 ≤ (45015140721169/100000000000000 : ℝ)^31
        have hw : |(5302302951/10000000000 : ℝ)|=(5302302951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079907821/10000000000 : ℝ)|^39 ≤ (21326405548847/50000000000000 : ℝ)^31
        have hw : |(5079907821/10000000000 : ℝ)|=(5079907821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1894477831/10000000000 : ℝ)|^39 ≤ (3083012040041/25000000000000 : ℝ)^31
        have hw : |(-1894477831/10000000000 : ℝ)|=(1894477831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1123822701/10000000000 : ℝ)*x 0 + (4715320213/10000000000 : ℝ)*x 1 + (-619680841/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123822701/10000000000 : ℝ)^39 ≤ (6393174929733/100000000000000 : ℝ)^31 := by
    have hnat : (1123822701 : ℕ)^39*100000000000000^31 ≤ 6393174929733^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123822701 10000000000 6393174929733 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4715320213/10000000000 : ℝ)^39 ≤ (38837924575719/100000000000000 : ℝ)^31 := by
    have hnat : (4715320213 : ℕ)^39*100000000000000^31 ≤ 38837924575719^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715320213 10000000000 38837924575719 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (619680841/1000000000 : ℝ)^39 ≤ (2738445024409/5000000000000 : ℝ)^31 := by
    have hnat : (619680841 : ℕ)^39*5000000000000^31 ≤ 2738445024409^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619680841 1000000000 2738445024409 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1123822701/10000000000 : ℝ), (4715320213/10000000000 : ℝ), (-619680841/1000000000 : ℝ)] ![(6393174929733/100000000000000 : ℝ), (38837924575719/100000000000000 : ℝ), (2738445024409/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1123822701/10000000000 : ℝ)|^39 ≤ (6393174929733/100000000000000 : ℝ)^31
        have hw : |(-1123822701/10000000000 : ℝ)|=(1123822701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4715320213/10000000000 : ℝ)|^39 ≤ (38837924575719/100000000000000 : ℝ)^31
        have hw : |(4715320213/10000000000 : ℝ)|=(4715320213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-619680841/1000000000 : ℝ)|^39 ≤ (2738445024409/5000000000000 : ℝ)^31
        have hw : |(-619680841/1000000000 : ℝ)|=(619680841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5688948267/10000000000 : ℝ)*x 0 + (-424057209/2000000000 : ℝ)*x 1 + (-4498837899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5688948267/10000000000 : ℝ)^39 ≤ (49182933904157/100000000000000 : ℝ)^31 := by
    have hnat : (5688948267 : ℕ)^39*100000000000000^31 ≤ 49182933904157^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688948267 10000000000 49182933904157 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424057209/2000000000 : ℝ)^39 ≤ (355222752061/2500000000000 : ℝ)^31 := by
    have hnat : (424057209 : ℕ)^39*2500000000000^31 ≤ 355222752061^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424057209 2000000000 355222752061 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498837899/10000000000 : ℝ)^39 ≤ (18304077999991/50000000000000 : ℝ)^31 := by
    have hnat : (4498837899 : ℕ)^39*50000000000000^31 ≤ 18304077999991^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498837899 10000000000 18304077999991 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5688948267/10000000000 : ℝ), (-424057209/2000000000 : ℝ), (-4498837899/10000000000 : ℝ)] ![(49182933904157/100000000000000 : ℝ), (355222752061/2500000000000 : ℝ), (18304077999991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5688948267/10000000000 : ℝ)|^39 ≤ (49182933904157/100000000000000 : ℝ)^31
        have hw : |(5688948267/10000000000 : ℝ)|=(5688948267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424057209/2000000000 : ℝ)|^39 ≤ (355222752061/2500000000000 : ℝ)^31
        have hw : |(-424057209/2000000000 : ℝ)|=(424057209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4498837899/10000000000 : ℝ)|^39 ≤ (18304077999991/50000000000000 : ℝ)^31
        have hw : |(-4498837899/10000000000 : ℝ)|=(4498837899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2527713169/5000000000 : ℝ)*x 0 + (1007617347/2000000000 : ℝ)*x 1 + (1129850921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2527713169/5000000000 : ℝ)^39 ≤ (42394369752071/100000000000000 : ℝ)^31 := by
    have hnat : (2527713169 : ℕ)^39*100000000000000^31 ≤ 42394369752071^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527713169 5000000000 42394369752071 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007617347/2000000000 : ℝ)^39 ≤ (4221151761141/10000000000000 : ℝ)^31 := by
    have hnat : (1007617347 : ℕ)^39*10000000000000^31 ≤ 4221151761141^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007617347 2000000000 4221151761141 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129850921/5000000000 : ℝ)^39 ≤ (15394112623223/100000000000000 : ℝ)^31 := by
    have hnat : (1129850921 : ℕ)^39*100000000000000^31 ≤ 15394112623223^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129850921 5000000000 15394112623223 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2527713169/5000000000 : ℝ), (1007617347/2000000000 : ℝ), (1129850921/5000000000 : ℝ)] ![(42394369752071/100000000000000 : ℝ), (4221151761141/10000000000000 : ℝ), (15394112623223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2527713169/5000000000 : ℝ)|^39 ≤ (42394369752071/100000000000000 : ℝ)^31
        have hw : |(2527713169/5000000000 : ℝ)|=(2527713169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007617347/2000000000 : ℝ)|^39 ≤ (4221151761141/10000000000000 : ℝ)^31
        have hw : |(1007617347/2000000000 : ℝ)|=(1007617347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129850921/5000000000 : ℝ)|^39 ≤ (15394112623223/100000000000000 : ℝ)^31
        have hw : |(1129850921/5000000000 : ℝ)|=(1129850921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s2_s2_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1286961749/2500000000 : ℝ)*x 0 + (1026714401/2000000000 : ℝ)*x 1 + (-202470851/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1286961749/2500000000 : ℝ)^39 ≤ (21685849653679/50000000000000 : ℝ)^31 := by
    have hnat : (1286961749 : ℕ)^39*50000000000000^31 ≤ 21685849653679^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286961749 2500000000 21685849653679 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026714401/2000000000 : ℝ)^39 ≤ (43220446293861/100000000000000 : ℝ)^31 := by
    have hnat : (1026714401 : ℕ)^39*100000000000000^31 ≤ 43220446293861^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026714401 2000000000 43220446293861 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202470851/1000000000 : ℝ)^39 ≤ (3351963595223/25000000000000 : ℝ)^31 := by
    have hnat : (202470851 : ℕ)^39*25000000000000^31 ≤ 3351963595223^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202470851 1000000000 3351963595223 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1286961749/2500000000 : ℝ), (1026714401/2000000000 : ℝ), (-202470851/1000000000 : ℝ)] ![(21685849653679/50000000000000 : ℝ), (43220446293861/100000000000000 : ℝ), (3351963595223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1286961749/2500000000 : ℝ)|^39 ≤ (21685849653679/50000000000000 : ℝ)^31
        have hw : |(1286961749/2500000000 : ℝ)|=(1286961749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026714401/2000000000 : ℝ)|^39 ≤ (43220446293861/100000000000000 : ℝ)^31
        have hw : |(1026714401/2000000000 : ℝ)|=(1026714401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202470851/1000000000 : ℝ)|^39 ≤ (3351963595223/25000000000000 : ℝ)^31
        have hw : |(-202470851/1000000000 : ℝ)|=(202470851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317054_s2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((1513/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1513/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51443/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38993/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20163/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20163/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1329/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1329/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (1513/3125 : ℝ) ^ (77/16 : ℝ) ≤ (1523979468543013927/50000000000000000000 : ℝ) := by
    have hpowers : (1513/3125 : ℝ)^77 ≤ (1523979468543013927/50000000000000000000 : ℝ)^16 := by
      have hnat : (1513 : ℕ)^77*50000000000000000000^16 ≤ 1523979468543013927^16*3125^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1513 3125 1523979468543013927 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1513/3125 : ℝ)) (X := (1523979468543013927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (51523979468543013927/50000000000000000000 : ℝ) ≤ (1006258320587021/1000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (51523979468543013927/50000000000000000000 : ℝ)^16 ≤ (1006258320587021/1000000000000000 : ℝ)^77 := by
      have hnat : (51523979468543013927 : ℕ)^16*1000000000000000^77 ≤ 1006258320587021^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51523979468543013927 50000000000000000000 1006258320587021 1000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006258320587021/1000000000000000 : ℝ)) (X := (51523979468543013927/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (26523979468543013927/25000000000000000000 : ℝ) ≤ (10123716719590651/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (26523979468543013927/25000000000000000000 : ℝ)^16 ≤ (10123716719590651/10000000000000000 : ℝ)^77 := by
      have hnat : (26523979468543013927 : ℕ)^16*10000000000000000^77 ≤ 10123716719590651^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26523979468543013927 25000000000000000000 10123716719590651 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10123716719590651/10000000000000000 : ℝ)) (X := (26523979468543013927/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6258320587021/484160000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(61133513720441/4841600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1513/3125 : ℝ)) (alpha := (6258320587021/484160000000000 : ℝ)) (beta := (61133513720441/4841600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1513/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6258320587021/484160000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(61133513720441/4841600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (51443/100000 : ℝ) ^ (77/16 : ℝ) ≤ (1020229240948855879/25000000000000000000 : ℝ) := by
    have hpowers : (51443/100000 : ℝ)^77 ≤ (1020229240948855879/25000000000000000000 : ℝ)^16 := by
      have hnat : (51443 : ℕ)^77*25000000000000000000^16 ≤ 1020229240948855879^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51443 100000 1020229240948855879 25000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51443/100000 : ℝ)) (X := (1020229240948855879/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (26020229240948855879/25000000000000000000 : ℝ) ≤ (10083460032787523/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (26020229240948855879/25000000000000000000 : ℝ)^16 ≤ (10083460032787523/10000000000000000 : ℝ)^77 := by
      have hnat : (26020229240948855879 : ℕ)^16*10000000000000000^77 ≤ 10083460032787523^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26020229240948855879 25000000000000000000 10083460032787523 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10083460032787523/10000000000000000 : ℝ)) (X := (26020229240948855879/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (13520229240948855879/12500000000000000000 : ℝ) ≤ (2032873320192943/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (13520229240948855879/12500000000000000000 : ℝ)^16 ≤ (2032873320192943/2000000000000000 : ℝ)^77 := by
      have hnat : (13520229240948855879 : ℕ)^16*2000000000000000^77 ≤ 2032873320192943^77*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13520229240948855879 12500000000000000000 2032873320192943 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2032873320192943/2000000000000000 : ℝ)) (X := (13520229240948855879/12500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(11922861826789/734900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(10113321022149/643037500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (51443/100000 : ℝ)) (alpha := (11922861826789/734900000000000 : ℝ)) (beta := (10113321022149/643037500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (51443/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(11922861826789/734900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(10113321022149/643037500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (38993/100000 : ℝ) ^ (77/16 : ℝ) ≤ (134441473844929089/12500000000000000000 : ℝ) := by
    have hpowers : (38993/100000 : ℝ)^77 ≤ (134441473844929089/12500000000000000000 : ℝ)^16 := by
      have hnat : (38993 : ℕ)^77*12500000000000000000^16 ≤ 134441473844929089^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38993 100000 134441473844929089 12500000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38993/100000 : ℝ)) (X := (134441473844929089/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (12634441473844929089/12500000000000000000 : ℝ) ≤ (10022254109224813/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (12634441473844929089/12500000000000000000 : ℝ)^16 ≤ (10022254109224813/10000000000000000 : ℝ)^77 := by
      have hnat : (12634441473844929089 : ℕ)^16*10000000000000000^77 ≤ 10022254109224813^77*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12634441473844929089 12500000000000000000 10022254109224813 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022254109224813/10000000000000000 : ℝ)) (X := (12634441473844929089/12500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (6384441473844929089/6250000000000000000 : ℝ) ≤ (10044321404751173/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (6384441473844929089/6250000000000000000 : ℝ)^16 ≤ (10044321404751173/10000000000000000 : ℝ)^77 := by
      have hnat : (6384441473844929089 : ℕ)^16*10000000000000000^77 ≤ 10044321404751173^77*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6384441473844929089 6250000000000000000 10044321404751173 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10044321404751173/10000000000000000 : ℝ)) (X := (6384441473844929089/6250000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(22254109224813/3899300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(551682388159/97482500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (38993/100000 : ℝ)) (alpha := (22254109224813/3899300000000000 : ℝ)) (beta := (551682388159/97482500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38993/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(22254109224813/3899300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(551682388159/97482500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1347327537/10000000000 : ℝ)*X 0 0+(141501253/312500000 : ℝ)*X 0 1+(-1555759169/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5066199297/10000000000 : ℝ)*X 2 0+(1262236493/2500000000 : ℝ)*X 2 1+(1116518533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2558522211/5000000000 : ℝ)*X 0 0+(637819183/1250000000 : ℝ)*X 0 1+(-525721827/2500000000 : ℝ)*X 0 2+(2558522211/5000000000 : ℝ)*X 1 0+(637819183/1250000000 : ℝ)*X 1 1+(-525721827/2500000000 : ℝ)*X 1 2+(2558522211/5000000000 : ℝ)*X 2 0+(637819183/1250000000 : ℝ)*X 2 1+(-525721827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1329617753/10000000000 : ℝ)*X 0 0+(4439460191/10000000000 : ℝ)*X 0 1+(-1579041009/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((339293637/625000000 : ℝ)*X 1 0+(-2126065573/10000000000 : ℝ)*X 1 1+(-2383447349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5016877657/10000000000 : ℝ)*X 2 0+(5244512739/10000000000 : ℝ)*X 2 1+(512327879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2553270897/5000000000 : ℝ)*X 0 0+(529889529/1000000000 : ℝ)*X 0 1+(-1864482667/10000000000 : ℝ)*X 0 2+(2553270897/5000000000 : ℝ)*X 1 0+(529889529/1000000000 : ℝ)*X 1 1+(-1864482667/10000000000 : ℝ)*X 1 2+(2553270897/5000000000 : ℝ)*X 2 0+(529889529/1000000000 : ℝ)*X 2 1+(-1864482667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-604594607/5000000000 : ℝ)*X 0 0+(4538992597/10000000000 : ℝ)*X 0 1+(-6304615127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((5334209073/10000000000 : ℝ)*X 1 0+(-2238260451/10000000000 : ℝ)*X 1 1+(-4772681963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5265328357/10000000000 : ℝ)*X 2 0+(500039623/1000000000 : ℝ)*X 2 1+(255440531/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5302302951/10000000000 : ℝ)*X 0 0+(5079907821/10000000000 : ℝ)*X 0 1+(-1894477831/10000000000 : ℝ)*X 0 2+(5302302951/10000000000 : ℝ)*X 1 0+(5079907821/10000000000 : ℝ)*X 1 1+(-1894477831/10000000000 : ℝ)*X 1 2+(5302302951/10000000000 : ℝ)*X 2 0+(5079907821/10000000000 : ℝ)*X 2 1+(-1894477831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1123822701/10000000000 : ℝ)*X 0 0+(4715320213/10000000000 : ℝ)*X 0 1+(-619680841/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5688948267/10000000000 : ℝ)*X 1 0+(-424057209/2000000000 : ℝ)*X 1 1+(-4498837899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2527713169/5000000000 : ℝ)*X 2 0+(1007617347/2000000000 : ℝ)*X 2 1+(1129850921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1286961749/2500000000 : ℝ)*X 0 0+(1026714401/2000000000 : ℝ)*X 0 1+(-202470851/1000000000 : ℝ)*X 0 2+(1286961749/2500000000 : ℝ)*X 1 0+(1026714401/2000000000 : ℝ)*X 1 1+(-202470851/1000000000 : ℝ)*X 1 2+(1286961749/2500000000 : ℝ)*X 2 0+(1026714401/2000000000 : ℝ)*X 2 1+(-202470851/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((20163/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20163/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18138907464679501755238706019873/971184725819840000000000000000000000 : ℝ) := by norm_num
    linear_combination (5009565707591/1000000000000 : ℝ)*(base39) + (1794576664321/1000000000000 : ℝ)*(base60) + (25642655960507/1000000000000 : ℝ)*(major_s2_0) + (25642655960507/1000000000000 : ℝ)*(major_s2_1) + (25642655960507/1000000000000 : ℝ)*(major_s2_2) + (6807881591/1000000000000 : ℝ)*(sp_s2_0) + (1418955441/500000000000 : ℝ)*(sp_s2_6) + (37021340238071/1000000000000 : ℝ)*(sp_s2_7) + (7405616824323/200000000000 : ℝ)*(sp_s2_8) + (37028260862891/1000000000000 : ℝ)*(sp_s2_9) + (14254012319021/1000000000000 : ℝ)*(sp_s2_13) + (19209109/62500000000 : ℝ)*(sp_s2_14) + (23208987/62500000000 : ℝ)*(sp_s2_15) + (38920503/200000000000 : ℝ)*(sp_s2_23) + (14256850229903/1000000000000 : ℝ)*(f.failure) + (18514227732703/500000000000 : ℝ)*(f.sum) + (9855636769439433871/14327977850000000000000000000000 : ℝ)*base62 + (25541467595927/389930000000000000000000000 : ℝ)*base64 + (838963249930773/2572150000000000000000000000 : ℝ)*base67 + (5690379581785629/3899300000000000000000000000 : ℝ)*base68 + (1460057549577138883/3775770176000000000000000000000 : ℝ)*base71 + (4795773565560227/4841600000000000000000000000 : ℝ)*base73 + (361797578697127/734900000000000000000000000 : ℝ)*base74 + (47750426986829/96832000000000000000000000 : ℝ)*base76 + (72467166781205632697/249066428800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (56693/50000000000000000 : ℝ)*base87 + (56693/50000000000000000 : ℝ)*base89 + (56693/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18784231633948401/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (4958178960387/1000000000000 : ℝ)*(base39) + (1452431/500000000000 : ℝ)*(base40) + (763042598061/500000000000 : ℝ)*(base60) + (25708725533113/1000000000000 : ℝ)*(major_s2_0) + (25708725533113/1000000000000 : ℝ)*(major_s2_1) + (25708725533113/1000000000000 : ℝ)*(major_s2_2) + (10407693/25000000000 : ℝ)*(sp_s2_0) + (61451843/250000000000 : ℝ)*(sp_s2_6) + (370532449/1000000000000 : ℝ)*(sp_s2_8) + (18561724271793/500000000000 : ℝ)*(sp_s2_14) + (37123494318857/1000000000000 : ℝ)*(sp_s2_15) + (37123772404417/1000000000000 : ℝ)*(sp_s2_16) + (714666895149/50000000000 : ℝ)*(sp_s2_20) + (92446889/1000000000000 : ℝ)*(sp_s2_23) + (893348981897/62500000000 : ℝ)*(f.failure) + (18561932425653/500000000000 : ℝ)*(f.sum) + (1538589021365226891/14327977850000000000000000000000 : ℝ)*base63 + (110280808697041/194965000000000000000000000 : ℝ)*base64 + (108752226146623/183725000000000000000000000 : ℝ)*base67 + (1910985457505821/3899300000000000000000000000 : ℝ)*base68 + (134624401010838077/755154035200000000000000000000 : ℝ)*base71 + (1236070685002673/4841600000000000000000000000 : ℝ)*base73 + (395287964305193/734900000000000000000000000 : ℝ)*base74 + (37449804847807/96832000000000000000000000 : ℝ)*base76 + (12618861034407940251/35580918400000000000000000000000 : ℝ)*base78 + (491/1562500000000000 : ℝ)*base87 + (491/1562500000000000 : ℝ)*base89 + (491/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1329/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1329/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (725947955611183278513969/138815080000000000000000000000 : ℝ) := by norm_num
    linear_combination (865173911119/250000000000 : ℝ)*(base39) + (313943662309/500000000000 : ℝ)*(base60) + (3989998679951/250000000000 : ℝ)*(major_s2_0) + (3989998679951/250000000000 : ℝ)*(major_s2_1) + (3989998679951/250000000000 : ℝ)*(major_s2_2) + (353291717/500000000000 : ℝ)*(sp_s2_2) + (159333883/1000000000000 : ℝ)*(sp_s2_8) + (129359/3906250000 : ℝ)*(sp_s2_13) + (46381157/1000000000000 : ℝ)*(sp_s2_14) + (468509/3906250000 : ℝ)*(sp_s2_20) + (1440404661929/62500000000 : ℝ)*(sp_s2_21) + (23046361638139/1000000000000 : ℝ)*(sp_s2_22) + (5761453597147/250000000000 : ℝ)*(sp_s2_23) + (2218328417543/250000000000 : ℝ)*(sp_s2_27) + (443673336219/50000000000 : ℝ)*(f.failure) + (23046520972021/1000000000000 : ℝ)*(f.sum) + (1802856685702860989/7163988925000000000000000000000 : ℝ)*base63 + (173828443712101/389930000000000000000000000 : ℝ)*base64 + (106030814727381/2572150000000000000000000000 : ℝ)*base67 + (592786800477239/1949650000000000000000000000 : ℝ)*base68 + (63502070992308653/277630160000000000000000000000 : ℝ)*base70 + (13855887755863/71200000000000000000000000 : ℝ)*base73 + (55585203650163/91862500000000000000000000 : ℝ)*base74 + (4336841810221/7120000000000000000000000 : ℝ)*base76 + (1800535815726277307/3662741600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (889/2500000000000000 : ℝ)*base87 + (889/2500000000000000 : ℝ)*base89 + (889/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((1513/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1513/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51443/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38993/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20163/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20163/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1329/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1329/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317054_s2 p hpa hpb X hX hprev1

#print axioms solution

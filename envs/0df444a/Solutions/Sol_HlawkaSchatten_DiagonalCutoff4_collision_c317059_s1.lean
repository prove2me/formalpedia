-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317059_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:15:33.842081+00:00
-- url     : https://prove2.me/submissions/8b42fdfc-f974-4651-99fc-aaf9d72bc607

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
theorem collision_support_c317059_s1_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1603502753/5000000000 : ℝ)*x 0 + (1601274091/5000000000 : ℝ)*x 1 + (5966000677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1603502753/5000000000 : ℝ)^39 ≤ (2391341303269/10000000000000 : ℝ)^31 := by
    have hnat : (1603502753 : ℕ)^39*10000000000000^31 ≤ 2391341303269^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603502753 5000000000 2391341303269 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1601274091/5000000000 : ℝ)^39 ≤ (11935803398861/50000000000000 : ℝ)^31 := by
    have hnat : (1601274091 : ℕ)^39*50000000000000^31 ≤ 11935803398861^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601274091 5000000000 11935803398861 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5966000677/10000000000 : ℝ)^39 ≤ (52214980148491/100000000000000 : ℝ)^31 := by
    have hnat : (5966000677 : ℕ)^39*100000000000000^31 ≤ 52214980148491^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5966000677 10000000000 52214980148491 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1603502753/5000000000 : ℝ), (1601274091/5000000000 : ℝ), (5966000677/10000000000 : ℝ)] ![(2391341303269/10000000000000 : ℝ), (11935803398861/50000000000000 : ℝ), (52214980148491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1603502753/5000000000 : ℝ)|^39 ≤ (2391341303269/10000000000000 : ℝ)^31
        have hw : |(-1603502753/5000000000 : ℝ)|=(1603502753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1601274091/5000000000 : ℝ)|^39 ≤ (11935803398861/50000000000000 : ℝ)^31
        have hw : |(1601274091/5000000000 : ℝ)|=(1601274091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5966000677/10000000000 : ℝ)|^39 ≤ (52214980148491/100000000000000 : ℝ)^31
        have hw : |(5966000677/10000000000 : ℝ)|=(5966000677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5870670939/10000000000 : ℝ)*x 0 + (679199007/1250000000 : ℝ)*x 1 + (-517611577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5870670939/10000000000 : ℝ)^39 ≤ (51167506238447/100000000000000 : ℝ)^31 := by
    have hnat : (5870670939 : ℕ)^39*100000000000000^31 ≤ 51167506238447^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5870670939 10000000000 51167506238447 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679199007/1250000000 : ℝ)^39 ≤ (46421844414251/100000000000000 : ℝ)^31 := by
    have hnat : (679199007 : ℕ)^39*100000000000000^31 ≤ 46421844414251^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679199007 1250000000 46421844414251 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517611577/10000000000 : ℝ)^39 ≤ (241064933847/10000000000000 : ℝ)^31 := by
    have hnat : (517611577 : ℕ)^39*10000000000000^31 ≤ 241064933847^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517611577 10000000000 241064933847 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5870670939/10000000000 : ℝ), (679199007/1250000000 : ℝ), (-517611577/10000000000 : ℝ)] ![(51167506238447/100000000000000 : ℝ), (46421844414251/100000000000000 : ℝ), (241064933847/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5870670939/10000000000 : ℝ)|^39 ≤ (51167506238447/100000000000000 : ℝ)^31
        have hw : |(5870670939/10000000000 : ℝ)|=(5870670939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679199007/1250000000 : ℝ)|^39 ≤ (46421844414251/100000000000000 : ℝ)^31
        have hw : |(679199007/1250000000 : ℝ)|=(679199007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517611577/10000000000 : ℝ)|^39 ≤ (241064933847/10000000000000 : ℝ)^31
        have hw : |(-517611577/10000000000 : ℝ)|=(517611577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (785051011/2000000000 : ℝ)*x 0 + (318116769/625000000 : ℝ)*x 1 + (3469969019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (785051011/2000000000 : ℝ)^39 ≤ (30836110475257/100000000000000 : ℝ)^31 := by
    have hnat : (785051011 : ℕ)^39*100000000000000^31 ≤ 30836110475257^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785051011 2000000000 30836110475257 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318116769/625000000 : ℝ)^39 ≤ (42758052093621/100000000000000 : ℝ)^31 := by
    have hnat : (318116769 : ℕ)^39*100000000000000^31 ≤ 42758052093621^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318116769 625000000 42758052093621 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3469969019/10000000000 : ℝ)^39 ≤ (1056233496699/4000000000000 : ℝ)^31 := by
    have hnat : (3469969019 : ℕ)^39*4000000000000^31 ≤ 1056233496699^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3469969019 10000000000 1056233496699 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(785051011/2000000000 : ℝ), (318116769/625000000 : ℝ), (3469969019/10000000000 : ℝ)] ![(30836110475257/100000000000000 : ℝ), (42758052093621/100000000000000 : ℝ), (1056233496699/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(785051011/2000000000 : ℝ)|^39 ≤ (30836110475257/100000000000000 : ℝ)^31
        have hw : |(785051011/2000000000 : ℝ)|=(785051011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(318116769/625000000 : ℝ)|^39 ≤ (42758052093621/100000000000000 : ℝ)^31
        have hw : |(318116769/625000000 : ℝ)|=(318116769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3469969019/10000000000 : ℝ)|^39 ≤ (1056233496699/4000000000000 : ℝ)^31
        have hw : |(3469969019/10000000000 : ℝ)|=(3469969019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1519806171/5000000000 : ℝ)*x 0 + (2796104339/10000000000 : ℝ)*x 1 + (1288623047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1519806171/5000000000 : ℝ)^39 ≤ (2235382919021/10000000000000 : ℝ)^31 := by
    have hnat : (1519806171 : ℕ)^39*10000000000000^31 ≤ 2235382919021^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519806171 5000000000 2235382919021 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796104339/10000000000 : ℝ)^39 ≤ (1257790919047/6250000000000 : ℝ)^31 := by
    have hnat : (2796104339 : ℕ)^39*6250000000000^31 ≤ 1257790919047^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796104339 10000000000 1257790919047 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288623047/2000000000 : ℝ)^39 ≤ (14380379024549/25000000000000 : ℝ)^31 := by
    have hnat : (1288623047 : ℕ)^39*25000000000000^31 ≤ 14380379024549^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288623047 2000000000 14380379024549 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1519806171/5000000000 : ℝ), (2796104339/10000000000 : ℝ), (1288623047/2000000000 : ℝ)] ![(2235382919021/10000000000000 : ℝ), (1257790919047/6250000000000 : ℝ), (14380379024549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1519806171/5000000000 : ℝ)|^39 ≤ (2235382919021/10000000000000 : ℝ)^31
        have hw : |(-1519806171/5000000000 : ℝ)|=(1519806171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796104339/10000000000 : ℝ)|^39 ≤ (1257790919047/6250000000000 : ℝ)^31
        have hw : |(2796104339/10000000000 : ℝ)|=(2796104339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288623047/2000000000 : ℝ)|^39 ≤ (14380379024549/25000000000000 : ℝ)^31
        have hw : |(1288623047/2000000000 : ℝ)|=(1288623047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (763689681/2500000000 : ℝ)*x 0 + (-554594793/2000000000 : ℝ)*x 1 + (6449257193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (763689681/2500000000 : ℝ)^39 ≤ (35146959119/156250000000 : ℝ)^31 := by
    have hnat : (763689681 : ℕ)^39*156250000000^31 ≤ 35146959119^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763689681 2500000000 35146959119 156250000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554594793/2000000000 : ℝ)^39 ≤ (9957719118489/50000000000000 : ℝ)^31 := by
    have hnat : (554594793 : ℕ)^39*50000000000000^31 ≤ 9957719118489^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554594793 2000000000 9957719118489 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6449257193/10000000000 : ℝ)^39 ≤ (7198813489419/12500000000000 : ℝ)^31 := by
    have hnat : (6449257193 : ℕ)^39*12500000000000^31 ≤ 7198813489419^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6449257193 10000000000 7198813489419 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(763689681/2500000000 : ℝ), (-554594793/2000000000 : ℝ), (6449257193/10000000000 : ℝ)] ![(35146959119/156250000000 : ℝ), (9957719118489/50000000000000 : ℝ), (7198813489419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(763689681/2500000000 : ℝ)|^39 ≤ (35146959119/156250000000 : ℝ)^31
        have hw : |(763689681/2500000000 : ℝ)|=(763689681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554594793/2000000000 : ℝ)|^39 ≤ (9957719118489/50000000000000 : ℝ)^31
        have hw : |(-554594793/2000000000 : ℝ)|=(554594793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6449257193/10000000000 : ℝ)|^39 ≤ (7198813489419/12500000000000 : ℝ)^31
        have hw : |(6449257193/10000000000 : ℝ)|=(6449257193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2835968239/5000000000 : ℝ)*x 0 + (291875587/500000000 : ℝ)*x 1 + (-277127/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2835968239/5000000000 : ℝ)^39 ≤ (6124747280839/12500000000000 : ℝ)^31 := by
    have hnat : (2835968239 : ℕ)^39*12500000000000^31 ≤ 6124747280839^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835968239 5000000000 6124747280839 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291875587/500000000 : ℝ)^39 ≤ (25402090160009/50000000000000 : ℝ)^31 := by
    have hnat : (291875587 : ℕ)^39*50000000000000^31 ≤ 25402090160009^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291875587 500000000 25402090160009 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277127/39062500 : ℝ)^39 ≤ (98920706967/50000000000000 : ℝ)^31 := by
    have hnat : (277127 : ℕ)^39*50000000000000^31 ≤ 98920706967^31*39062500^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277127 39062500 98920706967 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2835968239/5000000000 : ℝ), (291875587/500000000 : ℝ), (-277127/39062500 : ℝ)] ![(6124747280839/12500000000000 : ℝ), (25402090160009/50000000000000 : ℝ), (98920706967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2835968239/5000000000 : ℝ)|^39 ≤ (6124747280839/12500000000000 : ℝ)^31
        have hw : |(2835968239/5000000000 : ℝ)|=(2835968239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291875587/500000000 : ℝ)|^39 ≤ (25402090160009/50000000000000 : ℝ)^31
        have hw : |(291875587/500000000 : ℝ)|=(291875587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277127/39062500 : ℝ)|^39 ≤ (98920706967/50000000000000 : ℝ)^31
        have hw : |(-277127/39062500 : ℝ)|=(277127/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1806782801/5000000000 : ℝ)*x 0 + (198335853/312500000 : ℝ)*x 1 + (2303555333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806782801/5000000000 : ℝ)^39 ≤ (27787846848913/100000000000000 : ℝ)^31 := by
    have hnat : (1806782801 : ℕ)^39*100000000000000^31 ≤ 27787846848913^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806782801 5000000000 27787846848913 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198335853/312500000 : ℝ)^39 ≤ (2257650290433/4000000000000 : ℝ)^31 := by
    have hnat : (198335853 : ℕ)^39*4000000000000^31 ≤ 2257650290433^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198335853 312500000 2257650290433 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303555333/10000000000 : ℝ)^39 ≤ (15770895882191/100000000000000 : ℝ)^31 := by
    have hnat : (2303555333 : ℕ)^39*100000000000000^31 ≤ 15770895882191^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303555333 10000000000 15770895882191 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1806782801/5000000000 : ℝ), (198335853/312500000 : ℝ), (2303555333/10000000000 : ℝ)] ![(27787846848913/100000000000000 : ℝ), (2257650290433/4000000000000 : ℝ), (15770895882191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1806782801/5000000000 : ℝ)|^39 ≤ (27787846848913/100000000000000 : ℝ)^31
        have hw : |(1806782801/5000000000 : ℝ)|=(1806782801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(198335853/312500000 : ℝ)|^39 ≤ (2257650290433/4000000000000 : ℝ)^31
        have hw : |(198335853/312500000 : ℝ)|=(198335853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2303555333/10000000000 : ℝ)|^39 ≤ (15770895882191/100000000000000 : ℝ)^31
        have hw : |(2303555333/10000000000 : ℝ)|=(2303555333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-348755471/1250000000 : ℝ)*x 0 + (3050151933/10000000000 : ℝ)*x 1 + (6439313639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348755471/1250000000 : ℝ)^39 ≤ (4013958582889/20000000000000 : ℝ)^31 := by
    have hnat : (348755471 : ℕ)^39*20000000000000^31 ≤ 4013958582889^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348755471 1250000000 4013958582889 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3050151933/10000000000 : ℝ)^39 ≤ (11225692652619/50000000000000 : ℝ)^31 := by
    have hnat : (3050151933 : ℕ)^39*50000000000000^31 ≤ 11225692652619^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3050151933 10000000000 11225692652619 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6439313639/10000000000 : ℝ)^39 ≤ (28739410882711/50000000000000 : ℝ)^31 := by
    have hnat : (6439313639 : ℕ)^39*50000000000000^31 ≤ 28739410882711^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6439313639 10000000000 28739410882711 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-348755471/1250000000 : ℝ), (3050151933/10000000000 : ℝ), (6439313639/10000000000 : ℝ)] ![(4013958582889/20000000000000 : ℝ), (11225692652619/50000000000000 : ℝ), (28739410882711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-348755471/1250000000 : ℝ)|^39 ≤ (4013958582889/20000000000000 : ℝ)^31
        have hw : |(-348755471/1250000000 : ℝ)|=(348755471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3050151933/10000000000 : ℝ)|^39 ≤ (11225692652619/50000000000000 : ℝ)^31
        have hw : |(3050151933/10000000000 : ℝ)|=(3050151933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6439313639/10000000000 : ℝ)|^39 ≤ (28739410882711/50000000000000 : ℝ)^31
        have hw : |(6439313639/10000000000 : ℝ)|=(6439313639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2782663699/10000000000 : ℝ)*x 0 + (-609982789/2000000000 : ℝ)*x 1 + (805681807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2782663699/10000000000 : ℝ)^39 ≤ (4000605644189/20000000000000 : ℝ)^31 := by
    have hnat : (2782663699 : ℕ)^39*20000000000000^31 ≤ 4000605644189^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782663699 10000000000 4000605644189 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609982789/2000000000 : ℝ)^39 ≤ (22449181489549/100000000000000 : ℝ)^31 := by
    have hnat : (609982789 : ℕ)^39*100000000000000^31 ≤ 22449181489549^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609982789 2000000000 22449181489549 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805681807/1250000000 : ℝ)^39 ≤ (57547790263957/100000000000000 : ℝ)^31 := by
    have hnat : (805681807 : ℕ)^39*100000000000000^31 ≤ 57547790263957^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805681807 1250000000 57547790263957 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2782663699/10000000000 : ℝ), (-609982789/2000000000 : ℝ), (805681807/1250000000 : ℝ)] ![(4000605644189/20000000000000 : ℝ), (22449181489549/100000000000000 : ℝ), (57547790263957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2782663699/10000000000 : ℝ)|^39 ≤ (4000605644189/20000000000000 : ℝ)^31
        have hw : |(2782663699/10000000000 : ℝ)|=(2782663699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-609982789/2000000000 : ℝ)|^39 ≤ (22449181489549/100000000000000 : ℝ)^31
        have hw : |(-609982789/2000000000 : ℝ)|=(609982789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805681807/1250000000 : ℝ)|^39 ≤ (57547790263957/100000000000000 : ℝ)^31
        have hw : |(805681807/1250000000 : ℝ)|=(805681807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6267498747/10000000000 : ℝ)*x 0 + (5228910109/10000000000 : ℝ)*x 1 + (-9343297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6267498747/10000000000 : ℝ)^39 ≤ (55556065735803/100000000000000 : ℝ)^31 := by
    have hnat : (6267498747 : ℕ)^39*100000000000000^31 ≤ 55556065735803^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6267498747 10000000000 55556065735803 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228910109/10000000000 : ℝ)^39 ≤ (22116331787107/50000000000000 : ℝ)^31 := by
    have hnat : (5228910109 : ℕ)^39*50000000000000^31 ≤ 22116331787107^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228910109 10000000000 22116331787107 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9343297/1250000000 : ℝ)^39 ≤ (105635335073/50000000000000 : ℝ)^31 := by
    have hnat : (9343297 : ℕ)^39*50000000000000^31 ≤ 105635335073^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9343297 1250000000 105635335073 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6267498747/10000000000 : ℝ), (5228910109/10000000000 : ℝ), (-9343297/1250000000 : ℝ)] ![(55556065735803/100000000000000 : ℝ), (22116331787107/50000000000000 : ℝ), (105635335073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6267498747/10000000000 : ℝ)|^39 ≤ (55556065735803/100000000000000 : ℝ)^31
        have hw : |(6267498747/10000000000 : ℝ)|=(6267498747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228910109/10000000000 : ℝ)|^39 ≤ (22116331787107/50000000000000 : ℝ)^31
        have hw : |(5228910109/10000000000 : ℝ)|=(5228910109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9343297/1250000000 : ℝ)|^39 ≤ (105635335073/50000000000000 : ℝ)^31
        have hw : |(-9343297/1250000000 : ℝ)|=(9343297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_19 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-157/5000000000 : ℝ)*x 0 + (157/5000000000 : ℝ)*x 1 + (4999999997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157/5000000000 : ℝ)^39 ≤ (36363/100000000000000 : ℝ)^31 := by
    have hnat : (157 : ℕ)^39*100000000000000^31 ≤ 36363^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157 5000000000 36363 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157/5000000000 : ℝ)^39 ≤ (36363/100000000000000 : ℝ)^31 := by
    have hnat : (157 : ℕ)^39*100000000000000^31 ≤ 36363^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157 5000000000 36363 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999999997/5000000000 : ℝ)^39 ≤ (99999999924517/100000000000000 : ℝ)^31 := by
    have hnat : (4999999997 : ℕ)^39*100000000000000^31 ≤ 99999999924517^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999997 5000000000 99999999924517 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-157/5000000000 : ℝ), (157/5000000000 : ℝ), (4999999997/5000000000 : ℝ)] ![(36363/100000000000000 : ℝ), (36363/100000000000000 : ℝ), (99999999924517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-157/5000000000 : ℝ)|^39 ≤ (36363/100000000000000 : ℝ)^31
        have hw : |(-157/5000000000 : ℝ)|=(157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157/5000000000 : ℝ)|^39 ≤ (36363/100000000000000 : ℝ)^31
        have hw : |(157/5000000000 : ℝ)|=(157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999999997/5000000000 : ℝ)|^39 ≤ (99999999924517/100000000000000 : ℝ)^31
        have hw : |(4999999997/5000000000 : ℝ)|=(4999999997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1305135329/2500000000 : ℝ)*x 0 + (4827163859/10000000000 : ℝ)*x 1 + (2313430069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305135329/2500000000 : ℝ)^39 ≤ (44143618905477/100000000000000 : ℝ)^31 := by
    have hnat : (1305135329 : ℕ)^39*100000000000000^31 ≤ 44143618905477^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305135329 2500000000 44143618905477 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827163859/10000000000 : ℝ)^39 ≤ (40000385881491/100000000000000 : ℝ)^31 := by
    have hnat : (4827163859 : ℕ)^39*100000000000000^31 ≤ 40000385881491^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827163859 10000000000 40000385881491 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2313430069/10000000000 : ℝ)^39 ≤ (3963998797243/25000000000000 : ℝ)^31 := by
    have hnat : (2313430069 : ℕ)^39*25000000000000^31 ≤ 3963998797243^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313430069 10000000000 3963998797243 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305135329/2500000000 : ℝ), (4827163859/10000000000 : ℝ), (2313430069/10000000000 : ℝ)] ![(44143618905477/100000000000000 : ℝ), (40000385881491/100000000000000 : ℝ), (3963998797243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305135329/2500000000 : ℝ)|^39 ≤ (44143618905477/100000000000000 : ℝ)^31
        have hw : |(1305135329/2500000000 : ℝ)|=(1305135329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827163859/10000000000 : ℝ)|^39 ≤ (40000385881491/100000000000000 : ℝ)^31
        have hw : |(4827163859/10000000000 : ℝ)|=(4827163859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2313430069/10000000000 : ℝ)|^39 ≤ (3963998797243/25000000000000 : ℝ)^31
        have hw : |(2313430069/10000000000 : ℝ)|=(2313430069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-402229839/1250000000 : ℝ)*x 0 + (50372747/156250000 : ℝ)*x 1 + (5938587961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402229839/1250000000 : ℝ)^39 ≤ (24015082575483/100000000000000 : ℝ)^31 := by
    have hnat : (402229839 : ℕ)^39*100000000000000^31 ≤ 24015082575483^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402229839 1250000000 24015082575483 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50372747/156250000 : ℝ)^39 ≤ (12035795577561/50000000000000 : ℝ)^31 := by
    have hnat : (50372747 : ℕ)^39*50000000000000^31 ≤ 12035795577561^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50372747 156250000 12035795577561 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5938587961/10000000000 : ℝ)^39 ≤ (51913326248553/100000000000000 : ℝ)^31 := by
    have hnat : (5938587961 : ℕ)^39*100000000000000^31 ≤ 51913326248553^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938587961 10000000000 51913326248553 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402229839/1250000000 : ℝ), (50372747/156250000 : ℝ), (5938587961/10000000000 : ℝ)] ![(24015082575483/100000000000000 : ℝ), (12035795577561/50000000000000 : ℝ), (51913326248553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402229839/1250000000 : ℝ)|^39 ≤ (24015082575483/100000000000000 : ℝ)^31
        have hw : |(-402229839/1250000000 : ℝ)|=(402229839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50372747/156250000 : ℝ)|^39 ≤ (12035795577561/50000000000000 : ℝ)^31
        have hw : |(50372747/156250000 : ℝ)|=(50372747/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5938587961/10000000000 : ℝ)|^39 ≤ (51913326248553/100000000000000 : ℝ)^31
        have hw : |(5938587961/10000000000 : ℝ)|=(5938587961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3199132827/10000000000 : ℝ)*x 0 + (-400944253/1250000000 : ℝ)*x 1 + (1193688317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3199132827/10000000000 : ℝ)^39 ≤ (11919791790167/50000000000000 : ℝ)^31 := by
    have hnat : (3199132827 : ℕ)^39*50000000000000^31 ≤ 11919791790167^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3199132827 10000000000 11919791790167 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400944253/1250000000 : ℝ)^39 ≤ (11959279370953/50000000000000 : ℝ)^31 := by
    have hnat : (400944253 : ℕ)^39*50000000000000^31 ≤ 11959279370953^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400944253 1250000000 11959279370953 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193688317/2000000000 : ℝ)^39 ≤ (52241857660659/100000000000000 : ℝ)^31 := by
    have hnat : (1193688317 : ℕ)^39*100000000000000^31 ≤ 52241857660659^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193688317 2000000000 52241857660659 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3199132827/10000000000 : ℝ), (-400944253/1250000000 : ℝ), (1193688317/2000000000 : ℝ)] ![(11919791790167/50000000000000 : ℝ), (11959279370953/50000000000000 : ℝ), (52241857660659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3199132827/10000000000 : ℝ)|^39 ≤ (11919791790167/50000000000000 : ℝ)^31
        have hw : |(3199132827/10000000000 : ℝ)|=(3199132827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400944253/1250000000 : ℝ)|^39 ≤ (11959279370953/50000000000000 : ℝ)^31
        have hw : |(-400944253/1250000000 : ℝ)|=(400944253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193688317/2000000000 : ℝ)|^39 ≤ (52241857660659/100000000000000 : ℝ)^31
        have hw : |(1193688317/2000000000 : ℝ)|=(1193688317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6651846291/10000000000 : ℝ)*x 0 + (4694153397/10000000000 : ℝ)*x 1 + (-7121337/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6651846291/10000000000 : ℝ)^39 ≤ (14968899742541/25000000000000 : ℝ)^31 := by
    have hnat : (6651846291 : ℕ)^39*25000000000000^31 ≤ 14968899742541^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6651846291 10000000000 14968899742541 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4694153397/10000000000 : ℝ)^39 ≤ (38618719116051/100000000000000 : ℝ)^31 := by
    have hnat : (4694153397 : ℕ)^39*100000000000000^31 ≤ 38618719116051^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694153397 10000000000 38618719116051 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7121337/200000000 : ℝ)^39 ≤ (1505681904149/100000000000000 : ℝ)^31 := by
    have hnat : (7121337 : ℕ)^39*100000000000000^31 ≤ 1505681904149^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7121337 200000000 1505681904149 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6651846291/10000000000 : ℝ), (4694153397/10000000000 : ℝ), (-7121337/200000000 : ℝ)] ![(14968899742541/25000000000000 : ℝ), (38618719116051/100000000000000 : ℝ), (1505681904149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6651846291/10000000000 : ℝ)|^39 ≤ (14968899742541/25000000000000 : ℝ)^31
        have hw : |(6651846291/10000000000 : ℝ)|=(6651846291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4694153397/10000000000 : ℝ)|^39 ≤ (38618719116051/100000000000000 : ℝ)^31
        have hw : |(4694153397/10000000000 : ℝ)|=(4694153397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7121337/200000000 : ℝ)|^39 ≤ (1505681904149/100000000000000 : ℝ)^31
        have hw : |(-7121337/200000000 : ℝ)|=(7121337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317059_s1_s1_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2029542021/10000000000 : ℝ)*x 0 + (1769160609/2500000000 : ℝ)*x 1 + (2982501507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029542021/10000000000 : ℝ)^39 ≤ (6724067497299/50000000000000 : ℝ)^31 := by
    have hnat : (2029542021 : ℕ)^39*50000000000000^31 ≤ 6724067497299^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029542021 10000000000 6724067497299 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769160609/2500000000 : ℝ)^39 ≤ (64725139475891/100000000000000 : ℝ)^31 := by
    have hnat : (1769160609 : ℕ)^39*100000000000000^31 ≤ 64725139475891^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769160609 2500000000 64725139475891 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2982501507/10000000000 : ℝ)^39 ≤ (873069020867/4000000000000 : ℝ)^31 := by
    have hnat : (2982501507 : ℕ)^39*4000000000000^31 ≤ 873069020867^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982501507 10000000000 873069020867 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2029542021/10000000000 : ℝ), (1769160609/2500000000 : ℝ), (2982501507/10000000000 : ℝ)] ![(6724067497299/50000000000000 : ℝ), (64725139475891/100000000000000 : ℝ), (873069020867/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2029542021/10000000000 : ℝ)|^39 ≤ (6724067497299/50000000000000 : ℝ)^31
        have hw : |(2029542021/10000000000 : ℝ)|=(2029542021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1769160609/2500000000 : ℝ)|^39 ≤ (64725139475891/100000000000000 : ℝ)^31
        have hw : |(1769160609/2500000000 : ℝ)|=(1769160609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2982501507/10000000000 : ℝ)|^39 ≤ (873069020867/4000000000000 : ℝ)^31
        have hw : |(2982501507/10000000000 : ℝ)|=(2982501507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317059_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((77651/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77651/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38607/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38607/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(62623/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(62623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40161/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40161/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1527/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1527/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1443/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1443/10000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (77651/100000 : ℝ) ^ (77/16 : ℝ) ≤ (14801396644730797903/50000000000000000000 : ℝ) := by
    have hpowers : (77651/100000 : ℝ)^77 ≤ (14801396644730797903/50000000000000000000 : ℝ)^16 := by
      have hnat : (77651 : ℕ)^77*50000000000000000000^16 ≤ 14801396644730797903^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77651 100000 14801396644730797903 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77651/100000 : ℝ)) (X := (14801396644730797903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (64801396644730797903/50000000000000000000 : ℝ) ≤ (2110718820207619/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (64801396644730797903/50000000000000000000 : ℝ)^16 ≤ (2110718820207619/2000000000000000 : ℝ)^77 := by
      have hnat : (64801396644730797903 : ℕ)^16*2000000000000000^77 ≤ 2110718820207619^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64801396644730797903 50000000000000000000 2110718820207619 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2110718820207619/2000000000000000 : ℝ)) (X := (64801396644730797903/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (39801396644730797903/25000000000000000000 : ℝ) ≤ (5507257284464831/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (39801396644730797903/25000000000000000000 : ℝ)^16 ≤ (5507257284464831/5000000000000000 : ℝ)^77 := by
      have hnat : (39801396644730797903 : ℕ)^16*5000000000000000^77 ≤ 5507257284464831^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39801396644730797903 25000000000000000000 5507257284464831 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5507257284464831/5000000000000000 : ℝ)) (X := (39801396644730797903/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(110718820207619/1553020000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(460920467891567/7765100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (77651/100000 : ℝ)) (alpha := (110718820207619/1553020000000000 : ℝ)) (beta := (460920467891567/7765100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (77651/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(110718820207619/1553020000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(460920467891567/7765100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (38607/50000 : ℝ) ^ (77/16 : ℝ) ≤ (450150018899603647/1562500000000000000 : ℝ) := by
    have hpowers : (38607/50000 : ℝ)^77 ≤ (450150018899603647/1562500000000000000 : ℝ)^16 := by
      have hnat : (38607 : ℕ)^77*1562500000000000000^16 ≤ 450150018899603647^16*50000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38607 50000 450150018899603647 1562500000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38607/50000 : ℝ)) (X := (450150018899603647/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (2012650018899603647/1562500000000000000 : ℝ) ≤ (5270070087094571/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2012650018899603647/1562500000000000000 : ℝ)^16 ≤ (5270070087094571/5000000000000000 : ℝ)^77 := by
      have hnat : (2012650018899603647 : ℕ)^16*5000000000000000^77 ≤ 5270070087094571^77*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2012650018899603647 1562500000000000000 5270070087094571 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5270070087094571/5000000000000000 : ℝ)) (X := (2012650018899603647/1562500000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1231400018899603647/781250000000000000 : ℝ) ≤ (2198323649950957/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (1231400018899603647/781250000000000000 : ℝ)^16 ≤ (2198323649950957/2000000000000000 : ℝ)^77 := by
      have hnat : (1231400018899603647 : ℕ)^16*2000000000000000^77 ≤ 2198323649950957^77*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1231400018899603647 781250000000000000 2198323649950957 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2198323649950957/2000000000000000 : ℝ)) (X := (1231400018899603647/781250000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(90023362364857/1286900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(451478075565643/7721400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (38607/50000 : ℝ)) (alpha := (90023362364857/1286900000000000 : ℝ)) (beta := (451478075565643/7721400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (38607/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(90023362364857/1286900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(451478075565643/7721400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (62623/100000 : ℝ) ^ (77/16 : ℝ) ≤ (10514333410438496171/100000000000000000000 : ℝ) := by
    have hpowers : (62623/100000 : ℝ)^77 ≤ (10514333410438496171/100000000000000000000 : ℝ)^16 := by
      have hnat : (62623 : ℕ)^77*100000000000000000000^16 ≤ 10514333410438496171^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62623 100000 10514333410438496171 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62623/100000 : ℝ)) (X := (10514333410438496171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110514333410438496171/100000000000000000000 : ℝ) ≤ (102099131668137/100000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (110514333410438496171/100000000000000000000 : ℝ)^16 ≤ (102099131668137/100000000000000 : ℝ)^77 := by
      have hnat : (110514333410438496171 : ℕ)^16*100000000000000^77 ≤ 102099131668137^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110514333410438496171 100000000000000000000 102099131668137 100000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (102099131668137/100000000000000 : ℝ)) (X := (110514333410438496171/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60514333410438496171/50000000000000000000 : ℝ) ≤ (1040455552832613/1000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (60514333410438496171/50000000000000000000 : ℝ)^16 ≤ (1040455552832613/1000000000000000 : ℝ)^77 := by
      have hnat : (60514333410438496171 : ℕ)^16*1000000000000000^77 ≤ 1040455552832613^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60514333410438496171 50000000000000000000 1040455552832613 1000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1040455552832613/1000000000000000 : ℝ)) (X := (60514333410438496171/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2099131668137/62623000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(19464236151243/626230000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (62623/100000 : ℝ)) (alpha := (2099131668137/62623000000000 : ℝ)) (beta := (19464236151243/626230000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (62623/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2099131668137/62623000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(19464236151243/626230000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1603502753/5000000000 : ℝ)*X 0 0+(1601274091/5000000000 : ℝ)*X 0 1+(5966000677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5870670939/10000000000 : ℝ)*X 2 0+(679199007/1250000000 : ℝ)*X 2 1+(-517611577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((785051011/2000000000 : ℝ)*X 0 0+(318116769/625000000 : ℝ)*X 0 1+(3469969019/10000000000 : ℝ)*X 0 2+(785051011/2000000000 : ℝ)*X 1 0+(318116769/625000000 : ℝ)*X 1 1+(3469969019/10000000000 : ℝ)*X 1 2+(785051011/2000000000 : ℝ)*X 2 0+(318116769/625000000 : ℝ)*X 2 1+(3469969019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1519806171/5000000000 : ℝ)*X 0 0+(2796104339/10000000000 : ℝ)*X 0 1+(1288623047/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((763689681/2500000000 : ℝ)*X 1 0+(-554594793/2000000000 : ℝ)*X 1 1+(6449257193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2835968239/5000000000 : ℝ)*X 2 0+(291875587/500000000 : ℝ)*X 2 1+(-277127/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1806782801/5000000000 : ℝ)*X 0 0+(198335853/312500000 : ℝ)*X 0 1+(2303555333/10000000000 : ℝ)*X 0 2+(1806782801/5000000000 : ℝ)*X 1 0+(198335853/312500000 : ℝ)*X 1 1+(2303555333/10000000000 : ℝ)*X 1 2+(1806782801/5000000000 : ℝ)*X 2 0+(198335853/312500000 : ℝ)*X 2 1+(2303555333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-348755471/1250000000 : ℝ)*X 0 0+(3050151933/10000000000 : ℝ)*X 0 1+(6439313639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2782663699/10000000000 : ℝ)*X 1 0+(-609982789/2000000000 : ℝ)*X 1 1+(805681807/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6267498747/10000000000 : ℝ)*X 2 0+(5228910109/10000000000 : ℝ)*X 2 1+(-9343297/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-157/5000000000 : ℝ)*X 0 0+(157/5000000000 : ℝ)*X 0 1+(4999999997/5000000000 : ℝ)*X 0 2+(-157/5000000000 : ℝ)*X 1 0+(157/5000000000 : ℝ)*X 1 1+(4999999997/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_19 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1305135329/2500000000 : ℝ)*X 0 0+(4827163859/10000000000 : ℝ)*X 0 1+(2313430069/10000000000 : ℝ)*X 0 2+(1305135329/2500000000 : ℝ)*X 1 0+(4827163859/10000000000 : ℝ)*X 1 1+(2313430069/10000000000 : ℝ)*X 1 2+(1305135329/2500000000 : ℝ)*X 2 0+(4827163859/10000000000 : ℝ)*X 2 1+(2313430069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-402229839/1250000000 : ℝ)*X 0 0+(50372747/156250000 : ℝ)*X 0 1+(5938587961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3199132827/10000000000 : ℝ)*X 1 0+(-400944253/1250000000 : ℝ)*X 1 1+(1193688317/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((6651846291/10000000000 : ℝ)*X 2 0+(4694153397/10000000000 : ℝ)*X 2 1+(-7121337/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2029542021/10000000000 : ℝ)*X 0 0+(1769160609/2500000000 : ℝ)*X 0 1+(2982501507/10000000000 : ℝ)*X 0 2+(2029542021/10000000000 : ℝ)*X 1 0+(1769160609/2500000000 : ℝ)*X 1 1+(2982501507/10000000000 : ℝ)*X 1 2+(2029542021/10000000000 : ℝ)*X 2 0+(1769160609/2500000000 : ℝ)*X 2 1+(2982501507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317059_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((40161/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40161/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53273311922847059247965814378219/3128929134796850000000000000000000000 : ℝ) := by norm_num
    linear_combination (263937/1000000000000 : ℝ)*(base19) + (1102017847291/500000000000 : ℝ)*(base60) + (1003838796151/125000000000 : ℝ)*(major_s1_0) + (1003838796151/125000000000 : ℝ)*(major_s1_1) + (8030843561041/1000000000000 : ℝ)*(major_s1_2) + (378441/200000000000 : ℝ)*(sp_s1_0) + (20185639/250000000000 : ℝ)*(sp_s1_2) + (2899059585397/250000000000 : ℝ)*(sp_s1_7) + (11596485926317/1000000000000 : ℝ)*(sp_s1_8) + (11596405447699/1000000000000 : ℝ)*(sp_s1_9) + (558109549533/125000000000 : ℝ)*(sp_s1_13) + (245956461/1000000000000 : ℝ)*(sp_s1_14) + (133191833/1000000000000 : ℝ)*(sp_s1_19) + (52476543/1000000000000 : ℝ)*(sp_s1_27) + (4464928872807/1000000000000 : ℝ)*(f.failure) + (5798243095127/500000000000 : ℝ)*(f.sum) + (23369758068296240231/40294769350000000000000000000000 : ℝ)*base62 + (40919450408811/156557500000000000000000000 : ℝ)*base64 + (838083927296621/1930350000000000000000000000 : ℝ)*base67 + (120885472396741/626230000000000000000000000 : ℝ)*base68 + (7806222700212175979/12156846432500000000000000000000 : ℝ)*base70 + (273052982527561/485318750000000000000000000 : ℝ)*base73 + (56937892951637/643450000000000000000000000 : ℝ)*base74 + (45613269116903/194127500000000000000000000 : ℝ)*base76 + (3258899855362298543/149893607850000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (6317/50000000000000000 : ℝ)*base87 + (6317/50000000000000000 : ℝ)*base89 + (6317/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1527/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1527/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (140592017681679928171007249/20147384675000000000000000000000 : ℝ) := by norm_num
    linear_combination (628487/250000000000 : ℝ)*(base19) + (2189339510819/1000000000000 : ℝ)*(base60) + (1994621607487/250000000000 : ℝ)*(major_s1_0) + (1994621607487/250000000000 : ℝ)*(major_s1_1) + (7978531308497/1000000000000 : ℝ)*(major_s1_2) + (6904179/500000000000 : ℝ)*(sp_s1_0) + (6039781/500000000000 : ℝ)*(sp_s1_6) + (107959513/1000000000000 : ℝ)*(sp_s1_8) + (2880265853213/250000000000 : ℝ)*(sp_s1_14) + (46083866991/4000000000 : ℝ)*(sp_s1_15) + (5760510394383/500000000000 : ℝ)*(sp_s1_16) + (11219637/250000000000 : ℝ)*(sp_s1_19) + (221794061653/50000000000 : ℝ)*(sp_s1_20) + (14108111/250000000000 : ℝ)*(sp_s1_23) + (2217946656311/500000000000 : ℝ)*(f.failure) + (1152107722121/100000000000 : ℝ)*(f.sum) + (2909531780595701163/20147384675000000000000000000000 : ℝ)*base62 + (63046584788533/125246000000000000000000000 : ℝ)*base64 + (1079931922615801/1930350000000000000000000000 : ℝ)*base67 + (47178530073847/62623000000000000000000000 : ℝ)*base68 + (2615772802578188657/24313692865000000000000000000000 : ℝ)*base71 + (755791897545187/3882550000000000000000000000 : ℝ)*base72 + (144689828610251/321725000000000000000000000 : ℝ)*base74 + (5317354006871/12132968750000000000000000 : ℝ)*base76 + (1310358035509515827/149893607850000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (4541/25000000000000000 : ℝ)*base87 + (4541/25000000000000000 : ℝ)*base89 + (20459/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1443/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1443/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9032222616302193237360345419873/625785826959370000000000000000000000 : ℝ) := by norm_num
    linear_combination (586727/500000000000 : ℝ)*(base8) + (2996083/500000000000 : ℝ)*(base11) + (1559795921/100000000000 : ℝ)*(base50) + (783807012277/1000000000000 : ℝ)*(base60) + (455427526481/100000000000 : ℝ)*(major_s1_0) + (455427526481/100000000000 : ℝ)*(major_s1_1) + (455427526481/100000000000 : ℝ)*(major_s1_2) + (20841121/500000000000 : ℝ)*(sp_s1_2) + (94444427/1000000000000 : ℝ)*(sp_s1_13) + (50600471/500000000000 : ℝ)*(sp_s1_16) + (6576444355747/1000000000000 : ℝ)*(sp_s1_21) + (3288225760683/500000000000 : ℝ)*(sp_s1_22) + (6576308638183/1000000000000 : ℝ)*(sp_s1_23) + (506399950537/200000000000 : ℝ)*(sp_s1_27) + (316511774639/125000000000 : ℝ)*(f.failure) + (3288225760683/500000000000 : ℝ)*(f.sum) + (596940175776669817/4029476935000000000000000000000 : ℝ)*base62 + (77904018996207/313115000000000000000000000 : ℝ)*base64 + (35462948717741/772140000000000000000000000 : ℝ)*base67 + (251093974798917/626230000000000000000000000 : ℝ)*base69 + (3045916176715926249/48627385730000000000000000000000 : ℝ)*base70 + (488031927625731/776510000000000000000000000 : ℝ)*base73 + (6637878595341/128690000000000000000000000 : ℝ)*base75 + (9093301948289/97063750000000000000000000 : ℝ)*base77 + (270407084967357271/59957443140000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (2591/6250000000000000 : ℝ)*base86 + (2591/6250000000000000 : ℝ)*base88 + (2591/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((77651/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77651/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38607/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38607/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(62623/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(62623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40161/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40161/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1527/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1527/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1443/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1443/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317059_s1 p hpa hpb X hX hprev0

#print axioms solution

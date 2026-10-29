-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:24:35.080045+00:00
-- url     : https://prove2.me/submissions/1ff30354-6d1d-4ceb-9369-22415764ead1

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
theorem collision_support_c318062_s1_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1401572597/10000000000 : ℝ)*x 0 + (623704779/1250000000 : ℝ)*x 1 + (-715415403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1401572597/10000000000 : ℝ)^79 ≤ (531818044139/6250000000000 : ℝ)^63 := by
    have hnat : (1401572597 : ℕ)^79*6250000000000^63 ≤ 531818044139^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401572597 10000000000 531818044139 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623704779/1250000000 : ℝ)^79 ≤ (41820400228077/100000000000000 : ℝ)^63 := by
    have hnat : (623704779 : ℕ)^79*100000000000000^63 ≤ 41820400228077^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623704779 1250000000 41820400228077 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (715415403/1250000000 : ℝ)^79 ≤ (24835255529241/50000000000000 : ℝ)^63 := by
    have hnat : (715415403 : ℕ)^79*50000000000000^63 ≤ 24835255529241^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715415403 1250000000 24835255529241 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1401572597/10000000000 : ℝ), (623704779/1250000000 : ℝ), (-715415403/1250000000 : ℝ)] ![(531818044139/6250000000000 : ℝ), (41820400228077/100000000000000 : ℝ), (24835255529241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1401572597/10000000000 : ℝ)|^79 ≤ (531818044139/6250000000000 : ℝ)^63
        have hw : |(-1401572597/10000000000 : ℝ)|=(1401572597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623704779/1250000000 : ℝ)|^79 ≤ (41820400228077/100000000000000 : ℝ)^63
        have hw : |(623704779/1250000000 : ℝ)|=(623704779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-715415403/1250000000 : ℝ)|^79 ≤ (24835255529241/50000000000000 : ℝ)^63
        have hw : |(-715415403/1250000000 : ℝ)|=(715415403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1035996087/2000000000 : ℝ)*x 0 + (5196632469/10000000000 : ℝ)*x 1 + (1863488523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035996087/2000000000 : ℝ)^79 ≤ (21915255336049/50000000000000 : ℝ)^63 := by
    have hnat : (1035996087 : ℕ)^79*50000000000000^63 ≤ 21915255336049^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035996087 2000000000 21915255336049 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196632469/10000000000 : ℝ)^79 ≤ (11001817195587/25000000000000 : ℝ)^63 := by
    have hnat : (5196632469 : ℕ)^79*25000000000000^63 ≤ 11001817195587^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196632469 10000000000 11001817195587 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863488523/10000000000 : ℝ)^79 ≤ (12162220532623/100000000000000 : ℝ)^63 := by
    have hnat : (1863488523 : ℕ)^79*100000000000000^63 ≤ 12162220532623^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863488523 10000000000 12162220532623 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035996087/2000000000 : ℝ), (5196632469/10000000000 : ℝ), (1863488523/10000000000 : ℝ)] ![(21915255336049/50000000000000 : ℝ), (11001817195587/25000000000000 : ℝ), (12162220532623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035996087/2000000000 : ℝ)|^79 ≤ (21915255336049/50000000000000 : ℝ)^63
        have hw : |(1035996087/2000000000 : ℝ)|=(1035996087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196632469/10000000000 : ℝ)|^79 ≤ (11001817195587/25000000000000 : ℝ)^63
        have hw : |(5196632469/10000000000 : ℝ)|=(5196632469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1863488523/10000000000 : ℝ)|^79 ≤ (12162220532623/100000000000000 : ℝ)^63
        have hw : |(1863488523/10000000000 : ℝ)|=(1863488523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5520614731/10000000000 : ℝ)*x 0 + (5505236897/10000000000 : ℝ)*x 1 + (-948784787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520614731/10000000000 : ℝ)^79 ≤ (5934313061681/12500000000000 : ℝ)^63 := by
    have hnat : (5520614731 : ℕ)^79*12500000000000^63 ≤ 5934313061681^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520614731 10000000000 5934313061681 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505236897/10000000000 : ℝ)^79 ≤ (47308736393559/100000000000000 : ℝ)^63 := by
    have hnat : (5505236897 : ℕ)^79*100000000000000^63 ≤ 47308736393559^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505236897 10000000000 47308736393559 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948784787/10000000000 : ℝ)^79 ≤ (5216759100783/100000000000000 : ℝ)^63 := by
    have hnat : (948784787 : ℕ)^79*100000000000000^63 ≤ 5216759100783^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948784787 10000000000 5216759100783 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520614731/10000000000 : ℝ), (5505236897/10000000000 : ℝ), (-948784787/10000000000 : ℝ)] ![(5934313061681/12500000000000 : ℝ), (47308736393559/100000000000000 : ℝ), (5216759100783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520614731/10000000000 : ℝ)|^79 ≤ (5934313061681/12500000000000 : ℝ)^63
        have hw : |(5520614731/10000000000 : ℝ)|=(5520614731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505236897/10000000000 : ℝ)|^79 ≤ (47308736393559/100000000000000 : ℝ)^63
        have hw : |(5505236897/10000000000 : ℝ)|=(5505236897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948784787/10000000000 : ℝ)|^79 ≤ (5216759100783/100000000000000 : ℝ)^63
        have hw : |(-948784787/10000000000 : ℝ)|=(948784787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029124073/10000000000 : ℝ)*x 0 + (2258246929/5000000000 : ℝ)*x 1 + (-6415399073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029124073/10000000000 : ℝ)^79 ≤ (1444128707721/25000000000000 : ℝ)^63 := by
    have hnat : (1029124073 : ℕ)^79*25000000000000^63 ≤ 1444128707721^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029124073 10000000000 1444128707721 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258246929/5000000000 : ℝ)^79 ≤ (9227242895511/25000000000000 : ℝ)^63 := by
    have hnat : (2258246929 : ℕ)^79*25000000000000^63 ≤ 9227242895511^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258246929 5000000000 9227242895511 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6415399073/10000000000 : ℝ)^79 ≤ (57314513571821/100000000000000 : ℝ)^63 := by
    have hnat : (6415399073 : ℕ)^79*100000000000000^63 ≤ 57314513571821^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6415399073 10000000000 57314513571821 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029124073/10000000000 : ℝ), (2258246929/5000000000 : ℝ), (-6415399073/10000000000 : ℝ)] ![(1444128707721/25000000000000 : ℝ), (9227242895511/25000000000000 : ℝ), (57314513571821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029124073/10000000000 : ℝ)|^79 ≤ (1444128707721/25000000000000 : ℝ)^63
        have hw : |(-1029124073/10000000000 : ℝ)|=(1029124073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258246929/5000000000 : ℝ)|^79 ≤ (9227242895511/25000000000000 : ℝ)^63
        have hw : |(2258246929/5000000000 : ℝ)|=(2258246929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6415399073/10000000000 : ℝ)|^79 ≤ (57314513571821/100000000000000 : ℝ)^63
        have hw : |(-6415399073/10000000000 : ℝ)|=(6415399073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2405149083/5000000000 : ℝ)*x 0 + (-582058657/10000000000 : ℝ)*x 1 + (-1281551419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2405149083/5000000000 : ℝ)^79 ≤ (7988840852779/20000000000000 : ℝ)^63 := by
    have hnat : (2405149083 : ℕ)^79*20000000000000^63 ≤ 7988840852779^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405149083 5000000000 7988840852779 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582058657/10000000000 : ℝ)^79 ≤ (2826880926331/100000000000000 : ℝ)^63 := by
    have hnat : (582058657 : ℕ)^79*100000000000000^63 ≤ 2826880926331^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582058657 10000000000 2826880926331 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281551419/2000000000 : ℝ)^79 ≤ (57228914798343/100000000000000 : ℝ)^63 := by
    have hnat : (1281551419 : ℕ)^79*100000000000000^63 ≤ 57228914798343^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281551419 2000000000 57228914798343 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2405149083/5000000000 : ℝ), (-582058657/10000000000 : ℝ), (-1281551419/2000000000 : ℝ)] ![(7988840852779/20000000000000 : ℝ), (2826880926331/100000000000000 : ℝ), (57228914798343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2405149083/5000000000 : ℝ)|^79 ≤ (7988840852779/20000000000000 : ℝ)^63
        have hw : |(2405149083/5000000000 : ℝ)|=(2405149083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-582058657/10000000000 : ℝ)|^79 ≤ (2826880926331/100000000000000 : ℝ)^63
        have hw : |(-582058657/10000000000 : ℝ)|=(582058657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1281551419/2000000000 : ℝ)|^79 ≤ (57228914798343/100000000000000 : ℝ)^63
        have hw : |(-1281551419/2000000000 : ℝ)|=(1281551419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4782772017/10000000000 : ℝ)*x 0 + (1571241273/2500000000 : ℝ)*x 1 + (210268241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4782772017/10000000000 : ℝ)^79 ≤ (39657788028839/100000000000000 : ℝ)^63 := by
    have hnat : (4782772017 : ℕ)^79*100000000000000^63 ≤ 39657788028839^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782772017 10000000000 39657788028839 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1571241273/2500000000 : ℝ)^79 ≤ (6982134569709/12500000000000 : ℝ)^63 := by
    have hnat : (1571241273 : ℕ)^79*12500000000000^63 ≤ 6982134569709^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571241273 2500000000 6982134569709 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210268241/2500000000 : ℝ)^79 ≤ (2242567699091/50000000000000 : ℝ)^63 := by
    have hnat : (210268241 : ℕ)^79*50000000000000^63 ≤ 2242567699091^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210268241 2500000000 2242567699091 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4782772017/10000000000 : ℝ), (1571241273/2500000000 : ℝ), (210268241/2500000000 : ℝ)] ![(39657788028839/100000000000000 : ℝ), (6982134569709/12500000000000 : ℝ), (2242567699091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4782772017/10000000000 : ℝ)|^79 ≤ (39657788028839/100000000000000 : ℝ)^63
        have hw : |(4782772017/10000000000 : ℝ)|=(4782772017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1571241273/2500000000 : ℝ)|^79 ≤ (6982134569709/12500000000000 : ℝ)^63
        have hw : |(1571241273/2500000000 : ℝ)|=(1571241273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210268241/2500000000 : ℝ)|^79 ≤ (2242567699091/50000000000000 : ℝ)^63
        have hw : |(210268241/2500000000 : ℝ)|=(210268241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5045035127/10000000000 : ℝ)*x 0 + (3167185041/5000000000 : ℝ)*x 1 + (-291624997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5045035127/10000000000 : ℝ)^79 ≤ (8480688826683/20000000000000 : ℝ)^63 := by
    have hnat : (5045035127 : ℕ)^79*20000000000000^63 ≤ 8480688826683^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045035127 10000000000 8480688826683 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3167185041/5000000000 : ℝ)^79 ≤ (28204110315887/50000000000000 : ℝ)^63 := by
    have hnat : (3167185041 : ℕ)^79*50000000000000^63 ≤ 28204110315887^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167185041 5000000000 28204110315887 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291624997/10000000000 : ℝ)^79 ≤ (1188335219729/100000000000000 : ℝ)^63 := by
    have hnat : (291624997 : ℕ)^79*100000000000000^63 ≤ 1188335219729^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291624997 10000000000 1188335219729 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5045035127/10000000000 : ℝ), (3167185041/5000000000 : ℝ), (-291624997/10000000000 : ℝ)] ![(8480688826683/20000000000000 : ℝ), (28204110315887/50000000000000 : ℝ), (1188335219729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5045035127/10000000000 : ℝ)|^79 ≤ (8480688826683/20000000000000 : ℝ)^63
        have hw : |(5045035127/10000000000 : ℝ)|=(5045035127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3167185041/5000000000 : ℝ)|^79 ≤ (28204110315887/50000000000000 : ℝ)^63
        have hw : |(3167185041/5000000000 : ℝ)|=(3167185041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-291624997/10000000000 : ℝ)|^79 ≤ (1188335219729/100000000000000 : ℝ)^63
        have hw : |(-291624997/10000000000 : ℝ)|=(291624997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-116317911/2000000000 : ℝ)*x 0 + (4808660881/10000000000 : ℝ)*x 1 + (-6409534321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116317911/2000000000 : ℝ)^79 ≤ (44125380027/1562500000000 : ℝ)^63 := by
    have hnat : (116317911 : ℕ)^79*1562500000000^63 ≤ 44125380027^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116317911 2000000000 44125380027 1562500000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4808660881/10000000000 : ℝ)^79 ≤ (19963578124249/50000000000000 : ℝ)^63 := by
    have hnat : (4808660881 : ℕ)^79*50000000000000^63 ≤ 19963578124249^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808660881 10000000000 19963578124249 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6409534321/10000000000 : ℝ)^79 ≤ (57248819421737/100000000000000 : ℝ)^63 := by
    have hnat : (6409534321 : ℕ)^79*100000000000000^63 ≤ 57248819421737^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6409534321 10000000000 57248819421737 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116317911/2000000000 : ℝ), (4808660881/10000000000 : ℝ), (-6409534321/10000000000 : ℝ)] ![(44125380027/1562500000000 : ℝ), (19963578124249/50000000000000 : ℝ), (57248819421737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116317911/2000000000 : ℝ)|^79 ≤ (44125380027/1562500000000 : ℝ)^63
        have hw : |(-116317911/2000000000 : ℝ)|=(116317911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4808660881/10000000000 : ℝ)|^79 ≤ (19963578124249/50000000000000 : ℝ)^63
        have hw : |(4808660881/10000000000 : ℝ)|=(4808660881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6409534321/10000000000 : ℝ)|^79 ≤ (57248819421737/100000000000000 : ℝ)^63
        have hw : |(-6409534321/10000000000 : ℝ)|=(6409534321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (453815453/1000000000 : ℝ)*x 0 + (-127380951/1250000000 : ℝ)*x 1 + (-6401892903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453815453/1000000000 : ℝ)^79 ≤ (725216287/1953125000 : ℝ)^63 := by
    have hnat : (453815453 : ℕ)^79*1953125000^63 ≤ 725216287^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453815453 1000000000 725216287 1953125000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127380951/1250000000 : ℝ)^79 ≤ (5705679281861/100000000000000 : ℝ)^63 := by
    have hnat : (127380951 : ℕ)^79*100000000000000^63 ≤ 5705679281861^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127380951 1250000000 5705679281861 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6401892903/10000000000 : ℝ)^79 ≤ (7145405851319/12500000000000 : ℝ)^63 := by
    have hnat : (6401892903 : ℕ)^79*12500000000000^63 ≤ 7145405851319^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6401892903 10000000000 7145405851319 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(453815453/1000000000 : ℝ), (-127380951/1250000000 : ℝ), (-6401892903/10000000000 : ℝ)] ![(725216287/1953125000 : ℝ), (5705679281861/100000000000000 : ℝ), (7145405851319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(453815453/1000000000 : ℝ)|^79 ≤ (725216287/1953125000 : ℝ)^63
        have hw : |(453815453/1000000000 : ℝ)|=(453815453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127380951/1250000000 : ℝ)|^79 ≤ (5705679281861/100000000000000 : ℝ)^63
        have hw : |(-127380951/1250000000 : ℝ)|=(127380951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6401892903/10000000000 : ℝ)|^79 ≤ (7145405851319/12500000000000 : ℝ)^63
        have hw : |(-6401892903/10000000000 : ℝ)|=(6401892903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6060027339/10000000000 : ℝ)*x 0 + (627192613/1250000000 : ℝ)*x 1 + (846937581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6060027339/10000000000 : ℝ)^79 ≤ (13340436558553/25000000000000 : ℝ)^63 := by
    have hnat : (6060027339 : ℕ)^79*25000000000000^63 ≤ 13340436558553^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6060027339 10000000000 13340436558553 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627192613/1250000000 : ℝ)^79 ≤ (10528466815401/25000000000000 : ℝ)^63 := by
    have hnat : (627192613 : ℕ)^79*25000000000000^63 ≤ 10528466815401^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627192613 1250000000 10528466815401 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846937581/10000000000 : ℝ)^79 ≤ (1131096623503/25000000000000 : ℝ)^63 := by
    have hnat : (846937581 : ℕ)^79*25000000000000^63 ≤ 1131096623503^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846937581 10000000000 1131096623503 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6060027339/10000000000 : ℝ), (627192613/1250000000 : ℝ), (846937581/10000000000 : ℝ)] ![(13340436558553/25000000000000 : ℝ), (10528466815401/25000000000000 : ℝ), (1131096623503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6060027339/10000000000 : ℝ)|^79 ≤ (13340436558553/25000000000000 : ℝ)^63
        have hw : |(6060027339/10000000000 : ℝ)|=(6060027339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627192613/1250000000 : ℝ)|^79 ≤ (10528466815401/25000000000000 : ℝ)^63
        have hw : |(627192613/1250000000 : ℝ)|=(627192613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846937581/10000000000 : ℝ)|^79 ≤ (1131096623503/25000000000000 : ℝ)^63
        have hw : |(846937581/10000000000 : ℝ)|=(846937581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3437097173/5000000000 : ℝ)*x 0 + (4450264157/10000000000 : ℝ)*x 1 + (-307163027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3437097173/5000000000 : ℝ)^79 ≤ (62500186406289/100000000000000 : ℝ)^63 := by
    have hnat : (3437097173 : ℕ)^79*100000000000000^63 ≤ 62500186406289^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3437097173 5000000000 62500186406289 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4450264157/10000000000 : ℝ)^79 ≤ (36231552488323/100000000000000 : ℝ)^63 := by
    have hnat : (4450264157 : ℕ)^79*100000000000000^63 ≤ 36231552488323^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450264157 10000000000 36231552488323 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307163027/10000000000 : ℝ)^79 ≤ (50730443679/4000000000000 : ℝ)^63 := by
    have hnat : (307163027 : ℕ)^79*4000000000000^63 ≤ 50730443679^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307163027 10000000000 50730443679 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3437097173/5000000000 : ℝ), (4450264157/10000000000 : ℝ), (-307163027/10000000000 : ℝ)] ![(62500186406289/100000000000000 : ℝ), (36231552488323/100000000000000 : ℝ), (50730443679/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3437097173/5000000000 : ℝ)|^79 ≤ (62500186406289/100000000000000 : ℝ)^63
        have hw : |(3437097173/5000000000 : ℝ)|=(3437097173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4450264157/10000000000 : ℝ)|^79 ≤ (36231552488323/100000000000000 : ℝ)^63
        have hw : |(4450264157/10000000000 : ℝ)|=(4450264157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307163027/10000000000 : ℝ)|^79 ≤ (50730443679/4000000000000 : ℝ)^63
        have hw : |(-307163027/10000000000 : ℝ)|=(307163027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-77738221/2500000000 : ℝ)*x 0 + (5579253087/10000000000 : ℝ)*x 1 + (-5808975499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77738221/2500000000 : ℝ)^79 ≤ (64395700237/5000000000000 : ℝ)^63 := by
    have hnat : (77738221 : ℕ)^79*5000000000000^63 ≤ 64395700237^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77738221 2500000000 64395700237 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5579253087/10000000000 : ℝ)^79 ≤ (48107681545957/100000000000000 : ℝ)^63 := by
    have hnat : (5579253087 : ℕ)^79*100000000000000^63 ≤ 48107681545957^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579253087 10000000000 48107681545957 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5808975499/10000000000 : ℝ)^79 ≤ (202417617733/400000000000 : ℝ)^63 := by
    have hnat : (5808975499 : ℕ)^79*400000000000^63 ≤ 202417617733^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808975499 10000000000 202417617733 400000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77738221/2500000000 : ℝ), (5579253087/10000000000 : ℝ), (-5808975499/10000000000 : ℝ)] ![(64395700237/5000000000000 : ℝ), (48107681545957/100000000000000 : ℝ), (202417617733/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77738221/2500000000 : ℝ)|^79 ≤ (64395700237/5000000000000 : ℝ)^63
        have hw : |(-77738221/2500000000 : ℝ)|=(77738221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5579253087/10000000000 : ℝ)|^79 ≤ (48107681545957/100000000000000 : ℝ)^63
        have hw : |(5579253087/10000000000 : ℝ)|=(5579253087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5808975499/10000000000 : ℝ)|^79 ≤ (202417617733/400000000000 : ℝ)^63
        have hw : |(-5808975499/10000000000 : ℝ)|=(5808975499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (615244813/1000000000 : ℝ)*x 0 + (-21828729/250000000 : ℝ)*x 1 + (-490331431/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (615244813/1000000000 : ℝ)^79 ≤ (13596052990917/25000000000000 : ℝ)^63 := by
    have hnat : (615244813 : ℕ)^79*25000000000000^63 ≤ 13596052990917^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615244813 1000000000 13596052990917 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21828729/250000000 : ℝ)^79 ≤ (4700656547059/100000000000000 : ℝ)^63 := by
    have hnat : (21828729 : ℕ)^79*100000000000000^63 ≤ 4700656547059^63*250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21828729 250000000 4700656547059 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490331431/1000000000 : ℝ)^79 ≤ (40915131470419/100000000000000 : ℝ)^63 := by
    have hnat : (490331431 : ℕ)^79*100000000000000^63 ≤ 40915131470419^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490331431 1000000000 40915131470419 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(615244813/1000000000 : ℝ), (-21828729/250000000 : ℝ), (-490331431/1000000000 : ℝ)] ![(13596052990917/25000000000000 : ℝ), (4700656547059/100000000000000 : ℝ), (40915131470419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(615244813/1000000000 : ℝ)|^79 ≤ (13596052990917/25000000000000 : ℝ)^63
        have hw : |(615244813/1000000000 : ℝ)|=(615244813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21828729/250000000 : ℝ)|^79 ≤ (4700656547059/100000000000000 : ℝ)^63
        have hw : |(-21828729/250000000 : ℝ)|=(21828729/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490331431/1000000000 : ℝ)|^79 ≤ (40915131470419/100000000000000 : ℝ)^63
        have hw : |(-490331431/1000000000 : ℝ)|=(490331431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4616574517/10000000000 : ℝ)*x 0 + (2894064947/5000000000 : ℝ)*x 1 + (1805039913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4616574517/10000000000 : ℝ)^79 ≤ (4742177017179/12500000000000 : ℝ)^63 := by
    have hnat : (4616574517 : ℕ)^79*12500000000000^63 ≤ 4742177017179^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616574517 10000000000 4742177017179 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2894064947/5000000000 : ℝ)^79 ≤ (1259419856153/2500000000000 : ℝ)^63 := by
    have hnat : (2894064947 : ℕ)^79*2500000000000^63 ≤ 1259419856153^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2894064947 5000000000 1259419856153 2500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805039913/10000000000 : ℝ)^79 ≤ (2921447399879/25000000000000 : ℝ)^63 := by
    have hnat : (1805039913 : ℕ)^79*25000000000000^63 ≤ 2921447399879^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805039913 10000000000 2921447399879 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4616574517/10000000000 : ℝ), (2894064947/5000000000 : ℝ), (1805039913/10000000000 : ℝ)] ![(4742177017179/12500000000000 : ℝ), (1259419856153/2500000000000 : ℝ), (2921447399879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4616574517/10000000000 : ℝ)|^79 ≤ (4742177017179/12500000000000 : ℝ)^63
        have hw : |(4616574517/10000000000 : ℝ)|=(4616574517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2894064947/5000000000 : ℝ)|^79 ≤ (1259419856153/2500000000000 : ℝ)^63
        have hw : |(2894064947/5000000000 : ℝ)|=(2894064947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1805039913/10000000000 : ℝ)|^79 ≤ (2921447399879/25000000000000 : ℝ)^63
        have hw : |(1805039913/10000000000 : ℝ)|=(1805039913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318062_s1_s1_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1427722771/2000000000 : ℝ)*x 0 + (1015925687/2500000000 : ℝ)*x 1 + (-93269717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1427722771/2000000000 : ℝ)^79 ≤ (32764720704457/50000000000000 : ℝ)^63 := by
    have hnat : (1427722771 : ℕ)^79*50000000000000^63 ≤ 32764720704457^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427722771 2000000000 32764720704457 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015925687/2500000000 : ℝ)^79 ≤ (8082403487463/25000000000000 : ℝ)^63 := by
    have hnat : (1015925687 : ℕ)^79*25000000000000^63 ≤ 8082403487463^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015925687 2500000000 8082403487463 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93269717/2000000000 : ℝ)^79 ≤ (428188925479/20000000000000 : ℝ)^63 := by
    have hnat : (93269717 : ℕ)^79*20000000000000^63 ≤ 428188925479^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93269717 2000000000 428188925479 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1427722771/2000000000 : ℝ), (1015925687/2500000000 : ℝ), (-93269717/2000000000 : ℝ)] ![(32764720704457/50000000000000 : ℝ), (8082403487463/25000000000000 : ℝ), (428188925479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1427722771/2000000000 : ℝ)|^79 ≤ (32764720704457/50000000000000 : ℝ)^63
        have hw : |(1427722771/2000000000 : ℝ)|=(1427722771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015925687/2500000000 : ℝ)|^79 ≤ (8082403487463/25000000000000 : ℝ)^63
        have hw : |(1015925687/2500000000 : ℝ)|=(1015925687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93269717/2000000000 : ℝ)|^79 ≤ (428188925479/20000000000000 : ℝ)^63
        have hw : |(-93269717/2000000000 : ℝ)|=(93269717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318062_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((15111/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15111/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74999/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74999/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64397/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64397/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4609/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4609/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46493/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46493/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7883/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (15111/20000 : ℝ) ^ (39/8 : ℝ) ≤ (12749793553380286521/50000000000000000000 : ℝ) := by
    have hpowers : (15111/20000 : ℝ)^39 ≤ (12749793553380286521/50000000000000000000 : ℝ)^8 := by
      have hnat : (15111 : ℕ)^39*50000000000000000000^8 ≤ 12749793553380286521^8*20000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15111 20000 12749793553380286521 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15111/20000 : ℝ)) (X := (12749793553380286521/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (62749793553380286521/50000000000000000000 : ℝ) ≤ (5238468318056731/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (62749793553380286521/50000000000000000000 : ℝ)^8 ≤ (5238468318056731/5000000000000000 : ℝ)^39 := by
      have hnat : (62749793553380286521 : ℕ)^8*5000000000000000^39 ≤ 5238468318056731^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62749793553380286521 50000000000000000000 5238468318056731 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5238468318056731/5000000000000000 : ℝ)) (X := (62749793553380286521/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (37749793553380286521/25000000000000000000 : ℝ) ≤ (1360262563483977/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (37749793553380286521/25000000000000000000 : ℝ)^8 ≤ (1360262563483977/1250000000000000 : ℝ)^39 := by
      have hnat : (37749793553380286521 : ℕ)^8*1250000000000000^39 ≤ 1360262563483977^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37749793553380286521 25000000000000000000 1360262563483977 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1360262563483977/1250000000000000 : ℝ)) (X := (37749793553380286521/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10368187741597/164250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(202581935879177/3777750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (15111/20000 : ℝ)) (alpha := (10368187741597/164250000000000 : ℝ)) (beta := (202581935879177/3777750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15111/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10368187741597/164250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(202581935879177/3777750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (74999/100000 : ℝ) ^ (39/8 : ℝ) ≤ (4919550526449300929/20000000000000000000 : ℝ) := by
    have hpowers : (74999/100000 : ℝ)^39 ≤ (4919550526449300929/20000000000000000000 : ℝ)^8 := by
      have hnat : (74999 : ℕ)^39*20000000000000000000^8 ≤ 4919550526449300929^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74999 100000 4919550526449300929 20000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74999/100000 : ℝ)) (X := (4919550526449300929/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (24919550526449300929/20000000000000000000 : ℝ) ≤ (2092289778604283/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (24919550526449300929/20000000000000000000 : ℝ)^8 ≤ (2092289778604283/2000000000000000 : ℝ)^39 := by
      have hnat : (24919550526449300929 : ℕ)^8*2000000000000000^39 ≤ 2092289778604283^39*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24919550526449300929 20000000000000000000 2092289778604283 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2092289778604283/2000000000000000 : ℝ)) (X := (24919550526449300929/20000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (14919550526449300929/10000000000000000000 : ℝ) ≤ (1356913664631813/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (14919550526449300929/10000000000000000000 : ℝ)^8 ≤ (1356913664631813/1250000000000000 : ℝ)^39 := by
      have hnat : (14919550526449300929 : ℕ)^8*1250000000000000^39 ≤ 1356913664631813^39*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14919550526449300929 10000000000000000000 1356913664631813 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1356913664631813/1250000000000000 : ℝ)) (X := (14919550526449300929/10000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(92289778604283/1499980000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(393860424033089/7499900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (74999/100000 : ℝ)) (alpha := (92289778604283/1499980000000000 : ℝ)) (beta := (393860424033089/7499900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (74999/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(92289778604283/1499980000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(393860424033089/7499900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (64397/100000 : ℝ) ^ (39/8 : ℝ) ≤ (11700919039997587829/100000000000000000000 : ℝ) := by
    have hpowers : (64397/100000 : ℝ)^39 ≤ (11700919039997587829/100000000000000000000 : ℝ)^8 := by
      have hnat : (64397 : ℕ)^39*100000000000000000000^8 ≤ 11700919039997587829^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64397 100000 11700919039997587829 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64397/100000 : ℝ)) (X := (11700919039997587829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (111700919039997587829/100000000000000000000 : ℝ) ≤ (5114789894625993/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (111700919039997587829/100000000000000000000 : ℝ)^8 ≤ (5114789894625993/5000000000000000 : ℝ)^39 := by
      have hnat : (111700919039997587829 : ℕ)^8*5000000000000000^39 ≤ 5114789894625993^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111700919039997587829 100000000000000000000 5114789894625993 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5114789894625993/5000000000000000 : ℝ)) (X := (111700919039997587829/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (61700919039997587829/50000000000000000000 : ℝ) ≤ (10440772716128581/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (61700919039997587829/50000000000000000000 : ℝ)^8 ≤ (10440772716128581/10000000000000000 : ℝ)^39 := by
      have hnat : (61700919039997587829 : ℕ)^8*10000000000000000^39 ≤ 10440772716128581^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61700919039997587829 50000000000000000000 10440772716128581 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10440772716128581/10000000000000000 : ℝ)) (X := (61700919039997587829/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(114789894625993/3219850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(42238585375319/1287940000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (64397/100000 : ℝ)) (alpha := (114789894625993/3219850000000000 : ℝ)) (beta := (42238585375319/1287940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64397/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(114789894625993/3219850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(42238585375319/1287940000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1401572597/10000000000 : ℝ)*X 0 0+(623704779/1250000000 : ℝ)*X 0 1+(-715415403/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1035996087/2000000000 : ℝ)*X 2 0+(5196632469/10000000000 : ℝ)*X 2 1+(1863488523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5520614731/10000000000 : ℝ)*X 0 0+(5505236897/10000000000 : ℝ)*X 0 1+(-948784787/10000000000 : ℝ)*X 0 2+(5520614731/10000000000 : ℝ)*X 1 0+(5505236897/10000000000 : ℝ)*X 1 1+(-948784787/10000000000 : ℝ)*X 1 2+(5520614731/10000000000 : ℝ)*X 2 0+(5505236897/10000000000 : ℝ)*X 2 1+(-948784787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1029124073/10000000000 : ℝ)*X 0 0+(2258246929/5000000000 : ℝ)*X 0 1+(-6415399073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2405149083/5000000000 : ℝ)*X 1 0+(-582058657/10000000000 : ℝ)*X 1 1+(-1281551419/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4782772017/10000000000 : ℝ)*X 2 0+(1571241273/2500000000 : ℝ)*X 2 1+(210268241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5045035127/10000000000 : ℝ)*X 0 0+(3167185041/5000000000 : ℝ)*X 0 1+(-291624997/10000000000 : ℝ)*X 0 2+(5045035127/10000000000 : ℝ)*X 1 0+(3167185041/5000000000 : ℝ)*X 1 1+(-291624997/10000000000 : ℝ)*X 1 2+(5045035127/10000000000 : ℝ)*X 2 0+(3167185041/5000000000 : ℝ)*X 2 1+(-291624997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-116317911/2000000000 : ℝ)*X 0 0+(4808660881/10000000000 : ℝ)*X 0 1+(-6409534321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((453815453/1000000000 : ℝ)*X 1 0+(-127380951/1250000000 : ℝ)*X 1 1+(-6401892903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6060027339/10000000000 : ℝ)*X 2 0+(627192613/1250000000 : ℝ)*X 2 1+(846937581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3437097173/5000000000 : ℝ)*X 0 0+(4450264157/10000000000 : ℝ)*X 0 1+(-307163027/10000000000 : ℝ)*X 0 2+(3437097173/5000000000 : ℝ)*X 1 0+(4450264157/10000000000 : ℝ)*X 1 1+(-307163027/10000000000 : ℝ)*X 1 2+(3437097173/5000000000 : ℝ)*X 2 0+(4450264157/10000000000 : ℝ)*X 2 1+(-307163027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-77738221/2500000000 : ℝ)*X 0 0+(5579253087/10000000000 : ℝ)*X 0 1+(-5808975499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((615244813/1000000000 : ℝ)*X 1 0+(-21828729/250000000 : ℝ)*X 1 1+(-490331431/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4616574517/10000000000 : ℝ)*X 2 0+(2894064947/5000000000 : ℝ)*X 2 1+(1805039913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1427722771/2000000000 : ℝ)*X 0 0+(1015925687/2500000000 : ℝ)*X 0 1+(-93269717/2000000000 : ℝ)*X 0 2+(1427722771/2000000000 : ℝ)*X 1 0+(1015925687/2500000000 : ℝ)*X 1 1+(-93269717/2000000000 : ℝ)*X 1 2+(1427722771/2000000000 : ℝ)*X 2 0+(1015925687/2500000000 : ℝ)*X 2 1+(-93269717/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((4609/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4609/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (273822345575619357661895226633/22035554626187500000000000000000000 : ℝ) := by norm_num
    linear_combination (1363371/500000000000 : ℝ)*(base39) + (8151997/1000000000000 : ℝ)*(base49) + (151967710233/1000000000000 : ℝ)*(base60) + (635891446629/125000000000 : ℝ)*(major_s1_0) + (635891446629/125000000000 : ℝ)*(major_s1_1) + (635891446629/125000000000 : ℝ)*(major_s1_2) + (39720881/500000000000 : ℝ)*(sp_s1_0) + (3693159951093/500000000000 : ℝ)*(sp_s1_7) + (7386258950043/1000000000000 : ℝ)*(sp_s1_8) + (7386291283311/1000000000000 : ℝ)*(sp_s1_9) + (1393925626259/500000000000 : ℝ)*(sp_s1_13) + (8407467/1000000000000 : ℝ)*(sp_s1_14) + (37200343/250000000000 : ℝ)*(sp_s1_15) + (14558513/125000000000 : ℝ)*(sp_s1_23) + (1393925626259/500000000000 : ℝ)*(f.failure) + (1477281550283/200000000000 : ℝ)*(f.sum) + (69804236159633898831/241485530150000000000000000000000 : ℝ)*base62 + (143061486438429/643970000000000000000000000 : ℝ)*base65 + (632675589544829/3749950000000000000000000000 : ℝ)*base67 + (203665911996491/804962500000000000000000000 : ℝ)*base68 + (229075238654579607/1175245250000000000000000000000 : ℝ)*base71 + (90823009008879/419750000000000000000000000 : ℝ)*base72 + (6267320013131/749990000000000000000000000 : ℝ)*base74 + (28305776291/1140625000000000000000000 : ℝ)*base77 + (2511994730440252967/15740415125000000000000000000000 : ℝ)*base79 + (441/2000000000000000 : ℝ)*base87 + (441/2000000000000000 : ℝ)*base89 + (441/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46493/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46493/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28563308420749571100889463/1762867875000000000000000000000 : ℝ) := by norm_num
    linear_combination (415569/1000000000000 : ℝ)*(base49) + (768829/250000000000 : ℝ)*(base60) + (5125691837093/1000000000000 : ℝ)*(major_s1_0) + (5125691837093/1000000000000 : ℝ)*(major_s1_1) + (5125691837093/1000000000000 : ℝ)*(major_s1_2) + (19476973/500000000000 : ℝ)*(sp_s1_2) + (2481817/500000000000 : ℝ)*(sp_s1_6) + (21942681/250000000000 : ℝ)*(sp_s1_7) + (67609873/1000000000000 : ℝ)*(sp_s1_8) + (93028843043/12500000000 : ℝ)*(sp_s1_14) + (7442327604291/1000000000000 : ℝ)*(sp_s1_15) + (3721178130109/500000000000 : ℝ)*(sp_s1_16) + (702199843447/250000000000 : ℝ)*(sp_s1_20) + (89360839/500000000000 : ℝ)*(sp_s1_27) + (28089830591/10000000000 : ℝ)*(f.failure) + (1860598803541/250000000000 : ℝ)*(f.sum) + (212459689058132200683/482971060300000000000000000000000 : ℝ)*base62 + (1163802203328007/1287940000000000000000000000 : ℝ)*base65 + (1150712958839283/7499900000000000000000000000 : ℝ)*base66 + (108295699052449/3219850000000000000000000000 : ℝ)*base69 + (9029038228286480099/21154414500000000000000000000000 : ℝ)*base71 + (1829857022175239/3777750000000000000000000000 : ℝ)*base72 + (737415364849727/1499980000000000000000000000 : ℝ)*base75 + (76106781239321/164250000000000000000000000 : ℝ)*base77 + (215460327282702467413/566654944500000000000000000000000 : ℝ)*base79 + (11/40000000000000 : ℝ)*base86 + (11/40000000000000 : ℝ)*base88 + (11/40000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7883/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5297483137849505044683/643970000000000000000000000 : ℝ) := by norm_num
    linear_combination (2005833/500000000000 : ℝ)*(base11) + (261950841083/500000000000 : ℝ)*(base39) + (693573/1000000000000 : ℝ)*(base43) + (338141/500000000000 : ℝ)*(base59) + (2008982880863/500000000000 : ℝ)*(major_s1_0) + (4017965068153/1000000000000 : ℝ)*(major_s1_1) + (2008982880863/500000000000 : ℝ)*(major_s1_2) + (15736537/1000000000000 : ℝ)*(sp_s1_0) + (5472669/125000000000 : ℝ)*(sp_s1_9) + (35029653/1000000000000 : ℝ)*(sp_s1_20) + (2916990815431/500000000000 : ℝ)*(sp_s1_21) + (5834002072637/1000000000000 : ℝ)*(sp_s1_22) + (5833957597713/1000000000000 : ℝ)*(sp_s1_23) + (2201891679061/1000000000000 : ℝ)*(sp_s1_27) + (1100963354357/500000000000 : ℝ)*(f.failure) + (5834002072637/1000000000000 : ℝ)*(f.sum) + (37786759689027860201/482971060300000000000000000000000 : ℝ)*base62 + (38300653791839/321985000000000000000000000 : ℝ)*base65 + (1900411375422803/7499900000000000000000000000 : ℝ)*base66 + (1617586799641463/3219850000000000000000000000 : ℝ)*base69 + (1524567863531779867/5288603625000000000000000000000 : ℝ)*base71 + (208359873503587/944437500000000000000000000 : ℝ)*base72 + (51526800895339/299996000000000000000000000 : ℝ)*base75 + (33908876744453/164250000000000000000000000 : ℝ)*base76 + (159903184857568022981/566654944500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (257/2000000000000000 : ℝ)*base86 + (257/2000000000000000 : ℝ)*base88 + (257/2000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((15111/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15111/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74999/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74999/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64397/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64397/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4609/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4609/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46493/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46493/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7883/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318062_s1 p hpa hpb X hX hprev0

#print axioms solution

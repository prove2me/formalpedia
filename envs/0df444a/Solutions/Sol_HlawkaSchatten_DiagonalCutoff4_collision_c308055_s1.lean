-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:05.190983+00:00
-- url     : https://prove2.me/submissions/1d93b457-ed97-4a76-910b-49b9fe5eb190

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
theorem collision_support_c308055_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044980409/10000000000 : ℝ)*x 0 + (2994343651/5000000000 : ℝ)*x 1 + (5268370273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044980409/10000000000 : ℝ)^69 ≤ (5284329059981/100000000000000 : ℝ)^53 := by
    have hnat : (1044980409 : ℕ)^69*100000000000000^53 ≤ 5284329059981^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044980409 10000000000 5284329059981 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2994343651/5000000000 : ℝ)^69 ≤ (25649624025063/50000000000000 : ℝ)^53 := by
    have hnat : (2994343651 : ℕ)^69*50000000000000^53 ≤ 25649624025063^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994343651 5000000000 25649624025063 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5268370273/10000000000 : ℝ)^69 ≤ (43416422879633/100000000000000 : ℝ)^53 := by
    have hnat : (5268370273 : ℕ)^69*100000000000000^53 ≤ 43416422879633^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268370273 10000000000 43416422879633 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044980409/10000000000 : ℝ), (2994343651/5000000000 : ℝ), (5268370273/10000000000 : ℝ)] ![(5284329059981/100000000000000 : ℝ), (25649624025063/50000000000000 : ℝ), (43416422879633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044980409/10000000000 : ℝ)|^69 ≤ (5284329059981/100000000000000 : ℝ)^53
        have hw : |(-1044980409/10000000000 : ℝ)|=(1044980409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2994343651/5000000000 : ℝ)|^69 ≤ (25649624025063/50000000000000 : ℝ)^53
        have hw : |(2994343651/5000000000 : ℝ)|=(2994343651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5268370273/10000000000 : ℝ)|^69 ≤ (43416422879633/100000000000000 : ℝ)^53
        have hw : |(5268370273/10000000000 : ℝ)|=(5268370273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6588379027/10000000000 : ℝ)*x 0 + (1888424357/5000000000 : ℝ)*x 1 + (2180079597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6588379027/10000000000 : ℝ)^69 ≤ (29042916481177/50000000000000 : ℝ)^53 := by
    have hnat : (6588379027 : ℕ)^69*50000000000000^53 ≤ 29042916481177^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6588379027 10000000000 29042916481177 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888424357/5000000000 : ℝ)^69 ≤ (1759343392829/6250000000000 : ℝ)^53 := by
    have hnat : (1888424357 : ℕ)^69*6250000000000^53 ≤ 1759343392829^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888424357 5000000000 1759343392829 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180079597/10000000000 : ℝ)^69 ≤ (1720584091917/12500000000000 : ℝ)^53 := by
    have hnat : (2180079597 : ℕ)^69*12500000000000^53 ≤ 1720584091917^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180079597 10000000000 1720584091917 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6588379027/10000000000 : ℝ), (1888424357/5000000000 : ℝ), (2180079597/10000000000 : ℝ)] ![(29042916481177/50000000000000 : ℝ), (1759343392829/6250000000000 : ℝ), (1720584091917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6588379027/10000000000 : ℝ)|^69 ≤ (29042916481177/50000000000000 : ℝ)^53
        have hw : |(6588379027/10000000000 : ℝ)|=(6588379027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1888424357/5000000000 : ℝ)|^69 ≤ (1759343392829/6250000000000 : ℝ)^53
        have hw : |(1888424357/5000000000 : ℝ)|=(1888424357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180079597/10000000000 : ℝ)|^69 ≤ (1720584091917/12500000000000 : ℝ)^53
        have hw : |(2180079597/10000000000 : ℝ)|=(2180079597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-359942759/1000000000 : ℝ)*x 0 + (4249404103/10000000000 : ℝ)*x 1 + (5017147487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359942759/1000000000 : ℝ)^69 ≤ (26440287808227/100000000000000 : ℝ)^53 := by
    have hnat : (359942759 : ℕ)^69*100000000000000^53 ≤ 26440287808227^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359942759 1000000000 26440287808227 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249404103/10000000000 : ℝ)^69 ≤ (32818987228783/100000000000000 : ℝ)^53 := by
    have hnat : (4249404103 : ℕ)^69*100000000000000^53 ≤ 32818987228783^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249404103 10000000000 32818987228783 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5017147487/10000000000 : ℝ)^69 ≤ (40740724949569/100000000000000 : ℝ)^53 := by
    have hnat : (5017147487 : ℕ)^69*100000000000000^53 ≤ 40740724949569^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017147487 10000000000 40740724949569 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359942759/1000000000 : ℝ), (4249404103/10000000000 : ℝ), (5017147487/10000000000 : ℝ)] ![(26440287808227/100000000000000 : ℝ), (32818987228783/100000000000000 : ℝ), (40740724949569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359942759/1000000000 : ℝ)|^69 ≤ (26440287808227/100000000000000 : ℝ)^53
        have hw : |(-359942759/1000000000 : ℝ)|=(359942759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249404103/10000000000 : ℝ)|^69 ≤ (32818987228783/100000000000000 : ℝ)^53
        have hw : |(4249404103/10000000000 : ℝ)|=(4249404103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5017147487/10000000000 : ℝ)|^69 ≤ (40740724949569/100000000000000 : ℝ)^53
        have hw : |(5017147487/10000000000 : ℝ)|=(5017147487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (583803103/2500000000 : ℝ)*x 0 + (1011417/10000000000 : ℝ)*x 1 + (4411067837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583803103/2500000000 : ℝ)^69 ≤ (14700513789/97656250000 : ℝ)^53 := by
    have hnat : (583803103 : ℕ)^69*97656250000^53 ≤ 14700513789^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583803103 2500000000 14700513789 97656250000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011417/10000000000 : ℝ)^69 ≤ (39332493/6250000000000 : ℝ)^53 := by
    have hnat : (1011417 : ℕ)^69*6250000000000^53 ≤ 39332493^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011417 10000000000 39332493 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4411067837/5000000000 : ℝ)^69 ≤ (16989208910513/20000000000000 : ℝ)^53 := by
    have hnat : (4411067837 : ℕ)^69*20000000000000^53 ≤ 16989208910513^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411067837 5000000000 16989208910513 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(583803103/2500000000 : ℝ), (1011417/10000000000 : ℝ), (4411067837/5000000000 : ℝ)] ![(14700513789/97656250000 : ℝ), (39332493/6250000000000 : ℝ), (16989208910513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(583803103/2500000000 : ℝ)|^69 ≤ (14700513789/97656250000 : ℝ)^53
        have hw : |(583803103/2500000000 : ℝ)|=(583803103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011417/10000000000 : ℝ)|^69 ≤ (39332493/6250000000000 : ℝ)^53
        have hw : |(1011417/10000000000 : ℝ)|=(1011417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4411067837/5000000000 : ℝ)|^69 ≤ (16989208910513/20000000000000 : ℝ)^53
        have hw : |(4411067837/5000000000 : ℝ)|=(4411067837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1911936491/10000000000 : ℝ)*x 0 + (8791822131/10000000000 : ℝ)*x 1 + (-408124377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911936491/10000000000 : ℝ)^69 ≤ (116027194261/1000000000000 : ℝ)^53 := by
    have hnat : (1911936491 : ℕ)^69*1000000000000^53 ≤ 116027194261^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911936491 10000000000 116027194261 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8791822131/10000000000 : ℝ)^69 ≤ (84566245513433/100000000000000 : ℝ)^53 := by
    have hnat : (8791822131 : ℕ)^69*100000000000000^53 ≤ 84566245513433^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8791822131 10000000000 84566245513433 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408124377/5000000000 : ℝ)^69 ≤ (383103505313/10000000000000 : ℝ)^53 := by
    have hnat : (408124377 : ℕ)^69*10000000000000^53 ≤ 383103505313^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408124377 5000000000 383103505313 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1911936491/10000000000 : ℝ), (8791822131/10000000000 : ℝ), (-408124377/5000000000 : ℝ)] ![(116027194261/1000000000000 : ℝ), (84566245513433/100000000000000 : ℝ), (383103505313/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1911936491/10000000000 : ℝ)|^69 ≤ (116027194261/1000000000000 : ℝ)^53
        have hw : |(1911936491/10000000000 : ℝ)|=(1911936491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8791822131/10000000000 : ℝ)|^69 ≤ (84566245513433/100000000000000 : ℝ)^53
        have hw : |(8791822131/10000000000 : ℝ)|=(8791822131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408124377/5000000000 : ℝ)|^69 ≤ (383103505313/10000000000000 : ℝ)^53
        have hw : |(-408124377/5000000000 : ℝ)|=(408124377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (377582169/1000000000 : ℝ)*x 0 + (929989067/1250000000 : ℝ)*x 1 + (813709693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377582169/1000000000 : ℝ)^69 ≤ (28139529292347/100000000000000 : ℝ)^53 := by
    have hnat : (377582169 : ℕ)^69*100000000000000^53 ≤ 28139529292347^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377582169 1000000000 28139529292347 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929989067/1250000000 : ℝ)^69 ≤ (17011235731291/25000000000000 : ℝ)^53 := by
    have hnat : (929989067 : ℕ)^69*25000000000000^53 ≤ 17011235731291^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929989067 1250000000 17011235731291 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (813709693/10000000000 : ℝ)^69 ≤ (3815527765597/100000000000000 : ℝ)^53 := by
    have hnat : (813709693 : ℕ)^69*100000000000000^53 ≤ 3815527765597^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813709693 10000000000 3815527765597 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(377582169/1000000000 : ℝ), (929989067/1250000000 : ℝ), (813709693/10000000000 : ℝ)] ![(28139529292347/100000000000000 : ℝ), (17011235731291/25000000000000 : ℝ), (3815527765597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(377582169/1000000000 : ℝ)|^69 ≤ (28139529292347/100000000000000 : ℝ)^53
        have hw : |(377582169/1000000000 : ℝ)|=(377582169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929989067/1250000000 : ℝ)|^69 ≤ (17011235731291/25000000000000 : ℝ)^53
        have hw : |(929989067/1250000000 : ℝ)|=(929989067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(813709693/10000000000 : ℝ)|^69 ≤ (3815527765597/100000000000000 : ℝ)^53
        have hw : |(813709693/10000000000 : ℝ)|=(813709693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-171400911/1000000000 : ℝ)*x 0 + (46694053/100000000 : ℝ)*x 1 + (6125692371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171400911/1000000000 : ℝ)^69 ≤ (5032013640799/50000000000000 : ℝ)^53 := by
    have hnat : (171400911 : ℕ)^69*50000000000000^53 ≤ 5032013640799^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171400911 1000000000 5032013640799 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46694053/100000000 : ℝ)^69 ≤ (7420719305823/20000000000000 : ℝ)^53 := by
    have hnat : (46694053 : ℕ)^69*20000000000000^53 ≤ 7420719305823^53*100000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46694053 100000000 7420719305823 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6125692371/10000000000 : ℝ)^69 ≤ (52832376179993/100000000000000 : ℝ)^53 := by
    have hnat : (6125692371 : ℕ)^69*100000000000000^53 ≤ 52832376179993^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6125692371 10000000000 52832376179993 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-171400911/1000000000 : ℝ), (46694053/100000000 : ℝ), (6125692371/10000000000 : ℝ)] ![(5032013640799/50000000000000 : ℝ), (7420719305823/20000000000000 : ℝ), (52832376179993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-171400911/1000000000 : ℝ)|^69 ≤ (5032013640799/50000000000000 : ℝ)^53
        have hw : |(-171400911/1000000000 : ℝ)|=(171400911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46694053/100000000 : ℝ)|^69 ≤ (7420719305823/20000000000000 : ℝ)^53
        have hw : |(46694053/100000000 : ℝ)|=(46694053/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6125692371/10000000000 : ℝ)|^69 ≤ (52832376179993/100000000000000 : ℝ)^53
        have hw : |(6125692371/10000000000 : ℝ)|=(6125692371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (331701091/2500000000 : ℝ)*x 0 + (-177607/40000000 : ℝ)*x 1 + (9434576137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331701091/2500000000 : ℝ)^69 ≤ (7210973131209/100000000000000 : ℝ)^53 := by
    have hnat : (331701091 : ℕ)^69*100000000000000^53 ≤ 7210973131209^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331701091 2500000000 7210973131209 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177607/40000000 : ℝ)^69 ≤ (5408306089/6250000000000 : ℝ)^53 := by
    have hnat : (177607 : ℕ)^69*6250000000000^53 ≤ 5408306089^53*40000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177607 40000000 5408306089 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9434576137/10000000000 : ℝ)^69 ≤ (46351246980841/50000000000000 : ℝ)^53 := by
    have hnat : (9434576137 : ℕ)^69*50000000000000^53 ≤ 46351246980841^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9434576137 10000000000 46351246980841 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331701091/2500000000 : ℝ), (-177607/40000000 : ℝ), (9434576137/10000000000 : ℝ)] ![(7210973131209/100000000000000 : ℝ), (5408306089/6250000000000 : ℝ), (46351246980841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331701091/2500000000 : ℝ)|^69 ≤ (7210973131209/100000000000000 : ℝ)^53
        have hw : |(331701091/2500000000 : ℝ)|=(331701091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177607/40000000 : ℝ)|^69 ≤ (5408306089/6250000000000 : ℝ)^53
        have hw : |(-177607/40000000 : ℝ)|=(177607/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9434576137/10000000000 : ℝ)|^69 ≤ (46351246980841/50000000000000 : ℝ)^53
        have hw : |(9434576137/10000000000 : ℝ)|=(9434576137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3802186351/5000000000 : ℝ)*x 0 + (724143471/2000000000 : ℝ)*x 1 + (-735684001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3802186351/5000000000 : ℝ)^69 ≤ (7000966567339/10000000000000 : ℝ)^53 := by
    have hnat : (3802186351 : ℕ)^69*10000000000000^53 ≤ 7000966567339^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3802186351 5000000000 7000966567339 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (724143471/2000000000 : ℝ)^69 ≤ (13322034443431/50000000000000 : ℝ)^53 := by
    have hnat : (724143471 : ℕ)^69*50000000000000^53 ≤ 13322034443431^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724143471 2000000000 13322034443431 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735684001/10000000000 : ℝ)^69 ≤ (1673132714557/50000000000000 : ℝ)^53 := by
    have hnat : (735684001 : ℕ)^69*50000000000000^53 ≤ 1673132714557^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735684001 10000000000 1673132714557 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3802186351/5000000000 : ℝ), (724143471/2000000000 : ℝ), (-735684001/10000000000 : ℝ)] ![(7000966567339/10000000000000 : ℝ), (13322034443431/50000000000000 : ℝ), (1673132714557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3802186351/5000000000 : ℝ)|^69 ≤ (7000966567339/10000000000000 : ℝ)^53
        have hw : |(3802186351/5000000000 : ℝ)|=(3802186351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(724143471/2000000000 : ℝ)|^69 ≤ (13322034443431/50000000000000 : ℝ)^53
        have hw : |(724143471/2000000000 : ℝ)|=(724143471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-735684001/10000000000 : ℝ)|^69 ≤ (1673132714557/50000000000000 : ℝ)^53
        have hw : |(-735684001/10000000000 : ℝ)|=(735684001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8873969987/10000000000 : ℝ)*x 0 + (1868264319/10000000000 : ℝ)*x 1 + (140281313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8873969987/10000000000 : ℝ)^69 ≤ (42798195267653/50000000000000 : ℝ)^53 := by
    have hnat : (8873969987 : ℕ)^69*50000000000000^53 ≤ 42798195267653^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8873969987 10000000000 42798195267653 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868264319/10000000000 : ℝ)^69 ≤ (11258879490773/100000000000000 : ℝ)^53 := by
    have hnat : (1868264319 : ℕ)^69*100000000000000^53 ≤ 11258879490773^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868264319 10000000000 11258879490773 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140281313/2000000000 : ℝ)^69 ≤ (1572364982681/50000000000000 : ℝ)^53 := by
    have hnat : (140281313 : ℕ)^69*50000000000000^53 ≤ 1572364982681^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140281313 2000000000 1572364982681 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8873969987/10000000000 : ℝ), (1868264319/10000000000 : ℝ), (140281313/2000000000 : ℝ)] ![(42798195267653/50000000000000 : ℝ), (11258879490773/100000000000000 : ℝ), (1572364982681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8873969987/10000000000 : ℝ)|^69 ≤ (42798195267653/50000000000000 : ℝ)^53
        have hw : |(8873969987/10000000000 : ℝ)|=(8873969987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1868264319/10000000000 : ℝ)|^69 ≤ (11258879490773/100000000000000 : ℝ)^53
        have hw : |(1868264319/10000000000 : ℝ)|=(1868264319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140281313/2000000000 : ℝ)|^69 ≤ (1572364982681/50000000000000 : ℝ)^53
        have hw : |(140281313/2000000000 : ℝ)|=(140281313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-584969271/5000000000 : ℝ)*x 0 + (8310034983/10000000000 : ℝ)*x 1 + (2363949283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (584969271/5000000000 : ℝ)^69 ≤ (6121442579111/100000000000000 : ℝ)^53 := by
    have hnat : (584969271 : ℕ)^69*100000000000000^53 ≤ 6121442579111^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584969271 5000000000 6121442579111 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8310034983/10000000000 : ℝ)^69 ≤ (19645904274851/25000000000000 : ℝ)^53 := by
    have hnat : (8310034983 : ℕ)^69*25000000000000^53 ≤ 19645904274851^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8310034983 10000000000 19645904274851 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363949283/10000000000 : ℝ)^69 ≤ (15294940309777/100000000000000 : ℝ)^53 := by
    have hnat : (2363949283 : ℕ)^69*100000000000000^53 ≤ 15294940309777^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363949283 10000000000 15294940309777 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-584969271/5000000000 : ℝ), (8310034983/10000000000 : ℝ), (2363949283/10000000000 : ℝ)] ![(6121442579111/100000000000000 : ℝ), (19645904274851/25000000000000 : ℝ), (15294940309777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-584969271/5000000000 : ℝ)|^69 ≤ (6121442579111/100000000000000 : ℝ)^53
        have hw : |(-584969271/5000000000 : ℝ)|=(584969271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8310034983/10000000000 : ℝ)|^69 ≤ (19645904274851/25000000000000 : ℝ)^53
        have hw : |(8310034983/10000000000 : ℝ)|=(8310034983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363949283/10000000000 : ℝ)|^69 ≤ (15294940309777/100000000000000 : ℝ)^53
        have hw : |(2363949283/10000000000 : ℝ)|=(2363949283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7682720217/10000000000 : ℝ)*x 0 + (-4135783/10000000000 : ℝ)*x 1 + (773778547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7682720217/10000000000 : ℝ)^69 ≤ (17737545490433/25000000000000 : ℝ)^53 := by
    have hnat : (7682720217 : ℕ)^69*25000000000000^53 ≤ 17737545490433^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7682720217 10000000000 17737545490433 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135783/10000000000 : ℝ)^69 ≤ (492097577/12500000000000 : ℝ)^53 := by
    have hnat : (4135783 : ℕ)^69*12500000000000^53 ≤ 492097577^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135783 10000000000 492097577 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773778547/2000000000 : ℝ)^69 ≤ (14522940625149/50000000000000 : ℝ)^53 := by
    have hnat : (773778547 : ℕ)^69*50000000000000^53 ≤ 14522940625149^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773778547 2000000000 14522940625149 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7682720217/10000000000 : ℝ), (-4135783/10000000000 : ℝ), (773778547/2000000000 : ℝ)] ![(17737545490433/25000000000000 : ℝ), (492097577/12500000000000 : ℝ), (14522940625149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7682720217/10000000000 : ℝ)|^69 ≤ (17737545490433/25000000000000 : ℝ)^53
        have hw : |(7682720217/10000000000 : ℝ)|=(7682720217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4135783/10000000000 : ℝ)|^69 ≤ (492097577/12500000000000 : ℝ)^53
        have hw : |(-4135783/10000000000 : ℝ)|=(4135783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773778547/2000000000 : ℝ)|^69 ≤ (14522940625149/50000000000000 : ℝ)^53
        have hw : |(773778547/2000000000 : ℝ)|=(773778547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (556964979/5000000000 : ℝ)*x 0 + (4410235681/5000000000 : ℝ)*x 1 + (-1617428287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (556964979/5000000000 : ℝ)^69 ≤ (179459680217/3125000000000 : ℝ)^53 := by
    have hnat : (556964979 : ℕ)^69*3125000000000^53 ≤ 179459680217^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556964979 5000000000 179459680217 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4410235681/5000000000 : ℝ)^69 ≤ (21231295529029/25000000000000 : ℝ)^53 := by
    have hnat : (4410235681 : ℕ)^69*25000000000000^53 ≤ 21231295529029^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410235681 5000000000 21231295529029 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1617428287/10000000000 : ℝ)^69 ≤ (9332108112571/100000000000000 : ℝ)^53 := by
    have hnat : (1617428287 : ℕ)^69*100000000000000^53 ≤ 9332108112571^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617428287 10000000000 9332108112571 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(556964979/5000000000 : ℝ), (4410235681/5000000000 : ℝ), (-1617428287/10000000000 : ℝ)] ![(179459680217/3125000000000 : ℝ), (21231295529029/25000000000000 : ℝ), (9332108112571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(556964979/5000000000 : ℝ)|^69 ≤ (179459680217/3125000000000 : ℝ)^53
        have hw : |(556964979/5000000000 : ℝ)|=(556964979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4410235681/5000000000 : ℝ)|^69 ≤ (21231295529029/25000000000000 : ℝ)^53
        have hw : |(4410235681/5000000000 : ℝ)|=(4410235681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1617428287/10000000000 : ℝ)|^69 ≤ (9332108112571/100000000000000 : ℝ)^53
        have hw : |(-1617428287/10000000000 : ℝ)|=(1617428287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8432439329/10000000000 : ℝ)*x 0 + (408879183/2000000000 : ℝ)*x 1 + (266353027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8432439329/10000000000 : ℝ)^69 ≤ (2002347687093/2500000000000 : ℝ)^53 := by
    have hnat : (8432439329 : ℕ)^69*2500000000000^53 ≤ 2002347687093^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8432439329 10000000000 2002347687093 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408879183/2000000000 : ℝ)^69 ≤ (12659999400173/100000000000000 : ℝ)^53 := by
    have hnat : (408879183 : ℕ)^69*100000000000000^53 ≤ 12659999400173^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408879183 2000000000 12659999400173 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266353027/2000000000 : ℝ)^69 ≤ (905761638329/12500000000000 : ℝ)^53 := by
    have hnat : (266353027 : ℕ)^69*12500000000000^53 ≤ 905761638329^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266353027 2000000000 905761638329 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8432439329/10000000000 : ℝ), (408879183/2000000000 : ℝ), (266353027/2000000000 : ℝ)] ![(2002347687093/2500000000000 : ℝ), (12659999400173/100000000000000 : ℝ), (905761638329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8432439329/10000000000 : ℝ)|^69 ≤ (2002347687093/2500000000000 : ℝ)^53
        have hw : |(8432439329/10000000000 : ℝ)|=(8432439329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(408879183/2000000000 : ℝ)|^69 ≤ (12659999400173/100000000000000 : ℝ)^53
        have hw : |(408879183/2000000000 : ℝ)|=(408879183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266353027/2000000000 : ℝ)|^69 ≤ (905761638329/12500000000000 : ℝ)^53
        have hw : |(266353027/2000000000 : ℝ)|=(266353027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308055_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((46361/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46361/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3681/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3681/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((85179/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85179/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83651/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83651/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42061/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42061/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (46361/50000 : ℝ) ^ (17/4 : ℝ) ≤ (36265766828460997219/50000000000000000000 : ℝ) := by
    have hpowers : (46361/50000 : ℝ)^17 ≤ (36265766828460997219/50000000000000000000 : ℝ)^4 := by
      have hnat : (46361 : ℕ)^17*50000000000000000000^4 ≤ 36265766828460997219^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46361 50000 36265766828460997219 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46361/50000 : ℝ)) (X := (36265766828460997219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (86265766828460997219/50000000000000000000 : ℝ) ≤ (1136930089977471/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (86265766828460997219/50000000000000000000 : ℝ)^4 ≤ (1136930089977471/1000000000000000 : ℝ)^17 := by
      have hnat : (86265766828460997219 : ℕ)^4*1000000000000000^17 ≤ 1136930089977471^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86265766828460997219 50000000000000000000 1136930089977471 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1136930089977471/1000000000000000 : ℝ)) (X := (86265766828460997219/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (61265766828460997219/25000000000000000000 : ℝ) ≤ (12347947996269261/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (61265766828460997219/25000000000000000000 : ℝ)^4 ≤ (12347947996269261/10000000000000000 : ℝ)^17 := by
      have hnat : (61265766828460997219 : ℕ)^4*10000000000000000^17 ≤ 12347947996269261^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61265766828460997219 25000000000000000000 12347947996269261 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12347947996269261/10000000000000000 : ℝ)) (X := (61265766828460997219/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19561441425353/132460000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(978647096494551/9272200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (46361/50000 : ℝ)) (alpha := (19561441425353/132460000000000 : ℝ)) (beta := (978647096494551/9272200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (46361/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19561441425353/132460000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(978647096494551/9272200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (92297/100000 : ℝ) ^ (17/4 : ℝ) ≤ (35564543684394481823/50000000000000000000 : ℝ) := by
    have hpowers : (92297/100000 : ℝ)^17 ≤ (35564543684394481823/50000000000000000000 : ℝ)^4 := by
      have hnat : (92297 : ℕ)^17*50000000000000000000^4 ≤ 35564543684394481823^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92297 100000 35564543684394481823 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92297/100000 : ℝ)) (X := (35564543684394481823/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (85564543684394481823/50000000000000000000 : ℝ) ≤ (11347487831776203/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (85564543684394481823/50000000000000000000 : ℝ)^4 ≤ (11347487831776203/10000000000000000 : ℝ)^17 := by
      have hnat : (85564543684394481823 : ℕ)^4*10000000000000000^17 ≤ 11347487831776203^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85564543684394481823 50000000000000000000 11347487831776203 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11347487831776203/10000000000000000 : ℝ)) (X := (85564543684394481823/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60564543684394481823/25000000000000000000 : ℝ) ≤ (6157273727335949/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (60564543684394481823/25000000000000000000 : ℝ)^4 ≤ (6157273727335949/5000000000000000 : ℝ)^17 := by
      have hnat : (60564543684394481823 : ℕ)^4*5000000000000000^17 ≤ 6157273727335949^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60564543684394481823 25000000000000000000 6157273727335949 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6157273727335949/5000000000000000 : ℝ)) (X := (60564543684394481823/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1347487831776203/9229700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(193411924579139/1845940000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (92297/100000 : ℝ)) (alpha := (1347487831776203/9229700000000000 : ℝ)) (beta := (193411924579139/1845940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (92297/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1347487831776203/9229700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(193411924579139/1845940000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3681/4000 : ℝ) ^ (17/4 : ℝ) ≤ (70242467791483206983/100000000000000000000 : ℝ) := by
    have hpowers : (3681/4000 : ℝ)^17 ≤ (70242467791483206983/100000000000000000000 : ℝ)^4 := by
      have hnat : (3681 : ℕ)^17*100000000000000000000^4 ≤ 70242467791483206983^4*4000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 4000 70242467791483206983 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/4000 : ℝ)) (X := (70242467791483206983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (170242467791483206983/100000000000000000000 : ℝ) ≤ (2266725418607389/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (170242467791483206983/100000000000000000000 : ℝ)^4 ≤ (2266725418607389/2000000000000000 : ℝ)^17 := by
      have hnat : (170242467791483206983 : ℕ)^4*2000000000000000^17 ≤ 2266725418607389^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        170242467791483206983 100000000000000000000 2266725418607389 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2266725418607389/2000000000000000 : ℝ)) (X := (170242467791483206983/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (120242467791483206983/50000000000000000000 : ℝ) ≤ (12293278928441357/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (120242467791483206983/50000000000000000000 : ℝ)^4 ≤ (12293278928441357/10000000000000000 : ℝ)^17 := by
      have hnat : (120242467791483206983 : ℕ)^4*10000000000000000^17 ≤ 12293278928441357^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120242467791483206983 50000000000000000000 12293278928441357 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12293278928441357/10000000000000000 : ℝ)) (X := (120242467791483206983/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(266725418607389/1840500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(79970986283701/766875000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3681/4000 : ℝ)) (alpha := (266725418607389/1840500000000000 : ℝ)) (beta := (79970986283701/766875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3681/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(266725418607389/1840500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(79970986283701/766875000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1044980409/10000000000 : ℝ)*X 0 0+(2994343651/5000000000 : ℝ)*X 0 1+(5268370273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6588379027/10000000000 : ℝ)*X 0 0+(1888424357/5000000000 : ℝ)*X 0 1+(2180079597/10000000000 : ℝ)*X 0 2+(6588379027/10000000000 : ℝ)*X 1 0+(1888424357/5000000000 : ℝ)*X 1 1+(2180079597/10000000000 : ℝ)*X 1 2+(6588379027/10000000000 : ℝ)*X 2 0+(1888424357/5000000000 : ℝ)*X 2 1+(2180079597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-359942759/1000000000 : ℝ)*X 0 0+(4249404103/10000000000 : ℝ)*X 0 1+(5017147487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((583803103/2500000000 : ℝ)*X 1 0+(1011417/10000000000 : ℝ)*X 1 1+(4411067837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1911936491/10000000000 : ℝ)*X 2 0+(8791822131/10000000000 : ℝ)*X 2 1+(-408124377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((377582169/1000000000 : ℝ)*X 0 0+(929989067/1250000000 : ℝ)*X 0 1+(813709693/10000000000 : ℝ)*X 0 2+(377582169/1000000000 : ℝ)*X 1 0+(929989067/1250000000 : ℝ)*X 1 1+(813709693/10000000000 : ℝ)*X 1 2+(377582169/1000000000 : ℝ)*X 2 0+(929989067/1250000000 : ℝ)*X 2 1+(813709693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-171400911/1000000000 : ℝ)*X 0 0+(46694053/100000000 : ℝ)*X 0 1+(6125692371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((331701091/2500000000 : ℝ)*X 1 0+(-177607/40000000 : ℝ)*X 1 1+(9434576137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3802186351/5000000000 : ℝ)*X 2 0+(724143471/2000000000 : ℝ)*X 2 1+(-735684001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8873969987/10000000000 : ℝ)*X 0 0+(1868264319/10000000000 : ℝ)*X 0 1+(140281313/2000000000 : ℝ)*X 0 2+(8873969987/10000000000 : ℝ)*X 1 0+(1868264319/10000000000 : ℝ)*X 1 1+(140281313/2000000000 : ℝ)*X 1 2+(8873969987/10000000000 : ℝ)*X 2 0+(1868264319/10000000000 : ℝ)*X 2 1+(140281313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-584969271/5000000000 : ℝ)*X 0 0+(8310034983/10000000000 : ℝ)*X 0 1+(2363949283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7682720217/10000000000 : ℝ)*X 1 0+(-4135783/10000000000 : ℝ)*X 1 1+(773778547/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((556964979/5000000000 : ℝ)*X 2 0+(4410235681/5000000000 : ℝ)*X 2 1+(-1617428287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8432439329/10000000000 : ℝ)*X 0 0+(408879183/2000000000 : ℝ)*X 0 1+(266353027/2000000000 : ℝ)*X 0 2+(8432439329/10000000000 : ℝ)*X 1 0+(408879183/2000000000 : ℝ)*X 1 1+(266353027/2000000000 : ℝ)*X 1 2+(8432439329/10000000000 : ℝ)*X 2 0+(408879183/2000000000 : ℝ)*X 2 1+(266353027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((85179/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85179/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3701772604701179187070494437063/218762914719125000000000000000000000 : ℝ) := by norm_num
    linear_combination (23092804667/31250000000 : ℝ)*(base7) + (10011567/1000000000000 : ℝ)*(base23) + (621469/1000000000000 : ℝ)*(base49) + (856443389423/1000000000000 : ℝ)*(base53) + (1184897/500000000000 : ℝ)*(base60) + (101217051617/62500000000 : ℝ)*(major_s1_0) + (101217051617/62500000000 : ℝ)*(major_s1_1) + (763029436449/1000000000000 : ℝ)*(major_s1_2) + (30381743/1000000000000 : ℝ)*(sp_s1_0) + (55946738439/62500000000 : ℝ)*(sp_s1_7) + (44758910901/50000000000 : ℝ)*(sp_s1_8) + (437902898969/250000000000 : ℝ)*(sp_s1_9) + (1772383374343/1000000000000 : ℝ)*(sp_s1_13) + (21253/1000000000000 : ℝ)*(sp_s1_21) + (1033413624999/1000000000000 : ℝ)*(f.failure) + (1751621607443/1000000000000 : ℝ)*(f.sum) + (11345554644190124449/56624209500000000000000000000000 : ℝ)*base63 + (41100255360459/511250000000000000000000000 : ℝ)*base64 + (391454704976871/922970000000000000000000000 : ℝ)*base67 + (870649895387/613500000000000000000000000 : ℝ)*base69 + (165708821035214459/1693004375000000000000000000000 : ℝ)*base71 + (302771758602773/2318050000000000000000000000 : ℝ)*base73 + (149342727707601/2307425000000000000000000000 : ℝ)*base74 + (3386632470279/16557500000000000000000000 : ℝ)*base77 + (44969352226164864501/213949060850000000000000000000000 : ℝ)*base79 + (18289/100000000000000000 : ℝ)*base87 + (18289/100000000000000000 : ℝ)*base89 + (18289/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83651/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83651/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4180870866222804675357741/846502187500000000000000000000 : ℝ) := by norm_num
    linear_combination (184390698029/250000000000 : ℝ)*(base7) + (56367/15625000000 : ℝ)*(base34) + (161537274771/250000000000 : ℝ)*(base53) + (1513501192929/1000000000000 : ℝ)*(major_s1_0) + (1513504800417/1000000000000 : ℝ)*(major_s1_1) + (867355701333/1000000000000 : ℝ)*(major_s1_2) + (45682441/1000000000000 : ℝ)*(sp_s1_0) + (2169559/1000000000000 : ℝ)*(sp_s1_7) + (68670959/1000000000000 : ℝ)*(sp_s1_8) + (961973231647/1000000000000 : ℝ)*(sp_s1_14) + (60122251261/62500000000 : ℝ)*(sp_s1_15) + (1608173790219/1000000000000 : ℝ)*(sp_s1_16) + (425835539321/250000000000 : ℝ)*(sp_s1_20) + (10622189/1000000000000 : ℝ)*(sp_s1_27) + (241448398711/250000000000 : ℝ)*(f.failure) + (1608173790219/1000000000000 : ℝ)*(f.sum) + (1011334758264957119/7078026187500000000000000000000 : ℝ)*base62 + (14438508964121/15976562500000000000000000 : ℝ)*base65 + (273064983592413/369188000000000000000000000 : ℝ)*base67 + (41877255480829/613500000000000000000000000 : ℝ)*base69 + (35861829645173637/6772017500000000000000000000000 : ℝ)*base71 + (7157549333379219/9272200000000000000000000000 : ℝ)*base73 + (3162401770802461/9229700000000000000000000000 : ℝ)*base75 + (68994815405041/132460000000000000000000000 : ℝ)*base77 + (83458212507883735407/855796243400000000000000000000000 : ℝ)*base78 + (25479/25000000000000000 : ℝ)*base86 + (25479/25000000000000000 : ℝ)*base88 + (25479/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42061/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42061/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28886797434133659063085934535641/2187629147191250000000000000000000000 : ℝ) := by norm_num
    linear_combination (902296548921/1000000000000 : ℝ)*(base7) + (110004587487/500000000000 : ℝ)*(base43) + (8234760379/500000000000 : ℝ)*(base50) + (378268774773/250000000000 : ℝ)*(major_s1_0) + (646532962059/500000000000 : ℝ)*(major_s1_1) + (378268774773/250000000000 : ℝ)*(major_s1_2) + (18353163/1000000000000 : ℝ)*(sp_s1_6) + (115019/200000000000 : ℝ)*(sp_s1_7) + (8286091/125000000000 : ℝ)*(sp_s1_9) + (47544203/500000000000 : ℝ)*(sp_s1_20) + (257278003873/200000000000 : ℝ)*(sp_s1_21) + (753199884717/500000000000 : ℝ)*(sp_s1_22) + (321581076433/250000000000 : ℝ)*(sp_s1_23) + (1867702502349/1000000000000 : ℝ)*(sp_s1_27) + (241379848749/250000000000 : ℝ)*(f.failure) + (753199884717/500000000000 : ℝ)*(f.sum) + (22036774306075531499/28312104750000000000000000000000 : ℝ)*base62 + (209566665296047/511250000000000000000000000 : ℝ)*base64 + (507917025178873/922970000000000000000000000 : ℝ)*base66 + (52850108870069/38343750000000000000000000 : ℝ)*base68 + (1115285215429187281/3386008750000000000000000000000 : ℝ)*base70 + (949645161092907/2318050000000000000000000000 : ℝ)*base72 + (5435380036075303/4614850000000000000000000000 : ℝ)*base74 + (41769786655471/66230000000000000000000000 : ℝ)*base76 + (8115740493407385187/106974530425000000000000000000000 : ℝ)*base78 + (4539/25000000000000000 : ℝ)*base87 + (4539/25000000000000000 : ℝ)*base89 + (4539/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((46361/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46361/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3681/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3681/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((85179/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85179/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83651/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83651/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42061/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42061/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308055_s1 p hpa hpb X hX hprev0

#print axioms solution

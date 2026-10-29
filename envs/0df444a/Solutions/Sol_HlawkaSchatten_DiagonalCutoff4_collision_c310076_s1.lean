-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310076_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:03.389591+00:00
-- url     : https://prove2.me/submissions/820d33fd-cde9-47a9-ade3-51b2d5946161

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
theorem collision_support_c310076_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1518902071/10000000000 : ℝ)*x 0 + (-1535285337/2500000000 : ℝ)*x 1 + (2359599273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1518902071/10000000000 : ℝ)^71 ≤ (8778682557471/100000000000000 : ℝ)^55 := by
    have hnat : (1518902071 : ℕ)^71*100000000000000^55 ≤ 8778682557471^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518902071 10000000000 8778682557471 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1535285337/2500000000 : ℝ)^71 ≤ (1665324423517/3125000000000 : ℝ)^55 := by
    have hnat : (1535285337 : ℕ)^71*3125000000000^55 ≤ 1665324423517^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535285337 2500000000 1665324423517 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2359599273/5000000000 : ℝ)^71 ≤ (18965467938211/50000000000000 : ℝ)^55 := by
    have hnat : (2359599273 : ℕ)^71*50000000000000^55 ≤ 18965467938211^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359599273 5000000000 18965467938211 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1518902071/10000000000 : ℝ), (-1535285337/2500000000 : ℝ), (2359599273/5000000000 : ℝ)] ![(8778682557471/100000000000000 : ℝ), (1665324423517/3125000000000 : ℝ), (18965467938211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1518902071/10000000000 : ℝ)|^71 ≤ (8778682557471/100000000000000 : ℝ)^55
        have hw : |(-1518902071/10000000000 : ℝ)|=(1518902071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1535285337/2500000000 : ℝ)|^71 ≤ (1665324423517/3125000000000 : ℝ)^55
        have hw : |(-1535285337/2500000000 : ℝ)|=(1535285337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2359599273/5000000000 : ℝ)|^71 ≤ (18965467938211/50000000000000 : ℝ)^55
        have hw : |(2359599273/5000000000 : ℝ)|=(2359599273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3120296633/5000000000 : ℝ)*x 0 + (107143279/312500000 : ℝ)*x 1 + (1463909137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3120296633/5000000000 : ℝ)^71 ≤ (1360176393419/2500000000000 : ℝ)^55 := by
    have hnat : (3120296633 : ℕ)^71*2500000000000^55 ≤ 1360176393419^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120296633 5000000000 1360176393419 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107143279/312500000 : ℝ)^71 ≤ (1004466840923/4000000000000 : ℝ)^55 := by
    have hnat : (107143279 : ℕ)^71*4000000000000^55 ≤ 1004466840923^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107143279 312500000 1004466840923 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1463909137/5000000000 : ℝ)^71 ≤ (2560159152997/12500000000000 : ℝ)^55 := by
    have hnat : (1463909137 : ℕ)^71*12500000000000^55 ≤ 2560159152997^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463909137 5000000000 2560159152997 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3120296633/5000000000 : ℝ), (107143279/312500000 : ℝ), (1463909137/5000000000 : ℝ)] ![(1360176393419/2500000000000 : ℝ), (1004466840923/4000000000000 : ℝ), (2560159152997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3120296633/5000000000 : ℝ)|^71 ≤ (1360176393419/2500000000000 : ℝ)^55
        have hw : |(3120296633/5000000000 : ℝ)|=(3120296633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107143279/312500000 : ℝ)|^71 ≤ (1004466840923/4000000000000 : ℝ)^55
        have hw : |(107143279/312500000 : ℝ)|=(107143279/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1463909137/5000000000 : ℝ)|^71 ≤ (2560159152997/12500000000000 : ℝ)^55
        have hw : |(1463909137/5000000000 : ℝ)|=(1463909137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (946099009/2000000000 : ℝ)*x 0 + (-1139614147/2500000000 : ℝ)*x 1 + (-3488581617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946099009/2000000000 : ℝ)^71 ≤ (38048186709451/100000000000000 : ℝ)^55 := by
    have hnat : (946099009 : ℕ)^71*100000000000000^55 ≤ 38048186709451^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946099009 2000000000 38048186709451 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139614147/2500000000 : ℝ)^71 ≤ (3627144238931/10000000000000 : ℝ)^55 := by
    have hnat : (1139614147 : ℕ)^71*10000000000000^55 ≤ 3627144238931^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139614147 2500000000 3627144238931 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3488581617/10000000000 : ℝ)^71 ≤ (25680370887917/100000000000000 : ℝ)^55 := by
    have hnat : (3488581617 : ℕ)^71*100000000000000^55 ≤ 25680370887917^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3488581617 10000000000 25680370887917 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(946099009/2000000000 : ℝ), (-1139614147/2500000000 : ℝ), (-3488581617/10000000000 : ℝ)] ![(38048186709451/100000000000000 : ℝ), (3627144238931/10000000000000 : ℝ), (25680370887917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(946099009/2000000000 : ℝ)|^71 ≤ (38048186709451/100000000000000 : ℝ)^55
        have hw : |(946099009/2000000000 : ℝ)|=(946099009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139614147/2500000000 : ℝ)|^71 ≤ (3627144238931/10000000000000 : ℝ)^55
        have hw : |(-1139614147/2500000000 : ℝ)|=(1139614147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3488581617/10000000000 : ℝ)|^71 ≤ (25680370887917/100000000000000 : ℝ)^55
        have hw : |(-3488581617/10000000000 : ℝ)|=(3488581617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-271264377/2000000000 : ℝ)*x 0 + (-209702587/312500000 : ℝ)*x 1 + (4203010607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271264377/2000000000 : ℝ)^71 ≤ (7585063333511/100000000000000 : ℝ)^55 := by
    have hnat : (271264377 : ℕ)^71*100000000000000^55 ≤ 7585063333511^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271264377 2000000000 7585063333511 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209702587/312500000 : ℝ)^71 ≤ (59752332373633/100000000000000 : ℝ)^55 := by
    have hnat : (209702587 : ℕ)^71*100000000000000^55 ≤ 59752332373633^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209702587 312500000 59752332373633 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4203010607/10000000000 : ℝ)^71 ≤ (8165651068937/25000000000000 : ℝ)^55 := by
    have hnat : (4203010607 : ℕ)^71*25000000000000^55 ≤ 8165651068937^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203010607 10000000000 8165651068937 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271264377/2000000000 : ℝ), (-209702587/312500000 : ℝ), (4203010607/10000000000 : ℝ)] ![(7585063333511/100000000000000 : ℝ), (59752332373633/100000000000000 : ℝ), (8165651068937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271264377/2000000000 : ℝ)|^71 ≤ (7585063333511/100000000000000 : ℝ)^55
        have hw : |(-271264377/2000000000 : ℝ)|=(271264377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209702587/312500000 : ℝ)|^71 ≤ (59752332373633/100000000000000 : ℝ)^55
        have hw : |(-209702587/312500000 : ℝ)|=(209702587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4203010607/10000000000 : ℝ)|^71 ≤ (8165651068937/25000000000000 : ℝ)^55
        have hw : |(4203010607/10000000000 : ℝ)|=(4203010607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (244457327/400000000 : ℝ)*x 0 + (1681912189/5000000000 : ℝ)*x 1 + (3153434367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244457327/400000000 : ℝ)^71 ≤ (52957825166229/100000000000000 : ℝ)^55 := by
    have hnat : (244457327 : ℕ)^71*100000000000000^55 ≤ 52957825166229^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244457327 400000000 52957825166229 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1681912189/5000000000 : ℝ)^71 ≤ (3062632141771/12500000000000 : ℝ)^55 := by
    have hnat : (1681912189 : ℕ)^71*12500000000000^55 ≤ 3062632141771^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681912189 5000000000 3062632141771 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3153434367/10000000000 : ℝ)^71 ≤ (22541117674959/100000000000000 : ℝ)^55 := by
    have hnat : (3153434367 : ℕ)^71*100000000000000^55 ≤ 22541117674959^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3153434367 10000000000 22541117674959 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(244457327/400000000 : ℝ), (1681912189/5000000000 : ℝ), (3153434367/10000000000 : ℝ)] ![(52957825166229/100000000000000 : ℝ), (3062632141771/12500000000000 : ℝ), (22541117674959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(244457327/400000000 : ℝ)|^71 ≤ (52957825166229/100000000000000 : ℝ)^55
        have hw : |(244457327/400000000 : ℝ)|=(244457327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1681912189/5000000000 : ℝ)|^71 ≤ (3062632141771/12500000000000 : ℝ)^55
        have hw : |(1681912189/5000000000 : ℝ)|=(1681912189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3153434367/10000000000 : ℝ)|^71 ≤ (22541117674959/100000000000000 : ℝ)^55
        have hw : |(3153434367/10000000000 : ℝ)|=(3153434367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2275360803/5000000000 : ℝ)*x 0 + (-7596457/16000000 : ℝ)*x 1 + (-695606701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2275360803/5000000000 : ℝ)^71 ≤ (1809600526543/5000000000000 : ℝ)^55 := by
    have hnat : (2275360803 : ℕ)^71*5000000000000^55 ≤ 1809600526543^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275360803 5000000000 1809600526543 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7596457/16000000 : ℝ)^71 ≤ (38227810239721/100000000000000 : ℝ)^55 := by
    have hnat : (7596457 : ℕ)^71*100000000000000^55 ≤ 38227810239721^55*16000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7596457 16000000 38227810239721 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695606701/2000000000 : ℝ)^71 ≤ (25580179218049/100000000000000 : ℝ)^55 := by
    have hnat : (695606701 : ℕ)^71*100000000000000^55 ≤ 25580179218049^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695606701 2000000000 25580179218049 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2275360803/5000000000 : ℝ), (-7596457/16000000 : ℝ), (-695606701/2000000000 : ℝ)] ![(1809600526543/5000000000000 : ℝ), (38227810239721/100000000000000 : ℝ), (25580179218049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2275360803/5000000000 : ℝ)|^71 ≤ (1809600526543/5000000000000 : ℝ)^55
        have hw : |(2275360803/5000000000 : ℝ)|=(2275360803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7596457/16000000 : ℝ)|^71 ≤ (38227810239721/100000000000000 : ℝ)^55
        have hw : |(-7596457/16000000 : ℝ)|=(7596457/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-695606701/2000000000 : ℝ)|^71 ≤ (25580179218049/100000000000000 : ℝ)^55
        have hw : |(-695606701/2000000000 : ℝ)|=(695606701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (852165723/2500000000 : ℝ)*x 0 + (8927213/10000000000 : ℝ)*x 1 + (2001924553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852165723/2500000000 : ℝ)^71 ≤ (24923469832723/100000000000000 : ℝ)^55 := by
    have hnat : (852165723 : ℕ)^71*100000000000000^55 ≤ 24923469832723^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852165723 2500000000 24923469832723 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8927213/10000000000 : ℝ)^71 ≤ (1447309603/12500000000000 : ℝ)^55 := by
    have hnat : (8927213 : ℕ)^71*12500000000000^55 ≤ 1447309603^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8927213 10000000000 1447309603 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001924553/2500000000 : ℝ)^71 ≤ (4691559480249/6250000000000 : ℝ)^55 := by
    have hnat : (2001924553 : ℕ)^71*6250000000000^55 ≤ 4691559480249^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001924553 2500000000 4691559480249 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852165723/2500000000 : ℝ), (8927213/10000000000 : ℝ), (2001924553/2500000000 : ℝ)] ![(24923469832723/100000000000000 : ℝ), (1447309603/12500000000000 : ℝ), (4691559480249/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852165723/2500000000 : ℝ)|^71 ≤ (24923469832723/100000000000000 : ℝ)^55
        have hw : |(852165723/2500000000 : ℝ)|=(852165723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8927213/10000000000 : ℝ)|^71 ≤ (1447309603/12500000000000 : ℝ)^55
        have hw : |(8927213/10000000000 : ℝ)|=(8927213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2001924553/2500000000 : ℝ)|^71 ≤ (4691559480249/6250000000000 : ℝ)^55
        have hw : |(2001924553/2500000000 : ℝ)|=(2001924553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-91608417/1000000000 : ℝ)*x 0 + (-6008273423/10000000000 : ℝ)*x 1 + (1314757651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91608417/1000000000 : ℝ)^71 ≤ (2285193328951/50000000000000 : ℝ)^55 := by
    have hnat : (91608417 : ℕ)^71*50000000000000^55 ≤ 2285193328951^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91608417 1000000000 2285193328951 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6008273423/10000000000 : ℝ)^71 ≤ (25903351897109/50000000000000 : ℝ)^55 := by
    have hnat : (6008273423 : ℕ)^71*50000000000000^55 ≤ 25903351897109^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008273423 10000000000 25903351897109 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314757651/2500000000 : ℝ)^71 ≤ (43622909530811/100000000000000 : ℝ)^55 := by
    have hnat : (1314757651 : ℕ)^71*100000000000000^55 ≤ 43622909530811^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314757651 2500000000 43622909530811 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91608417/1000000000 : ℝ), (-6008273423/10000000000 : ℝ), (1314757651/2500000000 : ℝ)] ![(2285193328951/50000000000000 : ℝ), (25903351897109/50000000000000 : ℝ), (43622909530811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91608417/1000000000 : ℝ)|^71 ≤ (2285193328951/50000000000000 : ℝ)^55
        have hw : |(-91608417/1000000000 : ℝ)|=(91608417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6008273423/10000000000 : ℝ)|^71 ≤ (25903351897109/50000000000000 : ℝ)^55
        have hw : |(-6008273423/10000000000 : ℝ)|=(6008273423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314757651/2500000000 : ℝ)|^71 ≤ (43622909530811/100000000000000 : ℝ)^55
        have hw : |(1314757651/2500000000 : ℝ)|=(1314757651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6916718017/10000000000 : ℝ)*x 0 + (2909379107/10000000000 : ℝ)*x 1 + (25978379/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6916718017/10000000000 : ℝ)^71 ≤ (31066730500599/50000000000000 : ℝ)^55 := by
    have hnat : (6916718017 : ℕ)^71*50000000000000^55 ≤ 31066730500599^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6916718017 10000000000 31066730500599 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2909379107/10000000000 : ℝ)^71 ≤ (4062982471481/20000000000000 : ℝ)^55 := by
    have hnat : (2909379107 : ℕ)^71*20000000000000^55 ≤ 4062982471481^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909379107 10000000000 4062982471481 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25978379/100000000 : ℝ)^71 ≤ (17551626626749/100000000000000 : ℝ)^55 := by
    have hnat : (25978379 : ℕ)^71*100000000000000^55 ≤ 17551626626749^55*100000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25978379 100000000 17551626626749 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6916718017/10000000000 : ℝ), (2909379107/10000000000 : ℝ), (25978379/100000000 : ℝ)] ![(31066730500599/50000000000000 : ℝ), (4062982471481/20000000000000 : ℝ), (17551626626749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6916718017/10000000000 : ℝ)|^71 ≤ (31066730500599/50000000000000 : ℝ)^55
        have hw : |(6916718017/10000000000 : ℝ)|=(6916718017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2909379107/10000000000 : ℝ)|^71 ≤ (4062982471481/20000000000000 : ℝ)^55
        have hw : |(2909379107/10000000000 : ℝ)|=(2909379107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25978379/100000000 : ℝ)|^71 ≤ (17551626626749/100000000000000 : ℝ)^55
        have hw : |(25978379/100000000 : ℝ)|=(25978379/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2696177561/5000000000 : ℝ)*x 0 + (-894358553/2000000000 : ℝ)*x 1 + (-2825328789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696177561/5000000000 : ℝ)^71 ≤ (22527884613477/50000000000000 : ℝ)^55 := by
    have hnat : (2696177561 : ℕ)^71*50000000000000^55 ≤ 22527884613477^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696177561 5000000000 22527884613477 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894358553/2000000000 : ℝ)^71 ≤ (17691864860959/50000000000000 : ℝ)^55 := by
    have hnat : (894358553 : ℕ)^71*50000000000000^55 ≤ 17691864860959^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894358553 2000000000 17691864860959 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2825328789/10000000000 : ℝ)^71 ≤ (2445062630527/12500000000000 : ℝ)^55 := by
    have hnat : (2825328789 : ℕ)^71*12500000000000^55 ≤ 2445062630527^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825328789 10000000000 2445062630527 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696177561/5000000000 : ℝ), (-894358553/2000000000 : ℝ), (-2825328789/10000000000 : ℝ)] ![(22527884613477/50000000000000 : ℝ), (17691864860959/50000000000000 : ℝ), (2445062630527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696177561/5000000000 : ℝ)|^71 ≤ (22527884613477/50000000000000 : ℝ)^55
        have hw : |(2696177561/5000000000 : ℝ)|=(2696177561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894358553/2000000000 : ℝ)|^71 ≤ (17691864860959/50000000000000 : ℝ)^55
        have hw : |(-894358553/2000000000 : ℝ)|=(894358553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2825328789/10000000000 : ℝ)|^71 ≤ (2445062630527/12500000000000 : ℝ)^55
        have hw : |(-2825328789/10000000000 : ℝ)|=(2825328789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (697249891/2500000000 : ℝ)*x 0 + (-1481/100000000 : ℝ)*x 1 + (8474702631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (697249891/2500000000 : ℝ)^71 ≤ (19236424754253/100000000000000 : ℝ)^55 := by
    have hnat : (697249891 : ℕ)^71*100000000000000^55 ≤ 19236424754253^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697249891 2500000000 19236424754253 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1481/100000000 : ℝ)^71 ≤ (58294237/100000000000000 : ℝ)^55 := by
    have hnat : (1481 : ℕ)^71*100000000000000^55 ≤ 58294237^55*100000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481 100000000 58294237 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8474702631/10000000000 : ℝ)^71 ≤ (20190879235867/25000000000000 : ℝ)^55 := by
    have hnat : (8474702631 : ℕ)^71*25000000000000^55 ≤ 20190879235867^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8474702631 10000000000 20190879235867 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(697249891/2500000000 : ℝ), (-1481/100000000 : ℝ), (8474702631/10000000000 : ℝ)] ![(19236424754253/100000000000000 : ℝ), (58294237/100000000000000 : ℝ), (20190879235867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(697249891/2500000000 : ℝ)|^71 ≤ (19236424754253/100000000000000 : ℝ)^55
        have hw : |(697249891/2500000000 : ℝ)|=(697249891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1481/100000000 : ℝ)|^71 ≤ (58294237/100000000000000 : ℝ)^55
        have hw : |(-1481/100000000 : ℝ)|=(1481/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8474702631/10000000000 : ℝ)|^71 ≤ (20190879235867/25000000000000 : ℝ)^55
        have hw : |(8474702631/10000000000 : ℝ)|=(8474702631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1156003397/10000000000 : ℝ)*x 0 + (-6554857153/10000000000 : ℝ)*x 1 + (1129570873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1156003397/10000000000 : ℝ)^71 ≤ (123422799399/2000000000000 : ℝ)^55 := by
    have hnat : (1156003397 : ℕ)^71*2000000000000^55 ≤ 123422799399^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156003397 10000000000 123422799399 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6554857153/10000000000 : ℝ)^71 ≤ (1159390677431/2000000000000 : ℝ)^55 := by
    have hnat : (6554857153 : ℕ)^71*2000000000000^55 ≤ 1159390677431^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6554857153 10000000000 1159390677431 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129570873/2500000000 : ℝ)^71 ≤ (35859326146131/100000000000000 : ℝ)^55 := by
    have hnat : (1129570873 : ℕ)^71*100000000000000^55 ≤ 35859326146131^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129570873 2500000000 35859326146131 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1156003397/10000000000 : ℝ), (-6554857153/10000000000 : ℝ), (1129570873/2500000000 : ℝ)] ![(123422799399/2000000000000 : ℝ), (1159390677431/2000000000000 : ℝ), (35859326146131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1156003397/10000000000 : ℝ)|^71 ≤ (123422799399/2000000000000 : ℝ)^55
        have hw : |(-1156003397/10000000000 : ℝ)|=(1156003397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6554857153/10000000000 : ℝ)|^71 ≤ (1159390677431/2000000000000 : ℝ)^55
        have hw : |(-6554857153/10000000000 : ℝ)|=(6554857153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129570873/2500000000 : ℝ)|^71 ≤ (35859326146131/100000000000000 : ℝ)^55
        have hw : |(1129570873/2500000000 : ℝ)|=(1129570873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6677858129/10000000000 : ℝ)*x 0 + (1517571859/5000000000 : ℝ)*x 1 + (695294723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6677858129/10000000000 : ℝ)^71 ≤ (742219850193/1250000000000 : ℝ)^55 := by
    have hnat : (6677858129 : ℕ)^71*1250000000000^55 ≤ 742219850193^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6677858129 10000000000 742219850193 1250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517571859/5000000000 : ℝ)^71 ≤ (21455591883181/100000000000000 : ℝ)^55 := by
    have hnat : (1517571859 : ℕ)^71*100000000000000^55 ≤ 21455591883181^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517571859 5000000000 21455591883181 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695294723/2500000000 : ℝ)^71 ≤ (9583410044201/50000000000000 : ℝ)^55 := by
    have hnat : (695294723 : ℕ)^71*50000000000000^55 ≤ 9583410044201^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695294723 2500000000 9583410044201 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6677858129/10000000000 : ℝ), (1517571859/5000000000 : ℝ), (695294723/2500000000 : ℝ)] ![(742219850193/1250000000000 : ℝ), (21455591883181/100000000000000 : ℝ), (9583410044201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6677858129/10000000000 : ℝ)|^71 ≤ (742219850193/1250000000000 : ℝ)^55
        have hw : |(6677858129/10000000000 : ℝ)|=(6677858129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1517571859/5000000000 : ℝ)|^71 ≤ (21455591883181/100000000000000 : ℝ)^55
        have hw : |(1517571859/5000000000 : ℝ)|=(1517571859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(695294723/2500000000 : ℝ)|^71 ≤ (9583410044201/50000000000000 : ℝ)^55
        have hw : |(695294723/2500000000 : ℝ)|=(695294723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (568304667/1250000000 : ℝ)*x 0 + (-1222154843/2500000000 : ℝ)*x 1 + (-13307441/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568304667/1250000000 : ℝ)^71 ≤ (36148031521259/100000000000000 : ℝ)^55 := by
    have hnat : (568304667 : ℕ)^71*100000000000000^55 ≤ 36148031521259^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568304667 1250000000 36148031521259 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222154843/2500000000 : ℝ)^71 ≤ (9924478155921/25000000000000 : ℝ)^55 := by
    have hnat : (1222154843 : ℕ)^71*25000000000000^55 ≤ 9924478155921^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222154843 2500000000 9924478155921 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13307441/40000000 : ℝ)^71 ≤ (12077027915543/50000000000000 : ℝ)^55 := by
    have hnat : (13307441 : ℕ)^71*50000000000000^55 ≤ 12077027915543^55*40000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13307441 40000000 12077027915543 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(568304667/1250000000 : ℝ), (-1222154843/2500000000 : ℝ), (-13307441/40000000 : ℝ)] ![(36148031521259/100000000000000 : ℝ), (9924478155921/25000000000000 : ℝ), (12077027915543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(568304667/1250000000 : ℝ)|^71 ≤ (36148031521259/100000000000000 : ℝ)^55
        have hw : |(568304667/1250000000 : ℝ)|=(568304667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1222154843/2500000000 : ℝ)|^71 ≤ (9924478155921/25000000000000 : ℝ)^55
        have hw : |(-1222154843/2500000000 : ℝ)|=(1222154843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13307441/40000000 : ℝ)|^71 ≤ (12077027915543/50000000000000 : ℝ)^55
        have hw : |(-13307441/40000000 : ℝ)|=(13307441/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310076_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1169846349/2500000000 : ℝ)*x 0 + (4593017/5000000000 : ℝ)*x 1 + (1389138011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1169846349/2500000000 : ℝ)^71 ≤ (37518351115023/100000000000000 : ℝ)^55 := by
    have hnat : (1169846349 : ℕ)^71*100000000000000^55 ≤ 37518351115023^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169846349 2500000000 37518351115023 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4593017/5000000000 : ℝ)^71 ≤ (750852113/6250000000000 : ℝ)^55 := by
    have hnat : (4593017 : ℕ)^71*6250000000000^55 ≤ 750852113^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593017 5000000000 750852113 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389138011/2000000000 : ℝ)^71 ≤ (2498785409873/4000000000000 : ℝ)^55 := by
    have hnat : (1389138011 : ℕ)^71*4000000000000^55 ≤ 2498785409873^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389138011 2000000000 2498785409873 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1169846349/2500000000 : ℝ), (4593017/5000000000 : ℝ), (1389138011/2000000000 : ℝ)] ![(37518351115023/100000000000000 : ℝ), (750852113/6250000000000 : ℝ), (2498785409873/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1169846349/2500000000 : ℝ)|^71 ≤ (37518351115023/100000000000000 : ℝ)^55
        have hw : |(1169846349/2500000000 : ℝ)|=(1169846349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4593017/5000000000 : ℝ)|^71 ≤ (750852113/6250000000000 : ℝ)^55
        have hw : |(4593017/5000000000 : ℝ)|=(4593017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1389138011/2000000000 : ℝ)|^71 ≤ (2498785409873/4000000000000 : ℝ)^55
        have hw : |(1389138011/2000000000 : ℝ)|=(1389138011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310076_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((5211/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5211/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-20727/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-20727/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44589/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44589/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11197/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11197/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-10277/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-10277/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15237/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15237/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s1_pow0 : (5211/6250 : ℝ) ^ (35/8 : ℝ) ≤ (4513927913714569973/10000000000000000000 : ℝ) := by
    have hpowers : (5211/6250 : ℝ)^35 ≤ (4513927913714569973/10000000000000000000 : ℝ)^8 := by
      have hnat : (5211 : ℕ)^35*10000000000000000000^8 ≤ 4513927913714569973^8*6250^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5211 6250 4513927913714569973 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5211/6250 : ℝ)) (X := (4513927913714569973/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (14513927913714569973/10000000000000000000 : ℝ) ≤ (10888784927720177/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (14513927913714569973/10000000000000000000 : ℝ)^8 ≤ (10888784927720177/10000000000000000 : ℝ)^35 := by
      have hnat : (14513927913714569973 : ℕ)^8*10000000000000000^35 ≤ 10888784927720177^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14513927913714569973 10000000000000000000 10888784927720177 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10888784927720177/10000000000000000 : ℝ)) (X := (14513927913714569973/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (9513927913714569973/5000000000000000000 : ℝ) ≤ (11584053047142779/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (9513927913714569973/5000000000000000000 : ℝ)^8 ≤ (11584053047142779/10000000000000000 : ℝ)^35 := by
      have hnat : (9513927913714569973 : ℕ)^8*10000000000000000^35 ≤ 11584053047142779^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9513927913714569973 5000000000000000000 11584053047142779 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11584053047142779/10000000000000000 : ℝ)) (X := (9513927913714569973/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(888784927720177/8337600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12875335544863/154400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (5211/6250 : ℝ)) (alpha := (888784927720177/8337600000000000 : ℝ)) (beta := (12875335544863/154400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5211/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(888784927720177/8337600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12875335544863/154400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (20727/25000 : ℝ) ^ (35/8 : ℝ) ≤ (44041227955806100467/100000000000000000000 : ℝ) := by
    have hpowers : (20727/25000 : ℝ)^35 ≤ (44041227955806100467/100000000000000000000 : ℝ)^8 := by
      have hnat : (20727 : ℕ)^35*100000000000000000000^8 ≤ 44041227955806100467^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20727 25000 44041227955806100467 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20727/25000 : ℝ)) (X := (44041227955806100467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (144041227955806100467/100000000000000000000 : ℝ) ≤ (10869900225661103/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (144041227955806100467/100000000000000000000 : ℝ)^8 ≤ (10869900225661103/10000000000000000 : ℝ)^35 := by
      have hnat : (144041227955806100467 : ℕ)^8*10000000000000000^35 ≤ 10869900225661103^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144041227955806100467 100000000000000000000 10869900225661103 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10869900225661103/10000000000000000 : ℝ)) (X := (144041227955806100467/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (94041227955806100467/50000000000000000000 : ℝ) ≤ (11553356643298513/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (94041227955806100467/50000000000000000000 : ℝ)^8 ≤ (11553356643298513/10000000000000000 : ℝ)^35 := by
      have hnat : (94041227955806100467 : ℕ)^8*10000000000000000^35 ≤ 11553356643298513^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94041227955806100467 50000000000000000000 11553356643298513 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11553356643298513/10000000000000000 : ℝ)) (X := (94041227955806100467/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(124271460808729/1184400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(68345641763741/829080000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (20727/25000 : ℝ)) (alpha := (124271460808729/1184400000000000 : ℝ)) (beta := (68345641763741/829080000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (20727/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(124271460808729/1184400000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(68345641763741/829080000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (44589/50000 : ℝ) ^ (35/8 : ℝ) ≤ (60586736623272648733/100000000000000000000 : ℝ) := by
    have hpowers : (44589/50000 : ℝ)^35 ≤ (60586736623272648733/100000000000000000000 : ℝ)^8 := by
      have hnat : (44589 : ℕ)^35*100000000000000000000^8 ≤ 60586736623272648733^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44589 50000 60586736623272648733 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44589/50000 : ℝ)) (X := (60586736623272648733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (160586736623272648733/100000000000000000000 : ℝ) ≤ (11143441917279917/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (160586736623272648733/100000000000000000000 : ℝ)^8 ≤ (11143441917279917/10000000000000000 : ℝ)^35 := by
      have hnat : (160586736623272648733 : ℕ)^8*10000000000000000^35 ≤ 11143441917279917^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160586736623272648733 100000000000000000000 11143441917279917 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11143441917279917/10000000000000000 : ℝ)) (X := (160586736623272648733/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (110586736623272648733/50000000000000000000 : ℝ) ≤ (11989363373220547/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (110586736623272648733/50000000000000000000 : ℝ)^8 ≤ (11989363373220547/10000000000000000 : ℝ)^35 := by
      have hnat : (110586736623272648733 : ℕ)^8*10000000000000000^35 ≤ 11989363373220547^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110586736623272648733 50000000000000000000 11989363373220547 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11989363373220547/10000000000000000 : ℝ)) (X := (110586736623272648733/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1143441917279917/8917800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(84592145594063/891780000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (44589/50000 : ℝ)) (alpha := (1143441917279917/8917800000000000 : ℝ)) (beta := (84592145594063/891780000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44589/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1143441917279917/8917800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(84592145594063/891780000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1518902071/10000000000 : ℝ)*X 0 0+(-1535285337/2500000000 : ℝ)*X 0 1+(2359599273/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3120296633/5000000000 : ℝ)*X 1 0+(107143279/312500000 : ℝ)*X 1 1+(1463909137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((946099009/2000000000 : ℝ)*X 2 0+(-1139614147/2500000000 : ℝ)*X 2 1+(-3488581617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-271264377/2000000000 : ℝ)*X 0 0+(-209702587/312500000 : ℝ)*X 0 1+(4203010607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((244457327/400000000 : ℝ)*X 1 0+(1681912189/5000000000 : ℝ)*X 1 1+(3153434367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2275360803/5000000000 : ℝ)*X 2 0+(-7596457/16000000 : ℝ)*X 2 1+(-695606701/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((852165723/2500000000 : ℝ)*X 0 0+(8927213/10000000000 : ℝ)*X 0 1+(2001924553/2500000000 : ℝ)*X 0 2+(852165723/2500000000 : ℝ)*X 1 0+(8927213/10000000000 : ℝ)*X 1 1+(2001924553/2500000000 : ℝ)*X 1 2+(852165723/2500000000 : ℝ)*X 2 0+(8927213/10000000000 : ℝ)*X 2 1+(2001924553/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-91608417/1000000000 : ℝ)*X 0 0+(-6008273423/10000000000 : ℝ)*X 0 1+(1314757651/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6916718017/10000000000 : ℝ)*X 1 0+(2909379107/10000000000 : ℝ)*X 1 1+(25978379/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2696177561/5000000000 : ℝ)*X 2 0+(-894358553/2000000000 : ℝ)*X 2 1+(-2825328789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((697249891/2500000000 : ℝ)*X 0 0+(-1481/100000000 : ℝ)*X 0 1+(8474702631/10000000000 : ℝ)*X 0 2+(697249891/2500000000 : ℝ)*X 1 0+(-1481/100000000 : ℝ)*X 1 1+(8474702631/10000000000 : ℝ)*X 1 2+(697249891/2500000000 : ℝ)*X 2 0+(-1481/100000000 : ℝ)*X 2 1+(8474702631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1156003397/10000000000 : ℝ)*X 0 0+(-6554857153/10000000000 : ℝ)*X 0 1+(1129570873/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6677858129/10000000000 : ℝ)*X 1 0+(1517571859/5000000000 : ℝ)*X 1 1+(695294723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((568304667/1250000000 : ℝ)*X 2 0+(-1222154843/2500000000 : ℝ)*X 2 1+(-13307441/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1169846349/2500000000 : ℝ)*X 0 0+(4593017/5000000000 : ℝ)*X 0 1+(1389138011/2000000000 : ℝ)*X 0 2+(1169846349/2500000000 : ℝ)*X 1 0+(4593017/5000000000 : ℝ)*X 1 1+(1389138011/2000000000 : ℝ)*X 1 2+(1169846349/2500000000 : ℝ)*X 2 0+(4593017/5000000000 : ℝ)*X 2 1+(1389138011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310076_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11197/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11197/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22660235944175944926159379513/2265014186400000000000000000000000 : ℝ) := by norm_num
    linear_combination (50088935633/125000000000 : ℝ)*(base7) + (903018218521/1000000000000 : ℝ)*(base40) + (7516700540751/1000000000000 : ℝ)*(major_s1_0) + (7516700540751/1000000000000 : ℝ)*(major_s1_1) + (7516700540751/1000000000000 : ℝ)*(major_s1_2) + (354696793/1000000000000 : ℝ)*(sp_s1_1) + (502146543/1000000000000 : ℝ)*(sp_s1_2) + (5072581119749/500000000000 : ℝ)*(sp_s1_7) + (253630284057/25000000000 : ℝ)*(sp_s1_8) + (5072555537683/500000000000 : ℝ)*(sp_s1_9) + (2523289112131/500000000000 : ℝ)*(sp_s1_13) + (450982411/1000000000000 : ℝ)*(sp_s1_21) + (11790709/250000000000 : ℝ)*(sp_s1_22) + (4131019/500000000000 : ℝ)*(sp_s1_27) + (4645875001237/1000000000000 : ℝ)*(f.failure) + (10145613221909/1000000000000 : ℝ)*(f.sum) + (3093105774681823423/10268846700000000000000000000000 : ℝ)*base63 + (110883622498313/297260000000000000000000000 : ℝ)*base65 + (56602149447133/394800000000000000000000000 : ℝ)*base67 + (403347995130951/2972600000000000000000000000 : ℝ)*base68 + (16482305059398876427/41307249600000000000000000000000 : ℝ)*base71 + (51827560418607/154400000000000000000000000 : ℝ)*base72 + (3445660257337/55272000000000000000000000 : ℝ)*base74 + (2390599167757429/2779200000000000000000000000 : ℝ)*base77 + (5093244649410389/152392800000000000000000000000 : ℝ)*base79 + (37941/100000000000000000 : ℝ)*base87 + (37941/100000000000000000 : ℝ)*base89 + (37941/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-10277/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-10277/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (94873152535855993014942959737/47565297914400000000000000000000000 : ℝ) := by norm_num
    linear_combination (310579/200000000000 : ℝ)*(base13) + (3548809/1000000000000 : ℝ)*(base21) + (275468422511/200000000000 : ℝ)*(base40) + (6866508802513/1000000000000 : ℝ)*(major_s1_0) + (6866508802513/1000000000000 : ℝ)*(major_s1_1) + (6866508802513/1000000000000 : ℝ)*(major_s1_2) + (3932933/125000000000 : ℝ)*(sp_s1_0) + (5470467/125000000000 : ℝ)*(sp_s1_2) + (14056229/500000000000 : ℝ)*(sp_s1_13) + (4744487671691/500000000000 : ℝ)*(sp_s1_14) + (4744477710957/500000000000 : ℝ)*(sp_s1_15) + (2372240261799/250000000000 : ℝ)*(sp_s1_16) + (2121990233979/500000000000 : ℝ)*(sp_s1_20) + (52937827/1000000000000 : ℝ)*(sp_s1_22) + (66312634069/15625000000 : ℝ)*(f.failure) + (474450417987/50000000000 : ℝ)*(f.sum) + (2143372713739068757/30806540100000000000000000000000 : ℝ)*base63 + (233920442141569/891780000000000000000000000 : ℝ)*base64 + (44878537134937/1184400000000000000000000000 : ℝ)*base67 + (813569803278601/8917800000000000000000000000 : ℝ)*base69 + (49560277312976896063/123921748800000000000000000000000 : ℝ)*base71 + (20863201315601/154400000000000000000000000 : ℝ)*base72 + (159687584327827/829080000000000000000000000 : ℝ)*base75 + (3938600018451841/8337600000000000000000000000 : ℝ)*base77 + (48523370804693839/457178400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1691/3125000000000000 : ℝ)*base86 + (1691/3125000000000000 : ℝ)*base88 + (1691/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15237/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15237/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3673524326636621723113349/171147445000000000000000000000 : ℝ) := by norm_num
    linear_combination (736048879/200000000000 : ℝ)*(base7) + (1302846157263/500000000000 : ℝ)*(base40) + (2385194422071/200000000000 : ℝ)*(major_s1_0) + (2385194422071/200000000000 : ℝ)*(major_s1_1) + (2385194422071/200000000000 : ℝ)*(major_s1_2) + (1454343/200000000000 : ℝ)*(sp_s1_0) + (58094231/250000000000 : ℝ)*(sp_s1_1) + (7568253/1000000000000 : ℝ)*(sp_s1_13) + (210799923/500000000000 : ℝ)*(sp_s1_15) + (8670531/125000000000 : ℝ)*(sp_s1_16) + (4119644546401/250000000000 : ℝ)*(sp_s1_21) + (329558629611/20000000000 : ℝ)*(sp_s1_22) + (1029907255817/62500000000 : ℝ)*(sp_s1_23) + (7374802521287/1000000000000 : ℝ)*(sp_s1_27) + (1474225969029/200000000000 : ℝ)*(f.failure) + (16478585457319/1000000000000 : ℝ)*(f.sum) + (307203875569279217/2053769340000000000000000000000 : ℝ)*base62 + (19004461433833/59452000000000000000000000 : ℝ)*base65 + (48084805054931/78960000000000000000000000 : ℝ)*base66 + (706487603351319/594520000000000000000000000 : ℝ)*base68 + (934910167277134441/1652289984000000000000000000000 : ℝ)*base70 + (21484515028263/30880000000000000000000000 : ℝ)*base72 + (262912676474221/276360000000000000000000000 : ℝ)*base74 + (337895568881677/555840000000000000000000000 : ℝ)*base77 + (1313198350098793/6095712000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (8997/20000000000000000 : ℝ)*base87 + (8997/20000000000000000 : ℝ)*base89 + (8997/20000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((5211/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5211/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-20727/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-20727/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44589/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44589/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11197/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11197/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-10277/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-10277/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15237/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15237/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310076_s1 p hpa hpb X hX hprev0

#print axioms solution

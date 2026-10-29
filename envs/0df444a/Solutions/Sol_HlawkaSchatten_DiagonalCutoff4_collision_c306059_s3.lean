-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306059_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:57:33.116862+00:00
-- url     : https://prove2.me/submissions/45c0e5d5-412a-4a9a-af7b-a35fe2d5943d

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
theorem collision_support_c306059_s3_s3_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (162038413/400000000 : ℝ)*x 0 + (1341531317/2500000000 : ℝ)*x 1 + (436462817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162038413/400000000 : ℝ)^135 ≤ (30593858830797/100000000000000 : ℝ)^103 := by
    have hnat : (162038413 : ℕ)^135*100000000000000^103 ≤ 30593858830797^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162038413 400000000 30593858830797 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341531317/2500000000 : ℝ)^135 ≤ (5528177056107/12500000000000 : ℝ)^103 := by
    have hnat : (1341531317 : ℕ)^135*12500000000000^103 ≤ 5528177056107^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341531317 2500000000 5528177056107 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436462817/1250000000 : ℝ)^135 ≤ (25180724704351/100000000000000 : ℝ)^103 := by
    have hnat : (436462817 : ℕ)^135*100000000000000^103 ≤ 25180724704351^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436462817 1250000000 25180724704351 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162038413/400000000 : ℝ), (1341531317/2500000000 : ℝ), (436462817/1250000000 : ℝ)] ![(30593858830797/100000000000000 : ℝ), (5528177056107/12500000000000 : ℝ), (25180724704351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162038413/400000000 : ℝ)|^135 ≤ (30593858830797/100000000000000 : ℝ)^103
        have hw : |(162038413/400000000 : ℝ)|=(162038413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341531317/2500000000 : ℝ)|^135 ≤ (5528177056107/12500000000000 : ℝ)^103
        have hw : |(1341531317/2500000000 : ℝ)|=(1341531317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(436462817/1250000000 : ℝ)|^135 ≤ (25180724704351/100000000000000 : ℝ)^103
        have hw : |(436462817/1250000000 : ℝ)|=(436462817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1418120027/5000000000 : ℝ)*x 0 + (2559154759/10000000000 : ℝ)*x 1 + (889991773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1418120027/5000000000 : ℝ)^135 ≤ (9587191309293/50000000000000 : ℝ)^103 := by
    have hnat : (1418120027 : ℕ)^135*50000000000000^103 ≤ 9587191309293^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418120027 5000000000 9587191309293 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559154759/10000000000 : ℝ)^135 ≤ (8378653295163/50000000000000 : ℝ)^103 := by
    have hnat : (2559154759 : ℕ)^135*50000000000000^103 ≤ 8378653295163^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559154759 10000000000 8378653295163 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889991773/1250000000 : ℝ)^135 ≤ (64068310777069/100000000000000 : ℝ)^103 := by
    have hnat : (889991773 : ℕ)^135*100000000000000^103 ≤ 64068310777069^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889991773 1250000000 64068310777069 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1418120027/5000000000 : ℝ), (2559154759/10000000000 : ℝ), (889991773/1250000000 : ℝ)] ![(9587191309293/50000000000000 : ℝ), (8378653295163/50000000000000 : ℝ), (64068310777069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1418120027/5000000000 : ℝ)|^135 ≤ (9587191309293/50000000000000 : ℝ)^103
        have hw : |(-1418120027/5000000000 : ℝ)|=(1418120027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559154759/10000000000 : ℝ)|^135 ≤ (8378653295163/50000000000000 : ℝ)^103
        have hw : |(2559154759/10000000000 : ℝ)|=(2559154759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(889991773/1250000000 : ℝ)|^135 ≤ (64068310777069/100000000000000 : ℝ)^103
        have hw : |(889991773/1250000000 : ℝ)|=(889991773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (576450267/2000000000 : ℝ)*x 0 + (-2491453051/10000000000 : ℝ)*x 1 + (5707469/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576450267/2000000000 : ℝ)^135 ≤ (783324194897/4000000000000 : ℝ)^103 := by
    have hnat : (576450267 : ℕ)^135*4000000000000^103 ≤ 783324194897^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576450267 2000000000 783324194897 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491453051/10000000000 : ℝ)^135 ≤ (8089335980829/50000000000000 : ℝ)^103 := by
    have hnat : (2491453051 : ℕ)^135*50000000000000^103 ≤ 8089335980829^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491453051 10000000000 8089335980829 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707469/8000000 : ℝ)^135 ≤ (32119111576659/50000000000000 : ℝ)^103 := by
    have hnat : (5707469 : ℕ)^135*50000000000000^103 ≤ 32119111576659^103*8000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707469 8000000 32119111576659 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(576450267/2000000000 : ℝ), (-2491453051/10000000000 : ℝ), (5707469/8000000 : ℝ)] ![(783324194897/4000000000000 : ℝ), (8089335980829/50000000000000 : ℝ), (32119111576659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(576450267/2000000000 : ℝ)|^135 ≤ (783324194897/4000000000000 : ℝ)^103
        have hw : |(576450267/2000000000 : ℝ)|=(576450267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2491453051/10000000000 : ℝ)|^135 ≤ (8089335980829/50000000000000 : ℝ)^103
        have hw : |(-2491453051/10000000000 : ℝ)|=(2491453051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5707469/8000000 : ℝ)|^135 ≤ (32119111576659/50000000000000 : ℝ)^103
        have hw : |(5707469/8000000 : ℝ)|=(5707469/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5414295719/10000000000 : ℝ)*x 0 + (794950467/1250000000 : ℝ)*x 1 + (75937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414295719/10000000000 : ℝ)^135 ≤ (22373240973471/50000000000000 : ℝ)^103 := by
    have hnat : (5414295719 : ℕ)^135*50000000000000^103 ≤ 22373240973471^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414295719 10000000000 22373240973471 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794950467/1250000000 : ℝ)^135 ≤ (1105069970793/2000000000000 : ℝ)^103 := by
    have hnat : (794950467 : ℕ)^135*2000000000000^103 ≤ 1105069970793^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794950467 1250000000 1105069970793 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75937/10000000000 : ℝ)^135 ≤ (19494617/100000000000000 : ℝ)^103 := by
    have hnat : (75937 : ℕ)^135*100000000000000^103 ≤ 19494617^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75937 10000000000 19494617 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414295719/10000000000 : ℝ), (794950467/1250000000 : ℝ), (75937/10000000000 : ℝ)] ![(22373240973471/50000000000000 : ℝ), (1105069970793/2000000000000 : ℝ), (19494617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414295719/10000000000 : ℝ)|^135 ≤ (22373240973471/50000000000000 : ℝ)^103
        have hw : |(5414295719/10000000000 : ℝ)|=(5414295719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(794950467/1250000000 : ℝ)|^135 ≤ (1105069970793/2000000000000 : ℝ)^103
        have hw : |(794950467/1250000000 : ℝ)|=(794950467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75937/10000000000 : ℝ)|^135 ≤ (19494617/100000000000000 : ℝ)^103
        have hw : |(75937/10000000000 : ℝ)|=(75937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3234459137/10000000000 : ℝ)*x 0 + (7063272803/10000000000 : ℝ)*x 1 + (1104707531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3234459137/10000000000 : ℝ)^135 ≤ (4555510345817/20000000000000 : ℝ)^103 := by
    have hnat : (3234459137 : ℕ)^135*20000000000000^103 ≤ 4555510345817^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3234459137 10000000000 4555510345817 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7063272803/10000000000 : ℝ)^135 ≤ (63400869911283/100000000000000 : ℝ)^103 := by
    have hnat : (7063272803 : ℕ)^135*100000000000000^103 ≤ 63400869911283^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7063272803 10000000000 63400869911283 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104707531/5000000000 : ℝ)^135 ≤ (3455394586007/25000000000000 : ℝ)^103 := by
    have hnat : (1104707531 : ℕ)^135*25000000000000^103 ≤ 3455394586007^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104707531 5000000000 3455394586007 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3234459137/10000000000 : ℝ), (7063272803/10000000000 : ℝ), (1104707531/5000000000 : ℝ)] ![(4555510345817/20000000000000 : ℝ), (63400869911283/100000000000000 : ℝ), (3455394586007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3234459137/10000000000 : ℝ)|^135 ≤ (4555510345817/20000000000000 : ℝ)^103
        have hw : |(3234459137/10000000000 : ℝ)|=(3234459137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7063272803/10000000000 : ℝ)|^135 ≤ (63400869911283/100000000000000 : ℝ)^103
        have hw : |(7063272803/10000000000 : ℝ)|=(7063272803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104707531/5000000000 : ℝ)|^135 ≤ (3455394586007/25000000000000 : ℝ)^103
        have hw : |(1104707531/5000000000 : ℝ)|=(1104707531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2643094637/10000000000 : ℝ)*x 0 + (364105171/1250000000 : ℝ)*x 1 + (7000440953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643094637/10000000000 : ℝ)^135 ≤ (3496269578827/20000000000000 : ℝ)^103 := by
    have hnat : (2643094637 : ℕ)^135*20000000000000^103 ≤ 3496269578827^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643094637 10000000000 3496269578827 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364105171/1250000000 : ℝ)^135 ≤ (19855964868451/100000000000000 : ℝ)^103 := by
    have hnat : (364105171 : ℕ)^135*100000000000000^103 ≤ 19855964868451^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364105171 1250000000 19855964868451 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7000440953/10000000000 : ℝ)^135 ≤ (62662687223691/100000000000000 : ℝ)^103 := by
    have hnat : (7000440953 : ℕ)^135*100000000000000^103 ≤ 62662687223691^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7000440953 10000000000 62662687223691 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2643094637/10000000000 : ℝ), (364105171/1250000000 : ℝ), (7000440953/10000000000 : ℝ)] ![(3496269578827/20000000000000 : ℝ), (19855964868451/100000000000000 : ℝ), (62662687223691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2643094637/10000000000 : ℝ)|^135 ≤ (3496269578827/20000000000000 : ℝ)^103
        have hw : |(-2643094637/10000000000 : ℝ)|=(2643094637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364105171/1250000000 : ℝ)|^135 ≤ (19855964868451/100000000000000 : ℝ)^103
        have hw : |(364105171/1250000000 : ℝ)|=(364105171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7000440953/10000000000 : ℝ)|^135 ≤ (62662687223691/100000000000000 : ℝ)^103
        have hw : |(7000440953/10000000000 : ℝ)|=(7000440953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (656428619/2500000000 : ℝ)*x 0 + (-1455544271/5000000000 : ℝ)*x 1 + (280584003/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656428619/2500000000 : ℝ)^135 ≤ (17330836969171/100000000000000 : ℝ)^103 := by
    have hnat : (656428619 : ℕ)^135*100000000000000^103 ≤ 17330836969171^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656428619 2500000000 17330836969171 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1455544271/5000000000 : ℝ)^135 ≤ (9920152846173/50000000000000 : ℝ)^103 := by
    have hnat : (1455544271 : ℕ)^135*50000000000000^103 ≤ 9920152846173^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455544271 5000000000 9920152846173 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280584003/400000000 : ℝ)^135 ≤ (62828857312757/100000000000000 : ℝ)^103 := by
    have hnat : (280584003 : ℕ)^135*100000000000000^103 ≤ 62828857312757^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280584003 400000000 62828857312757 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656428619/2500000000 : ℝ), (-1455544271/5000000000 : ℝ), (280584003/400000000 : ℝ)] ![(17330836969171/100000000000000 : ℝ), (9920152846173/50000000000000 : ℝ), (62828857312757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656428619/2500000000 : ℝ)|^135 ≤ (17330836969171/100000000000000 : ℝ)^103
        have hw : |(656428619/2500000000 : ℝ)|=(656428619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1455544271/5000000000 : ℝ)|^135 ≤ (9920152846173/50000000000000 : ℝ)^103
        have hw : |(-1455544271/5000000000 : ℝ)|=(1455544271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280584003/400000000 : ℝ)|^135 ≤ (62828857312757/100000000000000 : ℝ)^103
        have hw : |(280584003/400000000 : ℝ)|=(280584003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3416554739/5000000000 : ℝ)*x 0 + (4903137821/10000000000 : ℝ)*x 1 + (980343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3416554739/5000000000 : ℝ)^135 ≤ (3794177973167/6250000000000 : ℝ)^103 := by
    have hnat : (3416554739 : ℕ)^135*6250000000000^103 ≤ 3794177973167^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416554739 5000000000 3794177973167 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4903137821/10000000000 : ℝ)^135 ≤ (19646297630899/50000000000000 : ℝ)^103 := by
    have hnat : (4903137821 : ℕ)^135*50000000000000^103 ≤ 19646297630899^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4903137821 10000000000 19646297630899 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980343/10000000000 : ℝ)^135 ≤ (557161299/100000000000000 : ℝ)^103 := by
    have hnat : (980343 : ℕ)^135*100000000000000^103 ≤ 557161299^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980343 10000000000 557161299 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3416554739/5000000000 : ℝ), (4903137821/10000000000 : ℝ), (980343/10000000000 : ℝ)] ![(3794177973167/6250000000000 : ℝ), (19646297630899/50000000000000 : ℝ), (557161299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3416554739/5000000000 : ℝ)|^135 ≤ (3794177973167/6250000000000 : ℝ)^103
        have hw : |(3416554739/5000000000 : ℝ)|=(3416554739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4903137821/10000000000 : ℝ)|^135 ≤ (19646297630899/50000000000000 : ℝ)^103
        have hw : |(4903137821/10000000000 : ℝ)|=(4903137821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(980343/10000000000 : ℝ)|^135 ≤ (557161299/100000000000000 : ℝ)^103
        have hw : |(980343/10000000000 : ℝ)|=(980343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (9283507/16000000 : ℝ)*x 0 + (2307327751/5000000000 : ℝ)*x 1 + (2317584311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9283507/16000000 : ℝ)^135 ≤ (4899423351949/10000000000000 : ℝ)^103 := by
    have hnat : (9283507 : ℕ)^135*10000000000000^103 ≤ 4899423351949^103*16000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9283507 16000000 4899423351949 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307327751/5000000000 : ℝ)^135 ≤ (18145302514531/50000000000000 : ℝ)^103 := by
    have hnat : (2307327751 : ℕ)^135*50000000000000^103 ≤ 18145302514531^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307327751 5000000000 18145302514531 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317584311/10000000000 : ℝ)^135 ≤ (7357580719493/50000000000000 : ℝ)^103 := by
    have hnat : (2317584311 : ℕ)^135*50000000000000^103 ≤ 7357580719493^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317584311 10000000000 7357580719493 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9283507/16000000 : ℝ), (2307327751/5000000000 : ℝ), (2317584311/10000000000 : ℝ)] ![(4899423351949/10000000000000 : ℝ), (18145302514531/50000000000000 : ℝ), (7357580719493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9283507/16000000 : ℝ)|^135 ≤ (4899423351949/10000000000000 : ℝ)^103
        have hw : |(9283507/16000000 : ℝ)|=(9283507/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2307327751/5000000000 : ℝ)|^135 ≤ (18145302514531/50000000000000 : ℝ)^103
        have hw : |(2307327751/5000000000 : ℝ)|=(2307327751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2317584311/10000000000 : ℝ)|^135 ≤ (7357580719493/50000000000000 : ℝ)^103
        have hw : |(2317584311/10000000000 : ℝ)|=(2317584311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-415018497/1250000000 : ℝ)*x 0 + (3322282671/10000000000 : ℝ)*x 1 + (3073126697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415018497/1250000000 : ℝ)^135 ≤ (5892923841289/25000000000000 : ℝ)^103 := by
    have hnat : (415018497 : ℕ)^135*25000000000000^103 ≤ 5892923841289^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415018497 1250000000 5892923841289 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3322282671/10000000000 : ℝ)^135 ≤ (11795780652663/50000000000000 : ℝ)^103 := by
    have hnat : (3322282671 : ℕ)^135*50000000000000^103 ≤ 11795780652663^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3322282671 10000000000 11795780652663 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3073126697/5000000000 : ℝ)^135 ≤ (26418371657719/50000000000000 : ℝ)^103 := by
    have hnat : (3073126697 : ℕ)^135*50000000000000^103 ≤ 26418371657719^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073126697 5000000000 26418371657719 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415018497/1250000000 : ℝ), (3322282671/10000000000 : ℝ), (3073126697/5000000000 : ℝ)] ![(5892923841289/25000000000000 : ℝ), (11795780652663/50000000000000 : ℝ), (26418371657719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415018497/1250000000 : ℝ)|^135 ≤ (5892923841289/25000000000000 : ℝ)^103
        have hw : |(-415018497/1250000000 : ℝ)|=(415018497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3322282671/10000000000 : ℝ)|^135 ≤ (11795780652663/50000000000000 : ℝ)^103
        have hw : |(3322282671/10000000000 : ℝ)|=(3322282671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3073126697/5000000000 : ℝ)|^135 ≤ (26418371657719/50000000000000 : ℝ)^103
        have hw : |(3073126697/5000000000 : ℝ)|=(3073126697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3292740051/10000000000 : ℝ)*x 0 + (-329720363/1000000000 : ℝ)*x 1 + (1237900787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3292740051/10000000000 : ℝ)^135 ≤ (4663396867187/20000000000000 : ℝ)^103 := by
    have hnat : (3292740051 : ℕ)^135*20000000000000^103 ≤ 4663396867187^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3292740051 10000000000 4663396867187 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329720363/1000000000 : ℝ)^135 ≤ (11679210563619/50000000000000 : ℝ)^103 := by
    have hnat : (329720363 : ℕ)^135*50000000000000^103 ≤ 11679210563619^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329720363 1000000000 11679210563619 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237900787/2000000000 : ℝ)^135 ≤ (26662297256831/50000000000000 : ℝ)^103 := by
    have hnat : (1237900787 : ℕ)^135*50000000000000^103 ≤ 26662297256831^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237900787 2000000000 26662297256831 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3292740051/10000000000 : ℝ), (-329720363/1000000000 : ℝ), (1237900787/2000000000 : ℝ)] ![(4663396867187/20000000000000 : ℝ), (11679210563619/50000000000000 : ℝ), (26662297256831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3292740051/10000000000 : ℝ)|^135 ≤ (4663396867187/20000000000000 : ℝ)^103
        have hw : |(3292740051/10000000000 : ℝ)|=(3292740051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329720363/1000000000 : ℝ)|^135 ≤ (11679210563619/50000000000000 : ℝ)^103
        have hw : |(-329720363/1000000000 : ℝ)|=(329720363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1237900787/2000000000 : ℝ)|^135 ≤ (26662297256831/50000000000000 : ℝ)^103
        have hw : |(1237900787/2000000000 : ℝ)|=(1237900787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7211915889/10000000000 : ℝ)*x 0 + (4473438901/10000000000 : ℝ)*x 1 + (-3258609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7211915889/10000000000 : ℝ)^135 ≤ (65155320435487/100000000000000 : ℝ)^103 := by
    have hnat : (7211915889 : ℕ)^135*100000000000000^103 ≤ 65155320435487^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7211915889 10000000000 65155320435487 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473438901/10000000000 : ℝ)^135 ≤ (34841989863341/100000000000000 : ℝ)^103 := by
    have hnat : (4473438901 : ℕ)^135*100000000000000^103 ≤ 34841989863341^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473438901 10000000000 34841989863341 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3258609/10000000000 : ℝ)^135 ≤ (2689691479/100000000000000 : ℝ)^103 := by
    have hnat : (3258609 : ℕ)^135*100000000000000^103 ≤ 2689691479^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3258609 10000000000 2689691479 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7211915889/10000000000 : ℝ), (4473438901/10000000000 : ℝ), (-3258609/10000000000 : ℝ)] ![(65155320435487/100000000000000 : ℝ), (34841989863341/100000000000000 : ℝ), (2689691479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7211915889/10000000000 : ℝ)|^135 ≤ (65155320435487/100000000000000 : ℝ)^103
        have hw : |(7211915889/10000000000 : ℝ)|=(7211915889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473438901/10000000000 : ℝ)|^135 ≤ (34841989863341/100000000000000 : ℝ)^103
        have hw : |(4473438901/10000000000 : ℝ)|=(4473438901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3258609/10000000000 : ℝ)|^135 ≤ (2689691479/100000000000000 : ℝ)^103
        have hw : |(-3258609/10000000000 : ℝ)|=(3258609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s3_s3_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2030177747/10000000000 : ℝ)*x 0 + (3861326329/5000000000 : ℝ)*x 1 + (628200833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030177747/10000000000 : ℝ)^135 ≤ (3092708752627/25000000000000 : ℝ)^103 := by
    have hnat : (2030177747 : ℕ)^135*25000000000000^103 ≤ 3092708752627^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030177747 10000000000 3092708752627 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3861326329/5000000000 : ℝ)^135 ≤ (71268536792149/100000000000000 : ℝ)^103 := by
    have hnat : (3861326329 : ℕ)^135*100000000000000^103 ≤ 71268536792149^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861326329 5000000000 71268536792149 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628200833/2500000000 : ℝ)^135 ≤ (16360628180571/100000000000000 : ℝ)^103 := by
    have hnat : (628200833 : ℕ)^135*100000000000000^103 ≤ 16360628180571^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628200833 2500000000 16360628180571 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030177747/10000000000 : ℝ), (3861326329/5000000000 : ℝ), (628200833/2500000000 : ℝ)] ![(3092708752627/25000000000000 : ℝ), (71268536792149/100000000000000 : ℝ), (16360628180571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030177747/10000000000 : ℝ)|^135 ≤ (3092708752627/25000000000000 : ℝ)^103
        have hw : |(2030177747/10000000000 : ℝ)|=(2030177747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3861326329/5000000000 : ℝ)|^135 ≤ (71268536792149/100000000000000 : ℝ)^103
        have hw : |(3861326329/5000000000 : ℝ)|=(3861326329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628200833/2500000000 : ℝ)|^135 ≤ (16360628180571/100000000000000 : ℝ)^103
        have hw : |(628200833/2500000000 : ℝ)|=(628200833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306059_s3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((40357/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40357/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79827/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79827/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11929/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11929/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4137/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4137/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5879/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5879/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (40357/50000 : ℝ) ^ (67/16 : ℝ) ≤ (509634016519834953/1250000000000000000 : ℝ) := by
    have hpowers : (40357/50000 : ℝ)^67 ≤ (509634016519834953/1250000000000000000 : ℝ)^16 := by
      have hnat : (40357 : ℕ)^67*1250000000000000000^16 ≤ 509634016519834953^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40357 50000 509634016519834953 1250000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40357/50000 : ℝ)) (X := (509634016519834953/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (1759634016519834953/1250000000000000000 : ℝ) ≤ (2712724196448751/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (1759634016519834953/1250000000000000000 : ℝ)^16 ≤ (2712724196448751/2500000000000000 : ℝ)^67 := by
      have hnat : (1759634016519834953 : ℕ)^16*2500000000000000^67 ≤ 2712724196448751^67*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759634016519834953 1250000000000000000 2712724196448751 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2712724196448751/2500000000000000 : ℝ)) (X := (1759634016519834953/1250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (1134634016519834953/625000000000000000 : ℝ) ≤ (5765207823061941/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (1134634016519834953/625000000000000000 : ℝ)^16 ≤ (5765207823061941/5000000000000000 : ℝ)^67 := by
      have hnat : (1134634016519834953 : ℕ)^16*5000000000000000^67 ≤ 5765207823061941^67*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1134634016519834953 625000000000000000 5765207823061941 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5765207823061941/5000000000000000 : ℝ)) (X := (1134634016519834953/625000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(212724196448751/2017850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(339759430164439/4035700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (40357/50000 : ℝ)) (alpha := (212724196448751/2017850000000000 : ℝ)) (beta := (339759430164439/4035700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40357/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(212724196448751/2017850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(339759430164439/4035700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (79827/100000 : ℝ) ^ (67/16 : ℝ) ≤ (2432945269561562071/6250000000000000000 : ℝ) := by
    have hpowers : (79827/100000 : ℝ)^67 ≤ (2432945269561562071/6250000000000000000 : ℝ)^16 := by
      have hnat : (79827 : ℕ)^67*6250000000000000000^16 ≤ 2432945269561562071^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79827 100000 2432945269561562071 6250000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79827/100000 : ℝ)) (X := (2432945269561562071/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (8682945269561562071/6250000000000000000 : ℝ) ≤ (5408395010199569/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (8682945269561562071/6250000000000000000 : ℝ)^16 ≤ (5408395010199569/5000000000000000 : ℝ)^67 := by
      have hnat : (8682945269561562071 : ℕ)^16*5000000000000000^67 ≤ 5408395010199569^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8682945269561562071 6250000000000000000 5408395010199569 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5408395010199569/5000000000000000 : ℝ)) (X := (8682945269561562071/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (5557945269561562071/3125000000000000000 : ℝ) ≤ (5737026273084861/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (5557945269561562071/3125000000000000000 : ℝ)^16 ≤ (5737026273084861/5000000000000000 : ℝ)^67 := by
      have hnat : (5557945269561562071 : ℕ)^16*5000000000000000^67 ≤ 5737026273084861^67*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5557945269561562071 3125000000000000000 5737026273084861 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5737026273084861/5000000000000000 : ℝ)) (X := (5557945269561562071/3125000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(136131670066523/1330450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(82157815721323/997837500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (79827/100000 : ℝ)) (alpha := (136131670066523/1330450000000000 : ℝ)) (beta := (82157815721323/997837500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79827/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(136131670066523/1330450000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(82157815721323/997837500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (11929/20000 : ℝ) ^ (67/16 : ℝ) ≤ (11487256133639995323/100000000000000000000 : ℝ) := by
    have hpowers : (11929/20000 : ℝ)^67 ≤ (11487256133639995323/100000000000000000000 : ℝ)^16 := by
      have hnat : (11929 : ℕ)^67*100000000000000000000^16 ≤ 11487256133639995323^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11929 20000 11487256133639995323 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11929/20000 : ℝ)) (X := (11487256133639995323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (111487256133639995323/100000000000000000000 : ℝ) ≤ (10263078863947851/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (111487256133639995323/100000000000000000000 : ℝ)^16 ≤ (10263078863947851/10000000000000000 : ℝ)^67 := by
      have hnat : (111487256133639995323 : ℕ)^16*10000000000000000^67 ≤ 10263078863947851^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111487256133639995323 100000000000000000000 10263078863947851 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10263078863947851/10000000000000000 : ℝ)) (X := (111487256133639995323/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (61487256133639995323/50000000000000000000 : ℝ) ≤ (10506265806751697/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (61487256133639995323/50000000000000000000 : ℝ)^16 ≤ (10506265806751697/10000000000000000 : ℝ)^67 := by
      have hnat : (61487256133639995323 : ℕ)^16*10000000000000000^67 ≤ 10506265806751697^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61487256133639995323 50000000000000000000 10506265806751697 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10506265806751697/10000000000000000 : ℝ)) (X := (61487256133639995323/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(263078863947851/5964500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(121593471401923/2982250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (11929/20000 : ℝ)) (alpha := (263078863947851/5964500000000000 : ℝ)) (beta := (121593471401923/2982250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (11929/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(263078863947851/5964500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(121593471401923/2982250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_6 : ((162038413/400000000 : ℝ)*X 0 0+(1341531317/2500000000 : ℝ)*X 0 1+(436462817/1250000000 : ℝ)*X 0 2+(162038413/400000000 : ℝ)*X 1 0+(1341531317/2500000000 : ℝ)*X 1 1+(436462817/1250000000 : ℝ)*X 1 2+(162038413/400000000 : ℝ)*X 2 0+(1341531317/2500000000 : ℝ)*X 2 1+(436462817/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1418120027/5000000000 : ℝ)*X 0 0+(2559154759/10000000000 : ℝ)*X 0 1+(889991773/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((576450267/2000000000 : ℝ)*X 1 0+(-2491453051/10000000000 : ℝ)*X 1 1+(5707469/8000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((5414295719/10000000000 : ℝ)*X 2 0+(794950467/1250000000 : ℝ)*X 2 1+(75937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((3234459137/10000000000 : ℝ)*X 0 0+(7063272803/10000000000 : ℝ)*X 0 1+(1104707531/5000000000 : ℝ)*X 0 2+(3234459137/10000000000 : ℝ)*X 1 0+(7063272803/10000000000 : ℝ)*X 1 1+(1104707531/5000000000 : ℝ)*X 1 2+(3234459137/10000000000 : ℝ)*X 2 0+(7063272803/10000000000 : ℝ)*X 2 1+(1104707531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-2643094637/10000000000 : ℝ)*X 0 0+(364105171/1250000000 : ℝ)*X 0 1+(7000440953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((656428619/2500000000 : ℝ)*X 1 0+(-1455544271/5000000000 : ℝ)*X 1 1+(280584003/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((3416554739/5000000000 : ℝ)*X 2 0+(4903137821/10000000000 : ℝ)*X 2 1+(980343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((9283507/16000000 : ℝ)*X 0 0+(2307327751/5000000000 : ℝ)*X 0 1+(2317584311/10000000000 : ℝ)*X 0 2+(9283507/16000000 : ℝ)*X 1 0+(2307327751/5000000000 : ℝ)*X 1 1+(2317584311/10000000000 : ℝ)*X 1 2+(9283507/16000000 : ℝ)*X 2 0+(2307327751/5000000000 : ℝ)*X 2 1+(2317584311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-415018497/1250000000 : ℝ)*X 0 0+(3322282671/10000000000 : ℝ)*X 0 1+(3073126697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3292740051/10000000000 : ℝ)*X 1 0+(-329720363/1000000000 : ℝ)*X 1 1+(1237900787/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((7211915889/10000000000 : ℝ)*X 2 0+(4473438901/10000000000 : ℝ)*X 2 1+(-3258609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((2030177747/10000000000 : ℝ)*X 0 0+(3861326329/5000000000 : ℝ)*X 0 1+(628200833/2500000000 : ℝ)*X 0 2+(2030177747/10000000000 : ℝ)*X 1 0+(3861326329/5000000000 : ℝ)*X 1 1+(628200833/2500000000 : ℝ)*X 1 2+(2030177747/10000000000 : ℝ)*X 2 0+(3861326329/5000000000 : ℝ)*X 2 1+(628200833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((4137/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4137/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (294099534135444993717098775239/32025172344192500000000000000000000 : ℝ) := by norm_num
    linear_combination (429064848197/1000000000000 : ℝ)*(base7) + (4638231/1000000000000 : ℝ)*(base19) + (4574386511/6250000000 : ℝ)*(base60) + (102070044607/25000000000 : ℝ)*(major_s3_0) + (102070044607/25000000000 : ℝ)*(major_s3_1) + (102070044607/25000000000 : ℝ)*(major_s3_2) + (3133731/1000000000000 : ℝ)*(sp_s3_6) + (262580854637/50000000000 : ℝ)*(sp_s3_7) + (2625768226081/500000000000 : ℝ)*(sp_s3_8) + (1312904065521/250000000000 : ℝ)*(sp_s3_9) + (3077017294461/1000000000000 : ℝ)*(sp_s3_13) + (76002347/1000000000000 : ℝ)*(sp_s3_15) + (12979/15625000000 : ℝ)*(sp_s3_16) + (8105051/500000000000 : ℝ)*(sp_s3_27) + (1323985895049/500000000000 : ℝ)*(f.failure) + (262580854637/50000000000 : ℝ)*(f.sum) + (2237334025530328139/7935469025000000000000000000000 : ℝ)*base63 + (600537939366873/596450000000000000000000000 : ℝ)*base65 + (322464191727979/399135000000000000000000000 : ℝ)*base67 + (94313213165603/149112500000000000000000000 : ℝ)*base69 + (16046799334076106721/24070932650000000000000000000000 : ℝ)*base71 + (360313618963933/403570000000000000000000000 : ℝ)*base73 + (108829231603839/133045000000000000000000000 : ℝ)*base75 + (443972403018157/403570000000000000000000000 : ℝ)*base77 + (4741697168726395903/16107891195000000000000000000000 : ℝ)*base79 + (12557/25000000000000000 : ℝ)*base87 + (12557/25000000000000000 : ℝ)*base89 + (12557/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15911/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1493536015878268313851874920951/128100689376770000000000000000000000 : ℝ) := by norm_num
    linear_combination (333180869577/1000000000000 : ℝ)*(base7) + (2330283/500000000000 : ℝ)*(base59) + (939779288043/1000000000000 : ℝ)*(base60) + (4800605796961/1000000000000 : ℝ)*(major_s3_0) + (4800605796961/1000000000000 : ℝ)*(major_s3_1) + (4800605796961/1000000000000 : ℝ)*(major_s3_2) + (3973599/500000000000 : ℝ)*(sp_s3_6) + (10881989/250000000000 : ℝ)*(sp_s3_7) + (10679101/200000000000 : ℝ)*(sp_s3_8) + (1570270673231/250000000000 : ℝ)*(sp_s3_14) + (50248582603/8000000000 : ℝ)*(sp_s3_15) + (628103929097/100000000000 : ℝ)*(sp_s3_16) + (107709029173/31250000000 : ℝ)*(sp_s3_20) + (8692991/100000000000 : ℝ)*(sp_s3_23) + (778379002789/250000000000 : ℝ)*(f.failure) + (78514077761/12500000000 : ℝ)*(f.sum) + (48405390290434228929/158709380500000000000000000000000 : ℝ)*base62 + (1873577145873697/2982250000000000000000000000 : ℝ)*base64 + (320735778645361/498918750000000000000000000 : ℝ)*base66 + (4106066052842061/5964500000000000000000000000 : ℝ)*base68 + (32780565685627367909/120354663250000000000000000000000 : ℝ)*base70 + (2602957083830551/4035700000000000000000000000 : ℝ)*base72 + (1032846020948397/1330450000000000000000000000 : ℝ)*base74 + (1639516607311849/2017850000000000000000000000 : ℝ)*base76 + (87958148156116506259/322157823900000000000000000000000 : ℝ)*base78 + (123/12500000000000000 : ℝ)*base86 + (123/12500000000000000 : ℝ)*base88 + (123/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5879/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5879/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17931258482681927184954917083873/3202517234419250000000000000000000000 : ℝ) := by norm_num
    linear_combination (568329/500000000000 : ℝ)*(base8) + (285611/1000000000000 : ℝ)*(base11) + (157421/250000000000 : ℝ)*(base40) + (1384938567/100000000000 : ℝ)*(base50) + (157686716233/500000000000 : ℝ)*(base60) + (3468553089473/1000000000000 : ℝ)*(major_s3_0) + (3468553089473/1000000000000 : ℝ)*(major_s3_1) + (3468553089473/1000000000000 : ℝ)*(major_s3_2) + (6054049/100000000000 : ℝ)*(sp_s3_13) + (26196551/200000000000 : ℝ)*(sp_s3_16) + (937502545363/200000000000 : ℝ)*(sp_s3_21) + (1171878537271/250000000000 : ℝ)*(sp_s3_22) + (4687383166329/1000000000000 : ℝ)*(sp_s3_23) + (562382405749/250000000000 : ℝ)*(sp_s3_27) + (1124795081743/500000000000 : ℝ)*(f.failure) + (1171878537271/250000000000 : ℝ)*(f.sum) + (56469627623065084697/158709380500000000000000000000000 : ℝ)*base62 + (130429037582351/745562500000000000000000000 : ℝ)*base65 + (453586152133123/1995675000000000000000000000 : ℝ)*base67 + (1536499471339777/5964500000000000000000000000 : ℝ)*base69 + (8551295227455464547/30088665812500000000000000000000 : ℝ)*base71 + (1093252993977207/4035700000000000000000000000 : ℝ)*base73 + (131491484169853/665225000000000000000000000 : ℝ)*base74 + (120924030950453/2017850000000000000000000000 : ℝ)*base77 + (167705084635384157053/322157823900000000000000000000000 : ℝ)*base79 + (11901/25000000000000000 : ℝ)*base86 + (11901/25000000000000000 : ℝ)*base88 + (11901/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((40357/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40357/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79827/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79827/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11929/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11929/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4137/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4137/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5879/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5879/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306059_s3 p hpa hpb X hX hprev2

#print axioms solution

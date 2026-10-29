-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305062_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:15.078195+00:00
-- url     : https://prove2.me/submissions/c5847e5c-e905-48b0-9724-19487f734c54

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
theorem collision_support_c305062_s3_s3_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1532619729/10000000000 : ℝ)*x 0 + (1241040697/2500000000 : ℝ)*x 1 + (-387003/640000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1532619729/10000000000 : ℝ)^67 ≤ (265909862247/3125000000000 : ℝ)^51 := by
    have hnat : (1532619729 : ℕ)^67*3125000000000^51 ≤ 265909862247^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532619729 10000000000 265909862247 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1241040697/2500000000 : ℝ)^67 ≤ (19924854603721/50000000000000 : ℝ)^51 := by
    have hnat : (1241040697 : ℕ)^67*50000000000000^51 ≤ 19924854603721^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241040697 2500000000 19924854603721 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387003/640000 : ℝ)^67 ≤ (51641175193581/100000000000000 : ℝ)^51 := by
    have hnat : (387003 : ℕ)^67*100000000000000^51 ≤ 51641175193581^51*640000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387003 640000 51641175193581 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1532619729/10000000000 : ℝ), (1241040697/2500000000 : ℝ), (-387003/640000 : ℝ)] ![(265909862247/3125000000000 : ℝ), (19924854603721/50000000000000 : ℝ), (51641175193581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1532619729/10000000000 : ℝ)|^67 ≤ (265909862247/3125000000000 : ℝ)^51
        have hw : |(-1532619729/10000000000 : ℝ)|=(1532619729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1241040697/2500000000 : ℝ)|^67 ≤ (19924854603721/50000000000000 : ℝ)^51
        have hw : |(1241040697/2500000000 : ℝ)|=(1241040697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387003/640000 : ℝ)|^67 ≤ (51641175193581/100000000000000 : ℝ)^51
        have hw : |(-387003/640000 : ℝ)|=(387003/640000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (107034543/200000000 : ℝ)*x 0 + (1343423297/2500000000 : ℝ)*x 1 + (196450959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107034543/200000000 : ℝ)^67 ≤ (43986114362903/100000000000000 : ℝ)^51 := by
    have hnat : (107034543 : ℕ)^67*100000000000000^51 ≤ 43986114362903^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107034543 200000000 43986114362903 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343423297/2500000000 : ℝ)^67 ≤ (11055861721571/25000000000000 : ℝ)^51 := by
    have hnat : (1343423297 : ℕ)^67*25000000000000^51 ≤ 11055861721571^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343423297 2500000000 11055861721571 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196450959/1000000000 : ℝ)^67 ≤ (11790438735697/100000000000000 : ℝ)^51 := by
    have hnat : (196450959 : ℕ)^67*100000000000000^51 ≤ 11790438735697^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196450959 1000000000 11790438735697 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107034543/200000000 : ℝ), (1343423297/2500000000 : ℝ), (196450959/1000000000 : ℝ)] ![(43986114362903/100000000000000 : ℝ), (11055861721571/25000000000000 : ℝ), (11790438735697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107034543/200000000 : ℝ)|^67 ≤ (43986114362903/100000000000000 : ℝ)^51
        have hw : |(107034543/200000000 : ℝ)|=(107034543/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343423297/2500000000 : ℝ)|^67 ≤ (11055861721571/25000000000000 : ℝ)^51
        have hw : |(1343423297/2500000000 : ℝ)|=(1343423297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196450959/1000000000 : ℝ)|^67 ≤ (11790438735697/100000000000000 : ℝ)^51
        have hw : |(196450959/1000000000 : ℝ)|=(196450959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-669328431/5000000000 : ℝ)*x 0 + (1949173449/5000000000 : ℝ)*x 1 + (-1777142793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669328431/5000000000 : ℝ)^67 ≤ (7123331517149/100000000000000 : ℝ)^51 := by
    have hnat : (669328431 : ℕ)^67*100000000000000^51 ≤ 7123331517149^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669328431 5000000000 7123331517149 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949173449/5000000000 : ℝ)^67 ≤ (1160350657767/4000000000000 : ℝ)^51 := by
    have hnat : (1949173449 : ℕ)^67*4000000000000^51 ≤ 1160350657767^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949173449 5000000000 1160350657767 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777142793/2500000000 : ℝ)^67 ≤ (31933951014133/50000000000000 : ℝ)^51 := by
    have hnat : (1777142793 : ℕ)^67*50000000000000^51 ≤ 31933951014133^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777142793 2500000000 31933951014133 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-669328431/5000000000 : ℝ), (1949173449/5000000000 : ℝ), (-1777142793/2500000000 : ℝ)] ![(7123331517149/100000000000000 : ℝ), (1160350657767/4000000000000 : ℝ), (31933951014133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-669328431/5000000000 : ℝ)|^67 ≤ (7123331517149/100000000000000 : ℝ)^51
        have hw : |(-669328431/5000000000 : ℝ)|=(669328431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1949173449/5000000000 : ℝ)|^67 ≤ (1160350657767/4000000000000 : ℝ)^51
        have hw : |(1949173449/5000000000 : ℝ)|=(1949173449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777142793/2500000000 : ℝ)|^67 ≤ (31933951014133/50000000000000 : ℝ)^51
        have hw : |(-1777142793/2500000000 : ℝ)|=(1777142793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2098406961/5000000000 : ℝ)*x 0 + (-178693353/2000000000 : ℝ)*x 1 + (-7107142693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098406961/5000000000 : ℝ)^67 ≤ (15980487386701/50000000000000 : ℝ)^51 := by
    have hnat : (2098406961 : ℕ)^67*50000000000000^51 ≤ 15980487386701^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098406961 5000000000 15980487386701 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178693353/2000000000 : ℝ)^67 ≤ (523497935067/12500000000000 : ℝ)^51 := by
    have hnat : (178693353 : ℕ)^67*12500000000000^51 ≤ 523497935067^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178693353 2000000000 523497935067 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7107142693/10000000000 : ℝ)^67 ≤ (31925520867379/50000000000000 : ℝ)^51 := by
    have hnat : (7107142693 : ℕ)^67*50000000000000^51 ≤ 31925520867379^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7107142693 10000000000 31925520867379 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098406961/5000000000 : ℝ), (-178693353/2000000000 : ℝ), (-7107142693/10000000000 : ℝ)] ![(15980487386701/50000000000000 : ℝ), (523497935067/12500000000000 : ℝ), (31925520867379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098406961/5000000000 : ℝ)|^67 ≤ (15980487386701/50000000000000 : ℝ)^51
        have hw : |(2098406961/5000000000 : ℝ)|=(2098406961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178693353/2000000000 : ℝ)|^67 ≤ (523497935067/12500000000000 : ℝ)^51
        have hw : |(-178693353/2000000000 : ℝ)|=(178693353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7107142693/10000000000 : ℝ)|^67 ≤ (31925520867379/50000000000000 : ℝ)^51
        have hw : |(-7107142693/10000000000 : ℝ)|=(7107142693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2195510567/5000000000 : ℝ)*x 0 + (6697415661/10000000000 : ℝ)*x 1 + (662108467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195510567/5000000000 : ℝ)^67 ≤ (33917920837909/100000000000000 : ℝ)^51 := by
    have hnat : (2195510567 : ℕ)^67*100000000000000^51 ≤ 33917920837909^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195510567 5000000000 33917920837909 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6697415661/10000000000 : ℝ)^67 ≤ (59059521101557/100000000000000 : ℝ)^51 := by
    have hnat : (6697415661 : ℕ)^67*100000000000000^51 ≤ 59059521101557^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6697415661 10000000000 59059521101557 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662108467/5000000000 : ℝ)^67 ≤ (3511279020063/50000000000000 : ℝ)^51 := by
    have hnat : (662108467 : ℕ)^67*50000000000000^51 ≤ 3511279020063^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662108467 5000000000 3511279020063 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2195510567/5000000000 : ℝ), (6697415661/10000000000 : ℝ), (662108467/5000000000 : ℝ)] ![(33917920837909/100000000000000 : ℝ), (59059521101557/100000000000000 : ℝ), (3511279020063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2195510567/5000000000 : ℝ)|^67 ≤ (33917920837909/100000000000000 : ℝ)^51
        have hw : |(2195510567/5000000000 : ℝ)|=(2195510567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6697415661/10000000000 : ℝ)|^67 ≤ (59059521101557/100000000000000 : ℝ)^51
        have hw : |(6697415661/10000000000 : ℝ)|=(6697415661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(662108467/5000000000 : ℝ)|^67 ≤ (3511279020063/50000000000000 : ℝ)^51
        have hw : |(662108467/5000000000 : ℝ)|=(662108467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4770511649/10000000000 : ℝ)*x 0 + (1392596381/2000000000 : ℝ)*x 1 + (-18062457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4770511649/10000000000 : ℝ)^67 ≤ (37820093257577/100000000000000 : ℝ)^51 := by
    have hnat : (4770511649 : ℕ)^67*100000000000000^51 ≤ 37820093257577^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770511649 10000000000 37820093257577 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392596381/2000000000 : ℝ)^67 ≤ (62155009117483/100000000000000 : ℝ)^51 := by
    have hnat : (1392596381 : ℕ)^67*100000000000000^51 ≤ 62155009117483^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392596381 2000000000 62155009117483 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18062457/10000000000 : ℝ)^67 ≤ (24897617539/100000000000000 : ℝ)^51 := by
    have hnat : (18062457 : ℕ)^67*100000000000000^51 ≤ 24897617539^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18062457 10000000000 24897617539 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4770511649/10000000000 : ℝ), (1392596381/2000000000 : ℝ), (-18062457/10000000000 : ℝ)] ![(37820093257577/100000000000000 : ℝ), (62155009117483/100000000000000 : ℝ), (24897617539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4770511649/10000000000 : ℝ)|^67 ≤ (37820093257577/100000000000000 : ℝ)^51
        have hw : |(4770511649/10000000000 : ℝ)|=(4770511649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392596381/2000000000 : ℝ)|^67 ≤ (62155009117483/100000000000000 : ℝ)^51
        have hw : |(1392596381/2000000000 : ℝ)|=(1392596381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18062457/10000000000 : ℝ)|^67 ≤ (24897617539/100000000000000 : ℝ)^51
        have hw : |(-18062457/10000000000 : ℝ)|=(18062457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-88217491/1000000000 : ℝ)*x 0 + (2085795413/5000000000 : ℝ)*x 1 + (-891795843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88217491/1000000000 : ℝ)^67 ≤ (2059293923983/50000000000000 : ℝ)^51 := by
    have hnat : (88217491 : ℕ)^67*50000000000000^51 ≤ 2059293923983^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88217491 1000000000 2059293923983 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085795413/5000000000 : ℝ)^67 ≤ (31708862997931/100000000000000 : ℝ)^51 := by
    have hnat : (2085795413 : ℕ)^67*100000000000000^51 ≤ 31708862997931^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085795413 5000000000 31708862997931 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891795843/1250000000 : ℝ)^67 ≤ (64172549135717/100000000000000 : ℝ)^51 := by
    have hnat : (891795843 : ℕ)^67*100000000000000^51 ≤ 64172549135717^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891795843 1250000000 64172549135717 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88217491/1000000000 : ℝ), (2085795413/5000000000 : ℝ), (-891795843/1250000000 : ℝ)] ![(2059293923983/50000000000000 : ℝ), (31708862997931/100000000000000 : ℝ), (64172549135717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88217491/1000000000 : ℝ)|^67 ≤ (2059293923983/50000000000000 : ℝ)^51
        have hw : |(-88217491/1000000000 : ℝ)|=(88217491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085795413/5000000000 : ℝ)|^67 ≤ (31708862997931/100000000000000 : ℝ)^51
        have hw : |(2085795413/5000000000 : ℝ)|=(2085795413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891795843/1250000000 : ℝ)|^67 ≤ (64172549135717/100000000000000 : ℝ)^51
        have hw : |(-891795843/1250000000 : ℝ)|=(891795843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1935241533/5000000000 : ℝ)*x 0 + (-83526857/625000000 : ℝ)*x 1 + (-1783232103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935241533/5000000000 : ℝ)^67 ≤ (2873668041157/10000000000000 : ℝ)^51 := by
    have hnat : (1935241533 : ℕ)^67*10000000000000^51 ≤ 2873668041157^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935241533 5000000000 2873668041157 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83526857/625000000 : ℝ)^67 ≤ (177694158037/2500000000000 : ℝ)^51 := by
    have hnat : (83526857 : ℕ)^67*2500000000000^51 ≤ 177694158037^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83526857 625000000 177694158037 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783232103/2500000000 : ℝ)^67 ≤ (32077776623189/50000000000000 : ℝ)^51 := by
    have hnat : (1783232103 : ℕ)^67*50000000000000^51 ≤ 32077776623189^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783232103 2500000000 32077776623189 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1935241533/5000000000 : ℝ), (-83526857/625000000 : ℝ), (-1783232103/2500000000 : ℝ)] ![(2873668041157/10000000000000 : ℝ), (177694158037/2500000000000 : ℝ), (32077776623189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1935241533/5000000000 : ℝ)|^67 ≤ (2873668041157/10000000000000 : ℝ)^51
        have hw : |(1935241533/5000000000 : ℝ)|=(1935241533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83526857/625000000 : ℝ)|^67 ≤ (177694158037/2500000000000 : ℝ)^51
        have hw : |(-83526857/625000000 : ℝ)|=(83526857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783232103/2500000000 : ℝ)|^67 ≤ (32077776623189/50000000000000 : ℝ)^51
        have hw : |(-1783232103/2500000000 : ℝ)|=(1783232103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1299540673/2000000000 : ℝ)*x 0 + (922120323/2000000000 : ℝ)*x 1 + (666209617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299540673/2000000000 : ℝ)^67 ≤ (56756797546723/100000000000000 : ℝ)^51 := by
    have hnat : (1299540673 : ℕ)^67*100000000000000^51 ≤ 56756797546723^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299540673 2000000000 56756797546723 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922120323/2000000000 : ℝ)^67 ≤ (7232688836489/20000000000000 : ℝ)^51 := by
    have hnat : (922120323 : ℕ)^67*20000000000000^51 ≤ 7232688836489^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922120323 2000000000 7232688836489 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (666209617/5000000000 : ℝ)^67 ≤ (7079758252941/100000000000000 : ℝ)^51 := by
    have hnat : (666209617 : ℕ)^67*100000000000000^51 ≤ 7079758252941^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666209617 5000000000 7079758252941 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299540673/2000000000 : ℝ), (922120323/2000000000 : ℝ), (666209617/5000000000 : ℝ)] ![(56756797546723/100000000000000 : ℝ), (7232688836489/20000000000000 : ℝ), (7079758252941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299540673/2000000000 : ℝ)|^67 ≤ (56756797546723/100000000000000 : ℝ)^51
        have hw : |(1299540673/2000000000 : ℝ)|=(1299540673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922120323/2000000000 : ℝ)|^67 ≤ (7232688836489/20000000000000 : ℝ)^51
        have hw : |(922120323/2000000000 : ℝ)|=(922120323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(666209617/5000000000 : ℝ)|^67 ≤ (7079758252941/100000000000000 : ℝ)^51
        have hw : |(666209617/5000000000 : ℝ)|=(666209617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7368536783/10000000000 : ℝ)*x 0 + (1075378781/2500000000 : ℝ)*x 1 + (-5675613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7368536783/10000000000 : ℝ)^67 ≤ (4184613893437/6250000000000 : ℝ)^51 := by
    have hnat : (7368536783 : ℕ)^67*6250000000000^51 ≤ 4184613893437^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7368536783 10000000000 4184613893437 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075378781/2500000000 : ℝ)^67 ≤ (3301255709533/10000000000000 : ℝ)^51 := by
    have hnat : (1075378781 : ℕ)^67*10000000000000^51 ≤ 3301255709533^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075378781 2500000000 3301255709533 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675613/2500000000 : ℝ)^67 ≤ (16810297637/50000000000000 : ℝ)^51 := by
    have hnat : (5675613 : ℕ)^67*50000000000000^51 ≤ 16810297637^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675613 2500000000 16810297637 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7368536783/10000000000 : ℝ), (1075378781/2500000000 : ℝ), (-5675613/2500000000 : ℝ)] ![(4184613893437/6250000000000 : ℝ), (3301255709533/10000000000000 : ℝ), (16810297637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7368536783/10000000000 : ℝ)|^67 ≤ (4184613893437/6250000000000 : ℝ)^51
        have hw : |(7368536783/10000000000 : ℝ)|=(7368536783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075378781/2500000000 : ℝ)|^67 ≤ (3301255709533/10000000000000 : ℝ)^51
        have hw : |(1075378781/2500000000 : ℝ)|=(1075378781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5675613/2500000000 : ℝ)|^67 ≤ (16810297637/50000000000000 : ℝ)^51
        have hw : |(-5675613/2500000000 : ℝ)|=(5675613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-378969967/10000000000 : ℝ)*x 0 + (375754651/625000000 : ℝ)*x 1 + (-5664342861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378969967/10000000000 : ℝ)^67 ≤ (1357303241047/100000000000000 : ℝ)^51 := by
    have hnat : (378969967 : ℕ)^67*100000000000000^51 ≤ 1357303241047^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378969967 10000000000 1357303241047 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375754651/625000000 : ℝ)^67 ≤ (256252822119/500000000000 : ℝ)^51 := by
    have hnat : (375754651 : ℕ)^67*500000000000^51 ≤ 256252822119^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375754651 625000000 256252822119 500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664342861/10000000000 : ℝ)^67 ≤ (296200827059/625000000000 : ℝ)^51 := by
    have hnat : (5664342861 : ℕ)^67*625000000000^51 ≤ 296200827059^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664342861 10000000000 296200827059 625000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378969967/10000000000 : ℝ), (375754651/625000000 : ℝ), (-5664342861/10000000000 : ℝ)] ![(1357303241047/100000000000000 : ℝ), (256252822119/500000000000 : ℝ), (296200827059/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378969967/10000000000 : ℝ)|^67 ≤ (1357303241047/100000000000000 : ℝ)^51
        have hw : |(-378969967/10000000000 : ℝ)|=(378969967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(375754651/625000000 : ℝ)|^67 ≤ (256252822119/500000000000 : ℝ)^51
        have hw : |(375754651/625000000 : ℝ)|=(375754651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5664342861/10000000000 : ℝ)|^67 ≤ (296200827059/625000000000 : ℝ)^51
        have hw : |(-5664342861/10000000000 : ℝ)|=(5664342861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6267387731/10000000000 : ℝ)*x 0 + (-315994281/5000000000 : ℝ)*x 1 + (-1056011623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6267387731/10000000000 : ℝ)^67 ≤ (54128681154471/100000000000000 : ℝ)^51 := by
    have hnat : (6267387731 : ℕ)^67*100000000000000^51 ≤ 54128681154471^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6267387731 10000000000 54128681154471 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315994281/5000000000 : ℝ)^67 ≤ (53148513899/2000000000000 : ℝ)^51 := by
    have hnat : (315994281 : ℕ)^67*2000000000000^51 ≤ 53148513899^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315994281 5000000000 53148513899 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056011623/2000000000 : ℝ)^67 ≤ (43213893137827/100000000000000 : ℝ)^51 := by
    have hnat : (1056011623 : ℕ)^67*100000000000000^51 ≤ 43213893137827^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056011623 2000000000 43213893137827 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6267387731/10000000000 : ℝ), (-315994281/5000000000 : ℝ), (-1056011623/2000000000 : ℝ)] ![(54128681154471/100000000000000 : ℝ), (53148513899/2000000000000 : ℝ), (43213893137827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6267387731/10000000000 : ℝ)|^67 ≤ (54128681154471/100000000000000 : ℝ)^51
        have hw : |(6267387731/10000000000 : ℝ)|=(6267387731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-315994281/5000000000 : ℝ)|^67 ≤ (53148513899/2000000000000 : ℝ)^51
        have hw : |(-315994281/5000000000 : ℝ)|=(315994281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056011623/2000000000 : ℝ)|^67 ≤ (43213893137827/100000000000000 : ℝ)^51
        have hw : |(-1056011623/2000000000 : ℝ)|=(1056011623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2201538849/5000000000 : ℝ)*x 0 + (3214921609/5000000000 : ℝ)*x 1 + (865216183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201538849/5000000000 : ℝ)^67 ≤ (34040320092131/100000000000000 : ℝ)^51 := by
    have hnat : (2201538849 : ℕ)^67*100000000000000^51 ≤ 34040320092131^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201538849 5000000000 34040320092131 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3214921609/5000000000 : ℝ)^67 ≤ (11195872663859/20000000000000 : ℝ)^51 := by
    have hnat : (3214921609 : ℕ)^67*20000000000000^51 ≤ 11195872663859^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3214921609 5000000000 11195872663859 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865216183/5000000000 : ℝ)^67 ≤ (9980316573899/100000000000000 : ℝ)^51 := by
    have hnat : (865216183 : ℕ)^67*100000000000000^51 ≤ 9980316573899^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865216183 5000000000 9980316573899 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2201538849/5000000000 : ℝ), (3214921609/5000000000 : ℝ), (865216183/5000000000 : ℝ)] ![(34040320092131/100000000000000 : ℝ), (11195872663859/20000000000000 : ℝ), (9980316573899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2201538849/5000000000 : ℝ)|^67 ≤ (34040320092131/100000000000000 : ℝ)^51
        have hw : |(2201538849/5000000000 : ℝ)|=(2201538849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3214921609/5000000000 : ℝ)|^67 ≤ (11195872663859/20000000000000 : ℝ)^51
        have hw : |(3214921609/5000000000 : ℝ)|=(3214921609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(865216183/5000000000 : ℝ)|^67 ≤ (9980316573899/100000000000000 : ℝ)^51
        have hw : |(865216183/5000000000 : ℝ)|=(865216183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s3_s3_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3919837201/5000000000 : ℝ)*x 0 + (3672178183/10000000000 : ℝ)*x 1 + (-190109569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3919837201/5000000000 : ℝ)^67 ≤ (18158360374299/25000000000000 : ℝ)^51 := by
    have hnat : (3919837201 : ℕ)^67*25000000000000^51 ≤ 18158360374299^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3919837201 5000000000 18158360374299 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3672178183/10000000000 : ℝ)^67 ≤ (26818175902673/100000000000000 : ℝ)^51 := by
    have hnat : (3672178183 : ℕ)^67*100000000000000^51 ≤ 26818175902673^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672178183 10000000000 26818175902673 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190109569/10000000000 : ℝ)^67 ≤ (548382587467/100000000000000 : ℝ)^51 := by
    have hnat : (190109569 : ℕ)^67*100000000000000^51 ≤ 548382587467^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190109569 10000000000 548382587467 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3919837201/5000000000 : ℝ), (3672178183/10000000000 : ℝ), (-190109569/10000000000 : ℝ)] ![(18158360374299/25000000000000 : ℝ), (26818175902673/100000000000000 : ℝ), (548382587467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3919837201/5000000000 : ℝ)|^67 ≤ (18158360374299/25000000000000 : ℝ)^51
        have hw : |(3919837201/5000000000 : ℝ)|=(3919837201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3672178183/10000000000 : ℝ)|^67 ≤ (26818175902673/100000000000000 : ℝ)^51
        have hw : |(3672178183/10000000000 : ℝ)|=(3672178183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190109569/10000000000 : ℝ)|^67 ≤ (548382587467/100000000000000 : ℝ)^51
        have hw : |(-190109569/10000000000 : ℝ)|=(190109569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305062_s3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((20091/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20091/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20069/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20069/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31811/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31811/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13143/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13143/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16511/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-46649/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-46649/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (20091/25000 : ℝ) ^ (133/32 : ℝ) ≤ (10077482554693886831/25000000000000000000 : ℝ) := by
    have hpowers : (20091/25000 : ℝ)^133 ≤ (10077482554693886831/25000000000000000000 : ℝ)^32 := by
      have hnat : (20091 : ℕ)^133*25000000000000000000^32 ≤ 10077482554693886831^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20091 25000 10077482554693886831 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20091/25000 : ℝ)) (X := (10077482554693886831/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (35077482554693886831/25000000000000000000 : ℝ) ≤ (433959983118167/400000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (35077482554693886831/25000000000000000000 : ℝ)^32 ≤ (433959983118167/400000000000000 : ℝ)^133 := by
      have hnat : (35077482554693886831 : ℕ)^32*400000000000000^133 ≤ 433959983118167^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35077482554693886831 25000000000000000000 433959983118167 400000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (433959983118167/400000000000000 : ℝ)) (X := (35077482554693886831/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (22577482554693886831/12500000000000000000 : ℝ) ≤ (11528642339180091/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (22577482554693886831/12500000000000000000 : ℝ)^32 ≤ (11528642339180091/10000000000000000 : ℝ)^133 := by
      have hnat : (22577482554693886831 : ℕ)^32*10000000000000000^133 ≤ 11528642339180091^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22577482554693886831 12500000000000000000 11528642339180091 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11528642339180091/10000000000000000 : ℝ)) (X := (22577482554693886831/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(33959983118167/321456000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(169910690306479/2009100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (20091/25000 : ℝ)) (alpha := (33959983118167/321456000000000 : ℝ)) (beta := (169910690306479/2009100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20091/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(33959983118167/321456000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(169910690306479/2009100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (20069/25000 : ℝ) ^ (133/32 : ℝ) ≤ (40126789765337300859/100000000000000000000 : ℝ) := by
    have hpowers : (20069/25000 : ℝ)^133 ≤ (40126789765337300859/100000000000000000000 : ℝ)^32 := by
      have hnat : (20069 : ℕ)^133*100000000000000000000^32 ≤ 40126789765337300859^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20069 25000 40126789765337300859 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20069/25000 : ℝ)) (X := (40126789765337300859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (140126789765337300859/100000000000000000000 : ℝ) ≤ (2169118159146533/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (140126789765337300859/100000000000000000000 : ℝ)^32 ≤ (2169118159146533/2000000000000000 : ℝ)^133 := by
      have hnat : (140126789765337300859 : ℕ)^32*2000000000000000^133 ≤ 2169118159146533^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140126789765337300859 100000000000000000000 2169118159146533 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2169118159146533/2000000000000000 : ℝ)) (X := (140126789765337300859/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (90126789765337300859/50000000000000000000 : ℝ) ≤ (2880753241770911/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (90126789765337300859/50000000000000000000 : ℝ)^32 ≤ (2880753241770911/2500000000000000 : ℝ)^133 := by
      have hnat : (90126789765337300859 : ℕ)^32*2500000000000000^133 ≤ 2880753241770911^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90126789765337300859 50000000000000000000 2880753241770911 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2880753241770911/2500000000000000 : ℝ)) (X := (90126789765337300859/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(169118159146533/1605520000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(677422171350979/8027600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (20069/25000 : ℝ)) (alpha := (169118159146533/1605520000000000 : ℝ)) (beta := (677422171350979/8027600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (20069/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(169118159146533/1605520000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(677422171350979/8027600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (31811/50000 : ℝ) ^ (133/32 : ℝ) ≤ (15266620593293987829/100000000000000000000 : ℝ) := by
    have hpowers : (31811/50000 : ℝ)^133 ≤ (15266620593293987829/100000000000000000000 : ℝ)^32 := by
      have hnat : (31811 : ℕ)^133*100000000000000000000^32 ≤ 15266620593293987829^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31811 50000 15266620593293987829 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31811/50000 : ℝ)) (X := (15266620593293987829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (115266620593293987829/100000000000000000000 : ℝ) ≤ (5173875497838321/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (115266620593293987829/100000000000000000000 : ℝ)^32 ≤ (5173875497838321/5000000000000000 : ℝ)^133 := by
      have hnat : (115266620593293987829 : ℕ)^32*5000000000000000^133 ≤ 5173875497838321^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115266620593293987829 100000000000000000000 5173875497838321 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5173875497838321/5000000000000000 : ℝ)) (X := (115266620593293987829/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (65266620593293987829/50000000000000000000 : ℝ) ≤ (533104907281553/500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (65266620593293987829/50000000000000000000 : ℝ)^32 ≤ (533104907281553/500000000000000 : ℝ)^133 := by
      have hnat : (65266620593293987829 : ℕ)^32*500000000000000^133 ≤ 533104907281553^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65266620593293987829 50000000000000000000 533104907281553 500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (533104907281553/500000000000000 : ℝ)) (X := (65266620593293987829/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(173875497838321/3181100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(157173574977209/3181100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (31811/50000 : ℝ)) (alpha := (173875497838321/3181100000000000 : ℝ)) (beta := (157173574977209/3181100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31811/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(173875497838321/3181100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(157173574977209/3181100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1532619729/10000000000 : ℝ)*X 0 0+(1241040697/2500000000 : ℝ)*X 0 1+(-387003/640000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((107034543/200000000 : ℝ)*X 2 0+(1343423297/2500000000 : ℝ)*X 2 1+(196450959/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-669328431/5000000000 : ℝ)*X 0 0+(1949173449/5000000000 : ℝ)*X 0 1+(-1777142793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2098406961/5000000000 : ℝ)*X 1 0+(-178693353/2000000000 : ℝ)*X 1 1+(-7107142693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2195510567/5000000000 : ℝ)*X 2 0+(6697415661/10000000000 : ℝ)*X 2 1+(662108467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((4770511649/10000000000 : ℝ)*X 0 0+(1392596381/2000000000 : ℝ)*X 0 1+(-18062457/10000000000 : ℝ)*X 0 2+(4770511649/10000000000 : ℝ)*X 1 0+(1392596381/2000000000 : ℝ)*X 1 1+(-18062457/10000000000 : ℝ)*X 1 2+(4770511649/10000000000 : ℝ)*X 2 0+(1392596381/2000000000 : ℝ)*X 2 1+(-18062457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-88217491/1000000000 : ℝ)*X 0 0+(2085795413/5000000000 : ℝ)*X 0 1+(-891795843/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1935241533/5000000000 : ℝ)*X 1 0+(-83526857/625000000 : ℝ)*X 1 1+(-1783232103/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1299540673/2000000000 : ℝ)*X 2 0+(922120323/2000000000 : ℝ)*X 2 1+(666209617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((7368536783/10000000000 : ℝ)*X 0 0+(1075378781/2500000000 : ℝ)*X 0 1+(-5675613/2500000000 : ℝ)*X 0 2+(7368536783/10000000000 : ℝ)*X 1 0+(1075378781/2500000000 : ℝ)*X 1 1+(-5675613/2500000000 : ℝ)*X 1 2+(7368536783/10000000000 : ℝ)*X 2 0+(1075378781/2500000000 : ℝ)*X 2 1+(-5675613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-378969967/10000000000 : ℝ)*X 0 0+(375754651/625000000 : ℝ)*X 0 1+(-5664342861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6267387731/10000000000 : ℝ)*X 1 0+(-315994281/5000000000 : ℝ)*X 1 1+(-1056011623/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2201538849/5000000000 : ℝ)*X 2 0+(3214921609/5000000000 : ℝ)*X 2 1+(865216183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((3919837201/5000000000 : ℝ)*X 0 0+(3672178183/10000000000 : ℝ)*X 0 1+(-190109569/10000000000 : ℝ)*X 0 2+(3919837201/5000000000 : ℝ)*X 1 0+(3672178183/10000000000 : ℝ)*X 1 1+(-190109569/10000000000 : ℝ)*X 1 2+(3919837201/5000000000 : ℝ)*X 2 0+(3672178183/10000000000 : ℝ)*X 2 1+(-190109569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((13143/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13143/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2956381710225279926021751385293/427546498042300000000000000000000000 : ℝ) := by norm_num
    linear_combination (276916203/800000000 : ℝ)*(base7) + (207283/100000000000 : ℝ)*(base12) + (933777/500000000000 : ℝ)*(base53) + (4620970197/50000000000 : ℝ)*(base60) + (719259464529/200000000000 : ℝ)*(major_s3_0) + (719259464529/200000000000 : ℝ)*(major_s3_1) + (3596295455091/1000000000000 : ℝ)*(major_s3_2) + (240027/1000000000000 : ℝ)*(sp_s3_2) + (462526756939/100000000000 : ℝ)*(sp_s3_7) + (4625302263493/1000000000000 : ℝ)*(sp_s3_8) + (4625322755881/1000000000000 : ℝ)*(sp_s3_9) + (1348886514013/500000000000 : ℝ)*(sp_s3_13) + (51486133/1000000000000 : ℝ)*(sp_s3_14) + (18864861/1000000000000 : ℝ)*(sp_s3_15) + (587906943569/250000000000 : ℝ)*(f.failure) + (4625322995907/1000000000000 : ℝ)*(f.sum) + (35890408119315397629/255365983600000000000000000000000 : ℝ)*base62 + (2739862823540139/3181100000000000000000000000 : ℝ)*base65 + (1090183929771581/1605520000000000000000000000 : ℝ)*base66 + (386674373607151/3181100000000000000000000000 : ℝ)*base69 + (28726720057335655807/85215306800000000000000000000000 : ℝ)*base71 + (9176818308419/133940000000000000000000000 : ℝ)*base73 + (389859738527929/1605520000000000000000000000 : ℝ)*base75 + (80441546351053/535760000000000000000000000 : ℝ)*base77 + (67814351897061089/10752167440000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (621/3125000000000000 : ℝ)*base86 + (621/3125000000000000 : ℝ)*base88 + (621/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16511/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (371501319792584035167895359393/61078071148900000000000000000000000 : ℝ) := by norm_num
    linear_combination (585115987/1600000000 : ℝ)*(base7) + (42539/250000000000 : ℝ)*(base39) + (1749095298643/500000000000 : ℝ)*(major_s3_0) + (1749095298643/500000000000 : ℝ)*(major_s3_1) + (1749095298643/500000000000 : ℝ)*(major_s3_2) + (3958053/1000000000000 : ℝ)*(sp_s3_0) + (27929/12500000000 : ℝ)*(sp_s3_2) + (14835207/200000000000 : ℝ)*(sp_s3_8) + (2240536133177/500000000000 : ℝ)*(sp_s3_14) + (44810072253/10000000000 : ℝ)*(sp_s3_15) + (896215833403/200000000000 : ℝ)*(sp_s3_16) + (2653168208371/1000000000000 : ℝ)*(sp_s3_20) + (5176929/1000000000000 : ℝ)*(sp_s3_21) + (4825777/1000000000000 : ℝ)*(sp_s3_27) + (8935451337/3906250000 : ℝ)*(f.failure) + (896216280267/200000000000 : ℝ)*(f.sum) + (6255430395003473441/18240427400000000000000000000000 : ℝ)*base62 + (921483163990549/795275000000000000000000000 : ℝ)*base64 + (582865513772571/573400000000000000000000000 : ℝ)*base67 + (10179995961719/12426171875000000000000000 : ℝ)*base68 + (33683368100057682757/127822960200000000000000000000000 : ℝ)*base70 + (856102062913297/1004550000000000000000000000 : ℝ)*base73 + (92570147836879/114680000000000000000000000 : ℝ)*base74 + (114050810292443/160728000000000000000000000 : ℝ)*base76 + (4264263298451489357/11520179400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (431/1562500000000000 : ℝ)*base86 + (431/1562500000000000 : ℝ)*base88 + (431/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-46649/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-46649/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20864764560076344003505138087/3817379446806250000000000000000000 : ℝ) := by norm_num
    linear_combination (1728053/250000000000 : ℝ)*(base11) + (133389/1000000000000 : ℝ)*(base15) + (21360374241/125000000000 : ℝ)*(base39) + (108613/1000000000000 : ℝ)*(base59) + (828828618331/250000000000 : ℝ)*(major_s3_0) + (828828618331/250000000000 : ℝ)*(major_s3_1) + (828828618331/250000000000 : ℝ)*(major_s3_2) + (6211733/500000000000 : ℝ)*(sp_s3_0) + (9103617/1000000000000 : ℝ)*(sp_s3_2) + (16576019/200000000000 : ℝ)*(sp_s3_9) + (892543079923/200000000000 : ℝ)*(sp_s3_21) + (278920912619/62500000000 : ℝ)*(sp_s3_22) + (223132137579/50000000000 : ℝ)*(sp_s3_23) + (2167892389441/1000000000000 : ℝ)*(sp_s3_27) + (2167892389441/1000000000000 : ℝ)*(f.failure) + (4462734735293/1000000000000 : ℝ)*(f.sum) + (1579497145109974947/9120213700000000000000000000000 : ℝ)*base62 + (1157641930603947/1590550000000000000000000000 : ℝ)*base64 + (12894152849987/286700000000000000000000000 : ℝ)*base67 + (88873675966291/198818750000000000000000000 : ℝ)*base68 + (29855450160656023219/63911480100000000000000000000000 : ℝ)*base70 + (110511035742593/1004550000000000000000000000 : ℝ)*base73 + (7951775940421/57340000000000000000000000 : ℝ)*base75 + (164092841470397/401820000000000000000000000 : ℝ)*base77 + (1270137461407866899/5760089700000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1039/3125000000000000 : ℝ)*base87 + (1039/3125000000000000 : ℝ)*base89 + (1039/3125000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((20091/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20091/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20069/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20069/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31811/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31811/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13143/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13143/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16511/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-46649/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-46649/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305062_s3 p hpa hpb X hX hprev2

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304052_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:02.632517+00:00
-- url     : https://prove2.me/submissions/db257a5a-fbad-4389-9831-b6d40b53fd0a

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
theorem collision_support_c304052_s3_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-155726913/625000000 : ℝ)*x 0 + (3641696781/10000000000 : ℝ)*x 1 + (-1302327363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155726913/625000000 : ℝ)^17 ≤ (16247491596663/100000000000000 : ℝ)^13 := by
    have hnat : (155726913 : ℕ)^17*100000000000000^13 ≤ 16247491596663^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155726913 625000000 16247491596663 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3641696781/10000000000 : ℝ)^17 ≤ (1668016521609/6250000000000 : ℝ)^13 := by
    have hnat : (3641696781 : ℕ)^17*6250000000000^13 ≤ 1668016521609^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641696781 10000000000 1668016521609 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302327363/2000000000 : ℝ)^17 ≤ (28532122019853/50000000000000 : ℝ)^13 := by
    have hnat : (1302327363 : ℕ)^17*50000000000000^13 ≤ 28532122019853^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302327363 2000000000 28532122019853 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-155726913/625000000 : ℝ), (3641696781/10000000000 : ℝ), (-1302327363/2000000000 : ℝ)] ![(16247491596663/100000000000000 : ℝ), (1668016521609/6250000000000 : ℝ), (28532122019853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-155726913/625000000 : ℝ)|^17 ≤ (16247491596663/100000000000000 : ℝ)^13
        have hw : |(-155726913/625000000 : ℝ)|=(155726913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3641696781/10000000000 : ℝ)|^17 ≤ (1668016521609/6250000000000 : ℝ)^13
        have hw : |(3641696781/10000000000 : ℝ)|=(3641696781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302327363/2000000000 : ℝ)|^17 ≤ (28532122019853/50000000000000 : ℝ)^13
        have hw : |(-1302327363/2000000000 : ℝ)|=(1302327363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4616290369/10000000000 : ℝ)*x 0 + (-440630203/1250000000 : ℝ)*x 1 + (-4774678643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4616290369/10000000000 : ℝ)^17 ≤ (3639139413301/10000000000000 : ℝ)^13 := by
    have hnat : (4616290369 : ℕ)^17*10000000000000^13 ≤ 3639139413301^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616290369 10000000000 3639139413301 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440630203/1250000000 : ℝ)^17 ≤ (25575855671623/100000000000000 : ℝ)^13 := by
    have hnat : (440630203 : ℕ)^17*100000000000000^13 ≤ 25575855671623^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440630203 1250000000 25575855671623 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774678643/10000000000 : ℝ)^17 ≤ (38032750171191/100000000000000 : ℝ)^13 := by
    have hnat : (4774678643 : ℕ)^17*100000000000000^13 ≤ 38032750171191^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774678643 10000000000 38032750171191 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4616290369/10000000000 : ℝ), (-440630203/1250000000 : ℝ), (-4774678643/10000000000 : ℝ)] ![(3639139413301/10000000000000 : ℝ), (25575855671623/100000000000000 : ℝ), (38032750171191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4616290369/10000000000 : ℝ)|^17 ≤ (3639139413301/10000000000000 : ℝ)^13
        have hw : |(4616290369/10000000000 : ℝ)|=(4616290369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440630203/1250000000 : ℝ)|^17 ≤ (25575855671623/100000000000000 : ℝ)^13
        have hw : |(-440630203/1250000000 : ℝ)|=(440630203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4774678643/10000000000 : ℝ)|^17 ≤ (38032750171191/100000000000000 : ℝ)^13
        have hw : |(-4774678643/10000000000 : ℝ)|=(4774678643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2421425413/5000000000 : ℝ)*x 0 + (2768619517/5000000000 : ℝ)*x 1 + (588716651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2421425413/5000000000 : ℝ)^17 ≤ (1937220803707/5000000000000 : ℝ)^13 := by
    have hnat : (2421425413 : ℕ)^17*5000000000000^13 ≤ 1937220803707^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421425413 5000000000 1937220803707 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2768619517/5000000000 : ℝ)^17 ≤ (46164335234931/100000000000000 : ℝ)^13 := by
    have hnat : (2768619517 : ℕ)^17*100000000000000^13 ≤ 46164335234931^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768619517 5000000000 46164335234931 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588716651/2500000000 : ℝ)^17 ≤ (7545624338001/50000000000000 : ℝ)^13 := by
    have hnat : (588716651 : ℕ)^17*50000000000000^13 ≤ 7545624338001^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588716651 2500000000 7545624338001 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2421425413/5000000000 : ℝ), (2768619517/5000000000 : ℝ), (588716651/2500000000 : ℝ)] ![(1937220803707/5000000000000 : ℝ), (46164335234931/100000000000000 : ℝ), (7545624338001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2421425413/5000000000 : ℝ)|^17 ≤ (1937220803707/5000000000000 : ℝ)^13
        have hw : |(2421425413/5000000000 : ℝ)|=(2421425413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2768619517/5000000000 : ℝ)|^17 ≤ (46164335234931/100000000000000 : ℝ)^13
        have hw : |(2768619517/5000000000 : ℝ)|=(2768619517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(588716651/2500000000 : ℝ)|^17 ≤ (7545624338001/50000000000000 : ℝ)^13
        have hw : |(588716651/2500000000 : ℝ)|=(588716651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5907231863/10000000000 : ℝ)*x 0 + (873538399/2000000000 : ℝ)*x 1 + (-245206249/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5907231863/10000000000 : ℝ)^17 ≤ (12559739938647/25000000000000 : ℝ)^13 := by
    have hnat : (5907231863 : ℕ)^17*25000000000000^13 ≤ 12559739938647^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5907231863 10000000000 12559739938647 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873538399/2000000000 : ℝ)^17 ≤ (33850127898923/100000000000000 : ℝ)^13 := by
    have hnat : (873538399 : ℕ)^17*100000000000000^13 ≤ 33850127898923^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873538399 2000000000 33850127898923 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245206249/1000000000 : ℝ)^17 ≤ (7955456164127/50000000000000 : ℝ)^13 := by
    have hnat : (245206249 : ℕ)^17*50000000000000^13 ≤ 7955456164127^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245206249 1000000000 7955456164127 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5907231863/10000000000 : ℝ), (873538399/2000000000 : ℝ), (-245206249/1000000000 : ℝ)] ![(12559739938647/25000000000000 : ℝ), (33850127898923/100000000000000 : ℝ), (7955456164127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5907231863/10000000000 : ℝ)|^17 ≤ (12559739938647/25000000000000 : ℝ)^13
        have hw : |(5907231863/10000000000 : ℝ)|=(5907231863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873538399/2000000000 : ℝ)|^17 ≤ (33850127898923/100000000000000 : ℝ)^13
        have hw : |(873538399/2000000000 : ℝ)|=(873538399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245206249/1000000000 : ℝ)|^17 ≤ (7955456164127/50000000000000 : ℝ)^13
        have hw : |(-245206249/1000000000 : ℝ)|=(245206249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-149422299/625000000 : ℝ)*x 0 + (775705731/2500000000 : ℝ)*x 1 + (-7020226991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149422299/625000000 : ℝ)^17 ≤ (962045331051/6250000000000 : ℝ)^13 := by
    have hnat : (149422299 : ℕ)^17*6250000000000^13 ≤ 962045331051^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149422299 625000000 962045331051 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775705731/2500000000 : ℝ)^17 ≤ (21645844150587/100000000000000 : ℝ)^13 := by
    have hnat : (775705731 : ℕ)^17*100000000000000^13 ≤ 21645844150587^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775705731 2500000000 21645844150587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7020226991/10000000000 : ℝ)^17 ≤ (3935089408631/6250000000000 : ℝ)^13 := by
    have hnat : (7020226991 : ℕ)^17*6250000000000^13 ≤ 3935089408631^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7020226991 10000000000 3935089408631 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-149422299/625000000 : ℝ), (775705731/2500000000 : ℝ), (-7020226991/10000000000 : ℝ)] ![(962045331051/6250000000000 : ℝ), (21645844150587/100000000000000 : ℝ), (3935089408631/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-149422299/625000000 : ℝ)|^17 ≤ (962045331051/6250000000000 : ℝ)^13
        have hw : |(-149422299/625000000 : ℝ)|=(149422299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775705731/2500000000 : ℝ)|^17 ≤ (21645844150587/100000000000000 : ℝ)^13
        have hw : |(775705731/2500000000 : ℝ)|=(775705731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7020226991/10000000000 : ℝ)|^17 ≤ (3935089408631/6250000000000 : ℝ)^13
        have hw : |(-7020226991/10000000000 : ℝ)|=(7020226991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (544229257/1250000000 : ℝ)*x 0 + (-2835368397/10000000000 : ℝ)*x 1 + (-1123682219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544229257/1250000000 : ℝ)^17 ≤ (33709749486931/100000000000000 : ℝ)^13 := by
    have hnat : (544229257 : ℕ)^17*100000000000000^13 ≤ 33709749486931^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544229257 1250000000 33709749486931 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2835368397/10000000000 : ℝ)^17 ≤ (9619481214741/50000000000000 : ℝ)^13 := by
    have hnat : (2835368397 : ℕ)^17*50000000000000^13 ≤ 9619481214741^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835368397 10000000000 9619481214741 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123682219/2000000000 : ℝ)^17 ≤ (47051288062471/100000000000000 : ℝ)^13 := by
    have hnat : (1123682219 : ℕ)^17*100000000000000^13 ≤ 47051288062471^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123682219 2000000000 47051288062471 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544229257/1250000000 : ℝ), (-2835368397/10000000000 : ℝ), (-1123682219/2000000000 : ℝ)] ![(33709749486931/100000000000000 : ℝ), (9619481214741/50000000000000 : ℝ), (47051288062471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544229257/1250000000 : ℝ)|^17 ≤ (33709749486931/100000000000000 : ℝ)^13
        have hw : |(544229257/1250000000 : ℝ)|=(544229257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2835368397/10000000000 : ℝ)|^17 ≤ (9619481214741/50000000000000 : ℝ)^13
        have hw : |(-2835368397/10000000000 : ℝ)|=(2835368397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123682219/2000000000 : ℝ)|^17 ≤ (47051288062471/100000000000000 : ℝ)^13
        have hw : |(-1123682219/2000000000 : ℝ)|=(1123682219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1145392287/2500000000 : ℝ)*x 0 + (1588100689/2500000000 : ℝ)*x 1 + (774048809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1145392287/2500000000 : ℝ)^17 ≤ (36033872419181/100000000000000 : ℝ)^13 := by
    have hnat : (1145392287 : ℕ)^17*100000000000000^13 ≤ 36033872419181^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145392287 2500000000 36033872419181 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1588100689/2500000000 : ℝ)^17 ≤ (5524634762643/10000000000000 : ℝ)^13 := by
    have hnat : (1588100689 : ℕ)^17*10000000000000^13 ≤ 5524634762643^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588100689 2500000000 5524634762643 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774048809/5000000000 : ℝ)^17 ≤ (34061640379/390625000000 : ℝ)^13 := by
    have hnat : (774048809 : ℕ)^17*390625000000^13 ≤ 34061640379^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774048809 5000000000 34061640379 390625000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1145392287/2500000000 : ℝ), (1588100689/2500000000 : ℝ), (774048809/5000000000 : ℝ)] ![(36033872419181/100000000000000 : ℝ), (5524634762643/10000000000000 : ℝ), (34061640379/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1145392287/2500000000 : ℝ)|^17 ≤ (36033872419181/100000000000000 : ℝ)^13
        have hw : |(1145392287/2500000000 : ℝ)|=(1145392287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1588100689/2500000000 : ℝ)|^17 ≤ (5524634762643/10000000000000 : ℝ)^13
        have hw : |(1588100689/2500000000 : ℝ)|=(1588100689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(774048809/5000000000 : ℝ)|^17 ≤ (34061640379/390625000000 : ℝ)^13
        have hw : |(774048809/5000000000 : ℝ)|=(774048809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5675842509/10000000000 : ℝ)*x 0 + (667776831/1250000000 : ℝ)*x 1 + (-371630889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5675842509/10000000000 : ℝ)^17 ≤ (23840610213761/50000000000000 : ℝ)^13 := by
    have hnat : (5675842509 : ℕ)^17*50000000000000^13 ≤ 23840610213761^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675842509 10000000000 23840610213761 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667776831/1250000000 : ℝ)^17 ≤ (44049733235503/100000000000000 : ℝ)^13 := by
    have hnat : (667776831 : ℕ)^17*100000000000000^13 ≤ 44049733235503^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667776831 1250000000 44049733235503 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371630889/2500000000 : ℝ)^17 ≤ (2067261581479/25000000000000 : ℝ)^13 := by
    have hnat : (371630889 : ℕ)^17*25000000000000^13 ≤ 2067261581479^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371630889 2500000000 2067261581479 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5675842509/10000000000 : ℝ), (667776831/1250000000 : ℝ), (-371630889/2500000000 : ℝ)] ![(23840610213761/50000000000000 : ℝ), (44049733235503/100000000000000 : ℝ), (2067261581479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5675842509/10000000000 : ℝ)|^17 ≤ (23840610213761/50000000000000 : ℝ)^13
        have hw : |(5675842509/10000000000 : ℝ)|=(5675842509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667776831/1250000000 : ℝ)|^17 ≤ (44049733235503/100000000000000 : ℝ)^13
        have hw : |(667776831/1250000000 : ℝ)|=(667776831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-371630889/2500000000 : ℝ)|^17 ≤ (2067261581479/25000000000000 : ℝ)^13
        have hw : |(-371630889/2500000000 : ℝ)|=(371630889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-881649483/5000000000 : ℝ)*x 0 + (449133241/1250000000 : ℝ)*x 1 + (-1412183367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881649483/5000000000 : ℝ)^17 ≤ (10337755253463/100000000000000 : ℝ)^13 := by
    have hnat : (881649483 : ℕ)^17*100000000000000^13 ≤ 10337755253463^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881649483 5000000000 10337755253463 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449133241/1250000000 : ℝ)^17 ≤ (26223173189483/100000000000000 : ℝ)^13 := by
    have hnat : (449133241 : ℕ)^17*100000000000000^13 ≤ 26223173189483^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449133241 1250000000 26223173189483 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1412183367/2000000000 : ℝ)^17 ≤ (1268781430789/2000000000000 : ℝ)^13 := by
    have hnat : (1412183367 : ℕ)^17*2000000000000^13 ≤ 1268781430789^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412183367 2000000000 1268781430789 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881649483/5000000000 : ℝ), (449133241/1250000000 : ℝ), (-1412183367/2000000000 : ℝ)] ![(10337755253463/100000000000000 : ℝ), (26223173189483/100000000000000 : ℝ), (1268781430789/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881649483/5000000000 : ℝ)|^17 ≤ (10337755253463/100000000000000 : ℝ)^13
        have hw : |(-881649483/5000000000 : ℝ)|=(881649483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449133241/1250000000 : ℝ)|^17 ≤ (26223173189483/100000000000000 : ℝ)^13
        have hw : |(449133241/1250000000 : ℝ)|=(449133241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1412183367/2000000000 : ℝ)|^17 ≤ (1268781430789/2000000000000 : ℝ)^13
        have hw : |(-1412183367/2000000000 : ℝ)|=(1412183367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4136930231/10000000000 : ℝ)*x 0 + (-636671287/2000000000 : ℝ)*x 1 + (-691255399/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4136930231/10000000000 : ℝ)^17 ≤ (15765328723833/50000000000000 : ℝ)^13 := by
    have hnat : (4136930231 : ℕ)^17*50000000000000^13 ≤ 15765328723833^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136930231 10000000000 15765328723833 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636671287/2000000000 : ℝ)^17 ≤ (22383442977083/100000000000000 : ℝ)^13 := by
    have hnat : (636671287 : ℕ)^17*100000000000000^13 ≤ 22383442977083^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636671287 2000000000 22383442977083 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691255399/1250000000 : ℝ)^17 ≤ (36004609031/78125000000 : ℝ)^13 := by
    have hnat : (691255399 : ℕ)^17*78125000000^13 ≤ 36004609031^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691255399 1250000000 36004609031 78125000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4136930231/10000000000 : ℝ), (-636671287/2000000000 : ℝ), (-691255399/1250000000 : ℝ)] ![(15765328723833/50000000000000 : ℝ), (22383442977083/100000000000000 : ℝ), (36004609031/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4136930231/10000000000 : ℝ)|^17 ≤ (15765328723833/50000000000000 : ℝ)^13
        have hw : |(4136930231/10000000000 : ℝ)|=(4136930231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-636671287/2000000000 : ℝ)|^17 ≤ (22383442977083/100000000000000 : ℝ)^13
        have hw : |(-636671287/2000000000 : ℝ)|=(636671287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-691255399/1250000000 : ℝ)|^17 ≤ (36004609031/78125000000 : ℝ)^13
        have hw : |(-691255399/1250000000 : ℝ)|=(691255399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5609208247/10000000000 : ℝ)*x 0 + (2653627807/5000000000 : ℝ)*x 1 + (1636465081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5609208247/10000000000 : ℝ)^17 ≤ (23475265403877/50000000000000 : ℝ)^13 := by
    have hnat : (5609208247 : ℕ)^17*50000000000000^13 ≤ 23475265403877^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609208247 10000000000 23475265403877 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2653627807/5000000000 : ℝ)^17 ≤ (43673160537963/100000000000000 : ℝ)^13 := by
    have hnat : (2653627807 : ℕ)^17*100000000000000^13 ≤ 43673160537963^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653627807 5000000000 43673160537963 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1636465081/10000000000 : ℝ)^17 ≤ (9376308634979/100000000000000 : ℝ)^13 := by
    have hnat : (1636465081 : ℕ)^17*100000000000000^13 ≤ 9376308634979^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636465081 10000000000 9376308634979 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5609208247/10000000000 : ℝ), (2653627807/5000000000 : ℝ), (1636465081/10000000000 : ℝ)] ![(23475265403877/50000000000000 : ℝ), (43673160537963/100000000000000 : ℝ), (9376308634979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5609208247/10000000000 : ℝ)|^17 ≤ (23475265403877/50000000000000 : ℝ)^13
        have hw : |(5609208247/10000000000 : ℝ)|=(5609208247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2653627807/5000000000 : ℝ)|^17 ≤ (43673160537963/100000000000000 : ℝ)^13
        have hw : |(2653627807/5000000000 : ℝ)|=(2653627807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1636465081/10000000000 : ℝ)|^17 ≤ (9376308634979/100000000000000 : ℝ)^13
        have hw : |(1636465081/10000000000 : ℝ)|=(1636465081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6930649659/10000000000 : ℝ)*x 0 + (4024488929/10000000000 : ℝ)*x 1 + (-1403783489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6930649659/10000000000 : ℝ)^17 ≤ (61912923834811/100000000000000 : ℝ)^13 := by
    have hnat : (6930649659 : ℕ)^17*100000000000000^13 ≤ 61912923834811^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6930649659 10000000000 61912923834811 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024488929/10000000000 : ℝ)^17 ≤ (15207340699819/50000000000000 : ℝ)^13 := by
    have hnat : (4024488929 : ℕ)^17*50000000000000^13 ≤ 15207340699819^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024488929 10000000000 15207340699819 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403783489/10000000000 : ℝ)^17 ≤ (3836197373049/50000000000000 : ℝ)^13 := by
    have hnat : (1403783489 : ℕ)^17*50000000000000^13 ≤ 3836197373049^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403783489 10000000000 3836197373049 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6930649659/10000000000 : ℝ), (4024488929/10000000000 : ℝ), (-1403783489/10000000000 : ℝ)] ![(61912923834811/100000000000000 : ℝ), (15207340699819/50000000000000 : ℝ), (3836197373049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6930649659/10000000000 : ℝ)|^17 ≤ (61912923834811/100000000000000 : ℝ)^13
        have hw : |(6930649659/10000000000 : ℝ)|=(6930649659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024488929/10000000000 : ℝ)|^17 ≤ (15207340699819/50000000000000 : ℝ)^13
        have hw : |(4024488929/10000000000 : ℝ)|=(4024488929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1403783489/10000000000 : ℝ)|^17 ≤ (3836197373049/50000000000000 : ℝ)^13
        have hw : |(-1403783489/10000000000 : ℝ)|=(1403783489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-62686843/400000000 : ℝ)*x 0 + (852945001/2000000000 : ℝ)*x 1 + (-6621722431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62686843/400000000 : ℝ)^17 ≤ (4430267213337/50000000000000 : ℝ)^13 := by
    have hnat : (62686843 : ℕ)^17*50000000000000^13 ≤ 4430267213337^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62686843 400000000 4430267213337 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852945001/2000000000 : ℝ)^17 ≤ (3281038679591/10000000000000 : ℝ)^13 := by
    have hnat : (852945001 : ℕ)^17*10000000000000^13 ≤ 3281038679591^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852945001 2000000000 3281038679591 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6621722431/10000000000 : ℝ)^17 ≤ (58329078761121/100000000000000 : ℝ)^13 := by
    have hnat : (6621722431 : ℕ)^17*100000000000000^13 ≤ 58329078761121^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6621722431 10000000000 58329078761121 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62686843/400000000 : ℝ), (852945001/2000000000 : ℝ), (-6621722431/10000000000 : ℝ)] ![(4430267213337/50000000000000 : ℝ), (3281038679591/10000000000000 : ℝ), (58329078761121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62686843/400000000 : ℝ)|^17 ≤ (4430267213337/50000000000000 : ℝ)^13
        have hw : |(-62686843/400000000 : ℝ)|=(62686843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(852945001/2000000000 : ℝ)|^17 ≤ (3281038679591/10000000000000 : ℝ)^13
        have hw : |(852945001/2000000000 : ℝ)|=(852945001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6621722431/10000000000 : ℝ)|^17 ≤ (58329078761121/100000000000000 : ℝ)^13
        have hw : |(-6621722431/10000000000 : ℝ)|=(6621722431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2788800089/5000000000 : ℝ)*x 0 + (-1469586021/5000000000 : ℝ)*x 1 + (-2153183987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2788800089/5000000000 : ℝ)^17 ≤ (2330242895911/5000000000000 : ℝ)^13 := by
    have hnat : (2788800089 : ℕ)^17*5000000000000^13 ≤ 2330242895911^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788800089 5000000000 2330242895911 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1469586021/5000000000 : ℝ)^17 ≤ (20165172124801/100000000000000 : ℝ)^13 := by
    have hnat : (1469586021 : ℕ)^17*100000000000000^13 ≤ 20165172124801^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469586021 5000000000 20165172124801 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153183987/5000000000 : ℝ)^17 ≤ (6645993987909/20000000000000 : ℝ)^13 := by
    have hnat : (2153183987 : ℕ)^17*20000000000000^13 ≤ 6645993987909^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153183987 5000000000 6645993987909 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2788800089/5000000000 : ℝ), (-1469586021/5000000000 : ℝ), (-2153183987/5000000000 : ℝ)] ![(2330242895911/5000000000000 : ℝ), (20165172124801/100000000000000 : ℝ), (6645993987909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2788800089/5000000000 : ℝ)|^17 ≤ (2330242895911/5000000000000 : ℝ)^13
        have hw : |(2788800089/5000000000 : ℝ)|=(2788800089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1469586021/5000000000 : ℝ)|^17 ≤ (20165172124801/100000000000000 : ℝ)^13
        have hw : |(-1469586021/5000000000 : ℝ)|=(1469586021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153183987/5000000000 : ℝ)|^17 ≤ (6645993987909/20000000000000 : ℝ)^13
        have hw : |(-2153183987/5000000000 : ℝ)|=(2153183987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1066086353/2500000000 : ℝ)*x 0 + (2969789849/5000000000 : ℝ)*x 1 + (2532213359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066086353/2500000000 : ℝ)^17 ≤ (32806567897243/100000000000000 : ℝ)^13 := by
    have hnat : (1066086353 : ℕ)^17*100000000000000^13 ≤ 32806567897243^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066086353 2500000000 32806567897243 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2969789849/5000000000 : ℝ)^17 ≤ (10119803584717/20000000000000 : ℝ)^13 := by
    have hnat : (2969789849 : ℕ)^17*20000000000000^13 ≤ 10119803584717^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969789849 5000000000 10119803584717 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532213359/10000000000 : ℝ)^17 ≤ (16594414165081/100000000000000 : ℝ)^13 := by
    have hnat : (2532213359 : ℕ)^17*100000000000000^13 ≤ 16594414165081^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532213359 10000000000 16594414165081 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066086353/2500000000 : ℝ), (2969789849/5000000000 : ℝ), (2532213359/10000000000 : ℝ)] ![(32806567897243/100000000000000 : ℝ), (10119803584717/20000000000000 : ℝ), (16594414165081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066086353/2500000000 : ℝ)|^17 ≤ (32806567897243/100000000000000 : ℝ)^13
        have hw : |(1066086353/2500000000 : ℝ)|=(1066086353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2969789849/5000000000 : ℝ)|^17 ≤ (10119803584717/20000000000000 : ℝ)^13
        have hw : |(2969789849/5000000000 : ℝ)|=(2969789849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532213359/10000000000 : ℝ)|^17 ≤ (16594414165081/100000000000000 : ℝ)^13
        have hw : |(2532213359/10000000000 : ℝ)|=(2532213359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s3_s3_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7134644639/10000000000 : ℝ)*x 0 + (1803966517/5000000000 : ℝ)*x 1 + (-815017369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7134644639/10000000000 : ℝ)^17 ≤ (32153344231303/50000000000000 : ℝ)^13 := by
    have hnat : (7134644639 : ℕ)^17*50000000000000^13 ≤ 32153344231303^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7134644639 10000000000 32153344231303 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1803966517/5000000000 : ℝ)^17 ≤ (13182576758363/50000000000000 : ℝ)^13 := by
    have hnat : (1803966517 : ℕ)^17*50000000000000^13 ≤ 13182576758363^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803966517 5000000000 13182576758363 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (815017369/5000000000 : ℝ)^17 ≤ (9328158002057/100000000000000 : ℝ)^13 := by
    have hnat : (815017369 : ℕ)^17*100000000000000^13 ≤ 9328158002057^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815017369 5000000000 9328158002057 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7134644639/10000000000 : ℝ), (1803966517/5000000000 : ℝ), (-815017369/5000000000 : ℝ)] ![(32153344231303/50000000000000 : ℝ), (13182576758363/50000000000000 : ℝ), (9328158002057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7134644639/10000000000 : ℝ)|^17 ≤ (32153344231303/50000000000000 : ℝ)^13
        have hw : |(7134644639/10000000000 : ℝ)|=(7134644639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1803966517/5000000000 : ℝ)|^17 ≤ (13182576758363/50000000000000 : ℝ)^13
        have hw : |(1803966517/5000000000 : ℝ)|=(1803966517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-815017369/5000000000 : ℝ)|^17 ≤ (9328158002057/100000000000000 : ℝ)^13
        have hw : |(-815017369/5000000000 : ℝ)|=(815017369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304052_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((26961/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26961/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57813/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(57813/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37869/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37869/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8587/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8587/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21281/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s3_pow0 : (26961/50000 : ℝ) ^ (33/8 : ℝ) ≤ (7825907625213116099/100000000000000000000 : ℝ) := by
    have hpowers : (26961/50000 : ℝ)^33 ≤ (7825907625213116099/100000000000000000000 : ℝ)^8 := by
      have hnat : (26961 : ℕ)^33*100000000000000000000^8 ≤ 7825907625213116099^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26961 50000 7825907625213116099 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26961/50000 : ℝ)) (X := (7825907625213116099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (107825907625213116099/100000000000000000000 : ℝ) ≤ (1273042466448449/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (107825907625213116099/100000000000000000000 : ℝ)^8 ≤ (1273042466448449/1250000000000000 : ℝ)^33 := by
      have hnat : (107825907625213116099 : ℕ)^8*1250000000000000^33 ≤ 1273042466448449^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107825907625213116099 100000000000000000000 1273042466448449 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1273042466448449/1250000000000000 : ℝ)) (X := (107825907625213116099/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (57825907625213116099/50000000000000000000 : ℝ) ≤ (2071761133671629/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (57825907625213116099/50000000000000000000 : ℝ)^8 ≤ (2071761133671629/2000000000000000 : ℝ)^33 := by
      have hnat : (57825907625213116099 : ℕ)^8*2000000000000000^33 ≤ 2071761133671629^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57825907625213116099 50000000000000000000 2071761133671629 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2071761133671629/2000000000000000 : ℝ)) (X := (57825907625213116099/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7680822149483/224675000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(58155312256851/1797400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (26961/50000 : ℝ)) (alpha := (7680822149483/224675000000000 : ℝ)) (beta := (58155312256851/1797400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (26961/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7680822149483/224675000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(58155312256851/1797400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (57813/100000 : ℝ) ^ (33/8 : ℝ) ≤ (2607925743796480943/25000000000000000000 : ℝ) := by
    have hpowers : (57813/100000 : ℝ)^33 ≤ (2607925743796480943/25000000000000000000 : ℝ)^8 := by
      have hnat : (57813 : ℕ)^33*25000000000000000000^8 ≤ 2607925743796480943^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57813 100000 2607925743796480943 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57813/100000 : ℝ)) (X := (2607925743796480943/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (27607925743796480943/25000000000000000000 : ℝ) ≤ (2048693408288517/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (27607925743796480943/25000000000000000000 : ℝ)^8 ≤ (2048693408288517/2000000000000000 : ℝ)^33 := by
      have hnat : (27607925743796480943 : ℕ)^8*2000000000000000^33 ≤ 2048693408288517^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27607925743796480943 25000000000000000000 2048693408288517 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2048693408288517/2000000000000000 : ℝ)) (X := (27607925743796480943/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (15107925743796480943/12500000000000000000 : ℝ) ≤ (5235043151127769/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (15107925743796480943/12500000000000000000 : ℝ)^8 ≤ (5235043151127769/5000000000000000 : ℝ)^33 := by
      have hnat : (15107925743796480943 : ℕ)^8*5000000000000000^33 ≤ 5235043151127769^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15107925743796480943 12500000000000000000 5235043151127769 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5235043151127769/5000000000000000 : ℝ)) (X := (15107925743796480943/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(48693408288517/1156260000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(226619260812953/5781300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (57813/100000 : ℝ)) (alpha := (48693408288517/1156260000000000 : ℝ)) (beta := (226619260812953/5781300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (57813/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(48693408288517/1156260000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(226619260812953/5781300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (37869/100000 : ℝ) ^ (33/8 : ℝ) ≤ (1821464986563565293/100000000000000000000 : ℝ) := by
    have hpowers : (37869/100000 : ℝ)^33 ≤ (1821464986563565293/100000000000000000000 : ℝ)^8 := by
      have hnat : (37869 : ℕ)^33*100000000000000000000^8 ≤ 1821464986563565293^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37869 100000 1821464986563565293 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37869/100000 : ℝ)) (X := (1821464986563565293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (101821464986563565293/100000000000000000000 : ℝ) ≤ (5021927639459201/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101821464986563565293/100000000000000000000 : ℝ)^8 ≤ (5021927639459201/5000000000000000 : ℝ)^33 := by
      have hnat : (101821464986563565293 : ℕ)^8*5000000000000000^33 ≤ 5021927639459201^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101821464986563565293 100000000000000000000 5021927639459201 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021927639459201/5000000000000000 : ℝ)) (X := (101821464986563565293/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (51821464986563565293/50000000000000000000 : ℝ) ≤ (2017424038276229/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (51821464986563565293/50000000000000000000 : ℝ)^8 ≤ (2017424038276229/2000000000000000 : ℝ)^33 := by
      have hnat : (51821464986563565293 : ℕ)^8*2000000000000000^33 ≤ 2017424038276229^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51821464986563565293 50000000000000000000 2017424038276229 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2017424038276229/2000000000000000 : ℝ)) (X := (51821464986563565293/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(7309213153067/631150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14421637487581/1262300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (37869/100000 : ℝ)) (alpha := (7309213153067/631150000000000 : ℝ)) (beta := (14421637487581/1262300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37869/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(7309213153067/631150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14421637487581/1262300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-155726913/625000000 : ℝ)*X 0 0+(3641696781/10000000000 : ℝ)*X 0 1+(-1302327363/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4616290369/10000000000 : ℝ)*X 1 0+(-440630203/1250000000 : ℝ)*X 1 1+(-4774678643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2421425413/5000000000 : ℝ)*X 2 0+(2768619517/5000000000 : ℝ)*X 2 1+(588716651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5907231863/10000000000 : ℝ)*X 0 0+(873538399/2000000000 : ℝ)*X 0 1+(-245206249/1000000000 : ℝ)*X 0 2+(5907231863/10000000000 : ℝ)*X 1 0+(873538399/2000000000 : ℝ)*X 1 1+(-245206249/1000000000 : ℝ)*X 1 2+(5907231863/10000000000 : ℝ)*X 2 0+(873538399/2000000000 : ℝ)*X 2 1+(-245206249/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-149422299/625000000 : ℝ)*X 0 0+(775705731/2500000000 : ℝ)*X 0 1+(-7020226991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((544229257/1250000000 : ℝ)*X 1 0+(-2835368397/10000000000 : ℝ)*X 1 1+(-1123682219/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1145392287/2500000000 : ℝ)*X 2 0+(1588100689/2500000000 : ℝ)*X 2 1+(774048809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5675842509/10000000000 : ℝ)*X 0 0+(667776831/1250000000 : ℝ)*X 0 1+(-371630889/2500000000 : ℝ)*X 0 2+(5675842509/10000000000 : ℝ)*X 1 0+(667776831/1250000000 : ℝ)*X 1 1+(-371630889/2500000000 : ℝ)*X 1 2+(5675842509/10000000000 : ℝ)*X 2 0+(667776831/1250000000 : ℝ)*X 2 1+(-371630889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-881649483/5000000000 : ℝ)*X 0 0+(449133241/1250000000 : ℝ)*X 0 1+(-1412183367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4136930231/10000000000 : ℝ)*X 1 0+(-636671287/2000000000 : ℝ)*X 1 1+(-691255399/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5609208247/10000000000 : ℝ)*X 2 0+(2653627807/5000000000 : ℝ)*X 2 1+(1636465081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((6930649659/10000000000 : ℝ)*X 0 0+(4024488929/10000000000 : ℝ)*X 0 1+(-1403783489/10000000000 : ℝ)*X 0 2+(6930649659/10000000000 : ℝ)*X 1 0+(4024488929/10000000000 : ℝ)*X 1 1+(-1403783489/10000000000 : ℝ)*X 1 2+(6930649659/10000000000 : ℝ)*X 2 0+(4024488929/10000000000 : ℝ)*X 2 1+(-1403783489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-62686843/400000000 : ℝ)*X 0 0+(852945001/2000000000 : ℝ)*X 0 1+(-6621722431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((2788800089/5000000000 : ℝ)*X 1 0+(-1469586021/5000000000 : ℝ)*X 1 1+(-2153183987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((1066086353/2500000000 : ℝ)*X 2 0+(2969789849/5000000000 : ℝ)*X 2 1+(2532213359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((7134644639/10000000000 : ℝ)*X 0 0+(1803966517/5000000000 : ℝ)*X 0 1+(-815017369/5000000000 : ℝ)*X 0 2+(7134644639/10000000000 : ℝ)*X 1 0+(1803966517/5000000000 : ℝ)*X 1 1+(-815017369/5000000000 : ℝ)*X 1 2+(7134644639/10000000000 : ℝ)*X 2 0+(1803966517/5000000000 : ℝ)*X 2 1+(-815017369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((15809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1846549304882973551096013/183779956250000000000000000000 : ℝ) := by norm_num
    linear_combination (685874826429/1000000000000 : ℝ)*(base39) + (212977/200000000000 : ℝ)*(base50) + (1298629474063/1000000000000 : ℝ)*(base59) + (5893112947631/1000000000000 : ℝ)*(major_s3_0) + (5893112947631/1000000000000 : ℝ)*(major_s3_1) + (5893112947631/1000000000000 : ℝ)*(major_s3_2) + (23396793/1000000000000 : ℝ)*(sp_s3_1) + (688789/50000000000 : ℝ)*(sp_s3_6) + (1580158040037/200000000000 : ℝ)*(sp_s3_7) + (3950285285277/500000000000 : ℝ)*(sp_s3_8) + (7900715409463/1000000000000 : ℝ)*(sp_s3_9) + (971354642523/250000000000 : ℝ)*(sp_s3_13) + (98116419/500000000000 : ℝ)*(sp_s3_15) + (37395361/500000000000 : ℝ)*(sp_s3_23) + (242839521617/62500000000 : ℝ)*(f.failure) + (1580158040037/200000000000 : ℝ)*(f.sum) + (133555126109925343/801948900000000000000000000000 : ℝ)*base62 + (37069819949807/97100000000000000000000000 : ℝ)*base64 + (113405453132719/825900000000000000000000000 : ℝ)*base66 + (576749746889/12137500000000000000000000 : ℝ)*base68 + (291083670438681/1068100000000000000000000000 : ℝ)*base70 + (400347273033/2200000000000000000000000 : ℝ)*base73 + (39539800534747/165180000000000000000000000 : ℝ)*base74 + (13511578981/275000000000000000000000 : ℝ)*base76 + (2333307069399391/18169800000000000000000000000 : ℝ)*base78 + (63/3125000000000000 : ℝ)*base86 + (63/3125000000000000 : ℝ)*base88 + (63/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8587/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8587/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (444071290000871703573589113/92048764007200000000000000000000 : ℝ) := by norm_num
    linear_combination (400612450983/500000000000 : ℝ)*(base39) + (84811/50000000000 : ℝ)*(base49) + (1104005262313/1000000000000 : ℝ)*(base59) + (5993276728581/1000000000000 : ℝ)*(major_s3_0) + (5993276728581/1000000000000 : ℝ)*(major_s3_1) + (5993276728581/1000000000000 : ℝ)*(major_s3_2) + (2024909/1000000000000 : ℝ)*(sp_s3_0) + (606527/50000000000 : ℝ)*(sp_s3_6) + (21794921/1000000000000 : ℝ)*(sp_s3_7) + (1607011190451/200000000000 : ℝ)*(sp_s3_14) + (2008769943021/250000000000 : ℝ)*(sp_s3_15) + (2008769943021/250000000000 : ℝ)*(sp_s3_16) + (1975692622083/500000000000 : ℝ)*(sp_s3_20) + (74702263/1000000000000 : ℝ)*(sp_s3_27) + (3951472076969/1000000000000 : ℝ)*(f.failure) + (2008769943021/250000000000 : ℝ)*(f.sum) + (13622797244874703569/24325783300000000000000000000000 : ℝ)*base63 + (138640247606769/1262300000000000000000000000 : ℝ)*base65 + (1601702240845459/1927100000000000000000000000 : ℝ)*base67 + (78345018861151/315575000000000000000000000 : ℝ)*base69 + (6077178482308833649/11344290100000000000000000000000 : ℝ)*base71 + (810050534199471/1797400000000000000000000000 : ℝ)*base73 + (98303568700761/385420000000000000000000000 : ℝ)*base75 + (15107294287163/224675000000000000000000000 : ℝ)*base77 + (16109026960487920367/34637695400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (7229/12500000000000000 : ℝ)*base86 + (7229/12500000000000000 : ℝ)*base88 + (7229/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21281/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40370419424293402711568750959/4372316290342000000000000000000000 : ℝ) := by norm_num
    linear_combination (1156173310507/1000000000000 : ℝ)*(base39) + (1473283/500000000000 : ℝ)*(base40) + (866097581149/1000000000000 : ℝ)*(base59) + (242016998299/50000000000 : ℝ)*(major_s3_0) + (242016998299/50000000000 : ℝ)*(major_s3_1) + (242016998299/50000000000 : ℝ)*(major_s3_2) + (31615071/1000000000000 : ℝ)*(sp_s3_0) + (8139589/200000000000 : ℝ)*(sp_s3_2) + (32145809/1000000000000 : ℝ)*(sp_s3_9) + (59121603/500000000000 : ℝ)*(sp_s3_20) + (6489324516817/1000000000000 : ℝ)*(sp_s3_21) + (405584758243/62500000000 : ℝ)*(sp_s3_22) + (3244641644067/500000000000 : ℝ)*(sp_s3_23) + (319120247913/100000000000 : ℝ)*(sp_s3_27) + (638264144467/200000000000 : ℝ)*(f.failure) + (405584758243/62500000000 : ℝ)*(f.sum) + (3617920895480414713/7297734990000000000000000000000 : ℝ)*base62 + (36163957670257/31557500000000000000000000 : ℝ)*base64 + (100353107080391/144532500000000000000000000 : ℝ)*base67 + (33191625043773/31557500000000000000000000 : ℝ)*base68 + (148663380862122169/283607252500000000000000000000 : ℝ)*base70 + (51226101588831/89870000000000000000000000 : ℝ)*base73 + (75060442346089/72266250000000000000000000 : ℝ)*base74 + (17039190374721/22467500000000000000000000 : ℝ)*base76 + (8504343967966867/1039130862000000000000000000000 : ℝ)*base78 + (147/2500000000000000 : ℝ)*base86 + (147/2500000000000000 : ℝ)*base88 + (147/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((26961/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26961/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57813/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(57813/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37869/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37869/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8587/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8587/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21281/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304052_s3 p hpa hpb X hX hprev2

#print axioms solution

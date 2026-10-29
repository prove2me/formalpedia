-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c325061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:04:41.111996+00:00
-- url     : https://prove2.me/submissions/3b89ca6a-c1b3-44d1-91b8-d19872601200

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
theorem collision_support_c325061_s1_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-877413647/5000000000 : ℝ)*x 0 + (34458877/78125000 : ℝ)*x 1 + (363462939/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (877413647/5000000000 : ℝ)^87 ≤ (5927765379739/50000000000000 : ℝ)^71 := by
    have hnat : (877413647 : ℕ)^87*50000000000000^71 ≤ 5927765379739^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877413647 5000000000 5927765379739 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34458877/78125000 : ℝ)^87 ≤ (36677600224369/100000000000000 : ℝ)^71 := by
    have hnat : (34458877 : ℕ)^87*100000000000000^71 ≤ 36677600224369^71*78125000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34458877 78125000 36677600224369 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363462939/625000000 : ℝ)^87 ≤ (51466868995223/100000000000000 : ℝ)^71 := by
    have hnat : (363462939 : ℕ)^87*100000000000000^71 ≤ 51466868995223^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363462939 625000000 51466868995223 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-877413647/5000000000 : ℝ), (34458877/78125000 : ℝ), (363462939/625000000 : ℝ)] ![(5927765379739/50000000000000 : ℝ), (36677600224369/100000000000000 : ℝ), (51466868995223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-877413647/5000000000 : ℝ)|^87 ≤ (5927765379739/50000000000000 : ℝ)^71
        have hw : |(-877413647/5000000000 : ℝ)|=(877413647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34458877/78125000 : ℝ)|^87 ≤ (36677600224369/100000000000000 : ℝ)^71
        have hw : |(34458877/78125000 : ℝ)|=(34458877/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(363462939/625000000 : ℝ)|^87 ≤ (51466868995223/100000000000000 : ℝ)^71
        have hw : |(363462939/625000000 : ℝ)|=(363462939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2314214207/5000000000 : ℝ)*x 0 + (-109450391/625000000 : ℝ)*x 1 + (5611692667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2314214207/5000000000 : ℝ)^87 ≤ (38907945150177/100000000000000 : ℝ)^71 := by
    have hnat : (2314214207 : ℕ)^87*100000000000000^71 ≤ 38907945150177^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314214207 5000000000 38907945150177 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109450391/625000000 : ℝ)^87 ≤ (11825561254707/100000000000000 : ℝ)^71 := by
    have hnat : (109450391 : ℕ)^87*100000000000000^71 ≤ 11825561254707^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109450391 625000000 11825561254707 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5611692667/10000000000 : ℝ)^87 ≤ (49266493582661/100000000000000 : ℝ)^71 := by
    have hnat : (5611692667 : ℕ)^87*100000000000000^71 ≤ 49266493582661^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5611692667 10000000000 49266493582661 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2314214207/5000000000 : ℝ), (-109450391/625000000 : ℝ), (5611692667/10000000000 : ℝ)] ![(38907945150177/100000000000000 : ℝ), (11825561254707/100000000000000 : ℝ), (49266493582661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2314214207/5000000000 : ℝ)|^87 ≤ (38907945150177/100000000000000 : ℝ)^71
        have hw : |(2314214207/5000000000 : ℝ)|=(2314214207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109450391/625000000 : ℝ)|^87 ≤ (11825561254707/100000000000000 : ℝ)^71
        have hw : |(-109450391/625000000 : ℝ)|=(109450391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5611692667/10000000000 : ℝ)|^87 ≤ (49266493582661/100000000000000 : ℝ)^71
        have hw : |(5611692667/10000000000 : ℝ)|=(5611692667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (585785327/1250000000 : ℝ)*x 0 + (1558257653/2500000000 : ℝ)*x 1 + (-395350531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (585785327/1250000000 : ℝ)^87 ≤ (19752359534493/50000000000000 : ℝ)^71 := by
    have hnat : (585785327 : ℕ)^87*50000000000000^71 ≤ 19752359534493^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585785327 1250000000 19752359534493 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558257653/2500000000 : ℝ)^87 ≤ (28015882586551/50000000000000 : ℝ)^71 := by
    have hnat : (1558257653 : ℕ)^87*50000000000000^71 ≤ 28015882586551^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558257653 2500000000 28015882586551 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395350531/5000000000 : ℝ)^87 ≤ (2231757870783/50000000000000 : ℝ)^71 := by
    have hnat : (395350531 : ℕ)^87*50000000000000^71 ≤ 2231757870783^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395350531 5000000000 2231757870783 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(585785327/1250000000 : ℝ), (1558257653/2500000000 : ℝ), (-395350531/5000000000 : ℝ)] ![(19752359534493/50000000000000 : ℝ), (28015882586551/50000000000000 : ℝ), (2231757870783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(585785327/1250000000 : ℝ)|^87 ≤ (19752359534493/50000000000000 : ℝ)^71
        have hw : |(585785327/1250000000 : ℝ)|=(585785327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558257653/2500000000 : ℝ)|^87 ≤ (28015882586551/50000000000000 : ℝ)^71
        have hw : |(1558257653/2500000000 : ℝ)|=(1558257653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395350531/5000000000 : ℝ)|^87 ≤ (2231757870783/50000000000000 : ℝ)^71
        have hw : |(-395350531/5000000000 : ℝ)|=(395350531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6503190407/10000000000 : ℝ)*x 0 + (617469901/2500000000 : ℝ)*x 1 + (188063747/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6503190407/10000000000 : ℝ)^87 ≤ (1180440552653/2000000000000 : ℝ)^71 := by
    have hnat : (6503190407 : ℕ)^87*2000000000000^71 ≤ 1180440552653^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6503190407 10000000000 1180440552653 2000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617469901/2500000000 : ℝ)^87 ≤ (9011228304503/50000000000000 : ℝ)^71 := by
    have hnat : (617469901 : ℕ)^87*50000000000000^71 ≤ 9011228304503^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617469901 2500000000 9011228304503 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188063747/625000000 : ℝ)^87 ≤ (11477757869783/50000000000000 : ℝ)^71 := by
    have hnat : (188063747 : ℕ)^87*50000000000000^71 ≤ 11477757869783^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188063747 625000000 11477757869783 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6503190407/10000000000 : ℝ), (617469901/2500000000 : ℝ), (188063747/625000000 : ℝ)] ![(1180440552653/2000000000000 : ℝ), (9011228304503/50000000000000 : ℝ), (11477757869783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6503190407/10000000000 : ℝ)|^87 ≤ (1180440552653/2000000000000 : ℝ)^71
        have hw : |(6503190407/10000000000 : ℝ)|=(6503190407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(617469901/2500000000 : ℝ)|^87 ≤ (9011228304503/50000000000000 : ℝ)^71
        have hw : |(617469901/2500000000 : ℝ)|=(617469901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188063747/625000000 : ℝ)|^87 ≤ (11477757869783/50000000000000 : ℝ)^71
        have hw : |(188063747/625000000 : ℝ)|=(188063747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763554617/10000000000 : ℝ)*x 0 + (970339233/2500000000 : ℝ)*x 1 + (1258967191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763554617/10000000000 : ℝ)^87 ≤ (477112786019/4000000000000 : ℝ)^71 := by
    have hnat : (1763554617 : ℕ)^87*4000000000000^71 ≤ 477112786019^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763554617 10000000000 477112786019 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970339233/2500000000 : ℝ)^87 ≤ (31358852658033/100000000000000 : ℝ)^71 := by
    have hnat : (970339233 : ℕ)^87*100000000000000^71 ≤ 31358852658033^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970339233 2500000000 31358852658033 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1258967191/2000000000 : ℝ)^87 ≤ (56713327673321/100000000000000 : ℝ)^71 := by
    have hnat : (1258967191 : ℕ)^87*100000000000000^71 ≤ 56713327673321^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258967191 2000000000 56713327673321 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763554617/10000000000 : ℝ), (970339233/2500000000 : ℝ), (1258967191/2000000000 : ℝ)] ![(477112786019/4000000000000 : ℝ), (31358852658033/100000000000000 : ℝ), (56713327673321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763554617/10000000000 : ℝ)|^87 ≤ (477112786019/4000000000000 : ℝ)^71
        have hw : |(-1763554617/10000000000 : ℝ)|=(1763554617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(970339233/2500000000 : ℝ)|^87 ≤ (31358852658033/100000000000000 : ℝ)^71
        have hw : |(970339233/2500000000 : ℝ)|=(970339233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1258967191/2000000000 : ℝ)|^87 ≤ (56713327673321/100000000000000 : ℝ)^71
        have hw : |(1258967191/2000000000 : ℝ)|=(1258967191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (532392867/1250000000 : ℝ)*x 0 + (-1280761149/10000000000 : ℝ)*x 1 + (6302779201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532392867/1250000000 : ℝ)^87 ≤ (35138983430619/100000000000000 : ℝ)^71 := by
    have hnat : (532392867 : ℕ)^87*100000000000000^71 ≤ 35138983430619^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532392867 1250000000 35138983430619 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280761149/10000000000 : ℝ)^87 ≤ (8059984487607/100000000000000 : ℝ)^71 := by
    have hnat : (1280761149 : ℕ)^87*100000000000000^71 ≤ 8059984487607^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280761149 10000000000 8059984487607 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6302779201/10000000000 : ℝ)^87 ≤ (56801032067847/100000000000000 : ℝ)^71 := by
    have hnat : (6302779201 : ℕ)^87*100000000000000^71 ≤ 56801032067847^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6302779201 10000000000 56801032067847 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532392867/1250000000 : ℝ), (-1280761149/10000000000 : ℝ), (6302779201/10000000000 : ℝ)] ![(35138983430619/100000000000000 : ℝ), (8059984487607/100000000000000 : ℝ), (56801032067847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532392867/1250000000 : ℝ)|^87 ≤ (35138983430619/100000000000000 : ℝ)^71
        have hw : |(532392867/1250000000 : ℝ)|=(532392867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1280761149/10000000000 : ℝ)|^87 ≤ (8059984487607/100000000000000 : ℝ)^71
        have hw : |(-1280761149/10000000000 : ℝ)|=(1280761149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6302779201/10000000000 : ℝ)|^87 ≤ (56801032067847/100000000000000 : ℝ)^71
        have hw : |(6302779201/10000000000 : ℝ)|=(6302779201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4317458971/10000000000 : ℝ)*x 0 + (6919409843/10000000000 : ℝ)*x 1 + (-150981531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317458971/10000000000 : ℝ)^87 ≤ (8932358319053/25000000000000 : ℝ)^71 := by
    have hnat : (4317458971 : ℕ)^87*25000000000000^71 ≤ 8932358319053^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317458971 10000000000 8932358319053 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6919409843/10000000000 : ℝ)^87 ≤ (63683698662509/100000000000000 : ℝ)^71 := by
    have hnat : (6919409843 : ℕ)^87*100000000000000^71 ≤ 63683698662509^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6919409843 10000000000 63683698662509 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150981531/10000000000 : ℝ)^87 ≤ (58686804331/10000000000000 : ℝ)^71 := by
    have hnat : (150981531 : ℕ)^87*10000000000000^71 ≤ 58686804331^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150981531 10000000000 58686804331 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317458971/10000000000 : ℝ), (6919409843/10000000000 : ℝ), (-150981531/10000000000 : ℝ)] ![(8932358319053/25000000000000 : ℝ), (63683698662509/100000000000000 : ℝ), (58686804331/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317458971/10000000000 : ℝ)|^87 ≤ (8932358319053/25000000000000 : ℝ)^71
        have hw : |(4317458971/10000000000 : ℝ)|=(4317458971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6919409843/10000000000 : ℝ)|^87 ≤ (63683698662509/100000000000000 : ℝ)^71
        have hw : |(6919409843/10000000000 : ℝ)|=(6919409843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150981531/10000000000 : ℝ)|^87 ≤ (58686804331/10000000000000 : ℝ)^71
        have hw : |(-150981531/10000000000 : ℝ)|=(150981531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6487044153/10000000000 : ℝ)*x 0 + (3716326431/10000000000 : ℝ)*x 1 + (340517497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6487044153/10000000000 : ℝ)^87 ≤ (7355314182157/12500000000000 : ℝ)^71 := by
    have hnat : (6487044153 : ℕ)^87*12500000000000^71 ≤ 7355314182157^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6487044153 10000000000 7355314182157 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3716326431/10000000000 : ℝ)^87 ≤ (29732957011283/100000000000000 : ℝ)^71 := by
    have hnat : (3716326431 : ℕ)^87*100000000000000^71 ≤ 29732957011283^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716326431 10000000000 29732957011283 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340517497/2000000000 : ℝ)^87 ≤ (2856132378191/25000000000000 : ℝ)^71 := by
    have hnat : (340517497 : ℕ)^87*25000000000000^71 ≤ 2856132378191^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340517497 2000000000 2856132378191 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6487044153/10000000000 : ℝ), (3716326431/10000000000 : ℝ), (340517497/2000000000 : ℝ)] ![(7355314182157/12500000000000 : ℝ), (29732957011283/100000000000000 : ℝ), (2856132378191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6487044153/10000000000 : ℝ)|^87 ≤ (7355314182157/12500000000000 : ℝ)^71
        have hw : |(6487044153/10000000000 : ℝ)|=(6487044153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3716326431/10000000000 : ℝ)|^87 ≤ (29732957011283/100000000000000 : ℝ)^71
        have hw : |(3716326431/10000000000 : ℝ)|=(3716326431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340517497/2000000000 : ℝ)|^87 ≤ (2856132378191/25000000000000 : ℝ)^71
        have hw : |(340517497/2000000000 : ℝ)|=(340517497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-107190963/1250000000 : ℝ)*x 0 + (916219757/2000000000 : ℝ)*x 1 + (1572250879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107190963/1250000000 : ℝ)^87 ≤ (4930073326121/100000000000000 : ℝ)^71 := by
    have hnat : (107190963 : ℕ)^87*100000000000000^71 ≤ 4930073326121^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107190963 1250000000 4930073326121 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916219757/2000000000 : ℝ)^87 ≤ (38420981288541/100000000000000 : ℝ)^71 := by
    have hnat : (916219757 : ℕ)^87*100000000000000^71 ≤ 38420981288541^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916219757 2000000000 38420981288541 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572250879/2500000000 : ℝ)^87 ≤ (1416223634399/2500000000000 : ℝ)^71 := by
    have hnat : (1572250879 : ℕ)^87*2500000000000^71 ≤ 1416223634399^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572250879 2500000000 1416223634399 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107190963/1250000000 : ℝ), (916219757/2000000000 : ℝ), (1572250879/2500000000 : ℝ)] ![(4930073326121/100000000000000 : ℝ), (38420981288541/100000000000000 : ℝ), (1416223634399/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107190963/1250000000 : ℝ)|^87 ≤ (4930073326121/100000000000000 : ℝ)^71
        have hw : |(-107190963/1250000000 : ℝ)|=(107190963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916219757/2000000000 : ℝ)|^87 ≤ (38420981288541/100000000000000 : ℝ)^71
        have hw : |(916219757/2000000000 : ℝ)|=(916219757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1572250879/2500000000 : ℝ)|^87 ≤ (1416223634399/2500000000000 : ℝ)^71
        have hw : |(1572250879/2500000000 : ℝ)|=(1572250879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4237649583/10000000000 : ℝ)*x 0 + (-329288269/2500000000 : ℝ)*x 1 + (3148475303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237649583/10000000000 : ℝ)^87 ≤ (1746091049427/5000000000000 : ℝ)^71 := by
    have hnat : (4237649583 : ℕ)^87*5000000000000^71 ≤ 1746091049427^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237649583 10000000000 1746091049427 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329288269/2500000000 : ℝ)^87 ≤ (1668301019567/20000000000000 : ℝ)^71 := by
    have hnat : (329288269 : ℕ)^87*20000000000000^71 ≤ 1668301019567^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329288269 2500000000 1668301019567 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3148475303/5000000000 : ℝ)^87 ≤ (14184168475789/25000000000000 : ℝ)^71 := by
    have hnat : (3148475303 : ℕ)^87*25000000000000^71 ≤ 14184168475789^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3148475303 5000000000 14184168475789 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237649583/10000000000 : ℝ), (-329288269/2500000000 : ℝ), (3148475303/5000000000 : ℝ)] ![(1746091049427/5000000000000 : ℝ), (1668301019567/20000000000000 : ℝ), (14184168475789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237649583/10000000000 : ℝ)|^87 ≤ (1746091049427/5000000000000 : ℝ)^71
        have hw : |(4237649583/10000000000 : ℝ)|=(4237649583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329288269/2500000000 : ℝ)|^87 ≤ (1668301019567/20000000000000 : ℝ)^71
        have hw : |(-329288269/2500000000 : ℝ)|=(329288269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3148475303/5000000000 : ℝ)|^87 ≤ (14184168475789/25000000000000 : ℝ)^71
        have hw : |(3148475303/5000000000 : ℝ)|=(3148475303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (112705211/200000000 : ℝ)*x 0 + (1133454899/2000000000 : ℝ)*x 1 + (-156812411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112705211/200000000 : ℝ)^87 ≤ (49520149206977/100000000000000 : ℝ)^71 := by
    have hnat : (112705211 : ℕ)^87*100000000000000^71 ≤ 49520149206977^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112705211 200000000 49520149206977 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133454899/2000000000 : ℝ)^87 ≤ (24932545391943/50000000000000 : ℝ)^71 := by
    have hnat : (1133454899 : ℕ)^87*50000000000000^71 ≤ 24932545391943^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133454899 2000000000 24932545391943 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156812411/10000000000 : ℝ)^87 ≤ (76844999657/12500000000000 : ℝ)^71 := by
    have hnat : (156812411 : ℕ)^87*12500000000000^71 ≤ 76844999657^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156812411 10000000000 76844999657 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112705211/200000000 : ℝ), (1133454899/2000000000 : ℝ), (-156812411/10000000000 : ℝ)] ![(49520149206977/100000000000000 : ℝ), (24932545391943/50000000000000 : ℝ), (76844999657/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112705211/200000000 : ℝ)|^87 ≤ (49520149206977/100000000000000 : ℝ)^71
        have hw : |(112705211/200000000 : ℝ)|=(112705211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133454899/2000000000 : ℝ)|^87 ≤ (24932545391943/50000000000000 : ℝ)^71
        have hw : |(1133454899/2000000000 : ℝ)|=(1133454899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-156812411/10000000000 : ℝ)|^87 ≤ (76844999657/12500000000000 : ℝ)^71
        have hw : |(-156812411/10000000000 : ℝ)|=(156812411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7794968667/10000000000 : ℝ)*x 0 + (1047840199/5000000000 : ℝ)*x 1 + (1720191151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7794968667/10000000000 : ℝ)^87 ≤ (14738880919779/20000000000000 : ℝ)^71 := by
    have hnat : (7794968667 : ℕ)^87*20000000000000^71 ≤ 14738880919779^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7794968667 10000000000 14738880919779 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047840199/5000000000 : ℝ)^87 ≤ (460504882733/3125000000000 : ℝ)^71 := by
    have hnat : (1047840199 : ℕ)^87*3125000000000^71 ≤ 460504882733^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047840199 5000000000 460504882733 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720191151/10000000000 : ℝ)^87 ≤ (5784719567757/50000000000000 : ℝ)^71 := by
    have hnat : (1720191151 : ℕ)^87*50000000000000^71 ≤ 5784719567757^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720191151 10000000000 5784719567757 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7794968667/10000000000 : ℝ), (1047840199/5000000000 : ℝ), (1720191151/10000000000 : ℝ)] ![(14738880919779/20000000000000 : ℝ), (460504882733/3125000000000 : ℝ), (5784719567757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7794968667/10000000000 : ℝ)|^87 ≤ (14738880919779/20000000000000 : ℝ)^71
        have hw : |(7794968667/10000000000 : ℝ)|=(7794968667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047840199/5000000000 : ℝ)|^87 ≤ (460504882733/3125000000000 : ℝ)^71
        have hw : |(1047840199/5000000000 : ℝ)|=(1047840199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1720191151/10000000000 : ℝ)|^87 ≤ (5784719567757/50000000000000 : ℝ)^71
        have hw : |(1720191151/10000000000 : ℝ)|=(1720191151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-787500449/10000000000 : ℝ)*x 0 + (5182213547/10000000000 : ℝ)*x 1 + (1152092529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787500449/10000000000 : ℝ)^87 ≤ (4441386807923/100000000000000 : ℝ)^71 := by
    have hnat : (787500449 : ℕ)^87*100000000000000^71 ≤ 4441386807923^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787500449 10000000000 4441386807923 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182213547/10000000000 : ℝ)^87 ≤ (4468695126017/10000000000000 : ℝ)^71 := by
    have hnat : (5182213547 : ℕ)^87*10000000000000^71 ≤ 4468695126017^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182213547 10000000000 4468695126017 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152092529/2000000000 : ℝ)^87 ≤ (12717915479193/25000000000000 : ℝ)^71 := by
    have hnat : (1152092529 : ℕ)^87*25000000000000^71 ≤ 12717915479193^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152092529 2000000000 12717915479193 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787500449/10000000000 : ℝ), (5182213547/10000000000 : ℝ), (1152092529/2000000000 : ℝ)] ![(4441386807923/100000000000000 : ℝ), (4468695126017/10000000000000 : ℝ), (12717915479193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787500449/10000000000 : ℝ)|^87 ≤ (4441386807923/100000000000000 : ℝ)^71
        have hw : |(-787500449/10000000000 : ℝ)|=(787500449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182213547/10000000000 : ℝ)|^87 ≤ (4468695126017/10000000000000 : ℝ)^71
        have hw : |(5182213547/10000000000 : ℝ)|=(5182213547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152092529/2000000000 : ℝ)|^87 ≤ (12717915479193/25000000000000 : ℝ)^71
        have hw : |(1152092529/2000000000 : ℝ)|=(1152092529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5646969073/10000000000 : ℝ)*x 0 + (-389038381/5000000000 : ℝ)*x 1 + (5304020289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5646969073/10000000000 : ℝ)^87 ≤ (24823127141367/50000000000000 : ℝ)^71 := by
    have hnat : (5646969073 : ℕ)^87*50000000000000^71 ≤ 24823127141367^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646969073 10000000000 24823127141367 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389038381/5000000000 : ℝ)^87 ≤ (4376349620943/100000000000000 : ℝ)^71 := by
    have hnat : (389038381 : ℕ)^87*100000000000000^71 ≤ 4376349620943^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389038381 5000000000 4376349620943 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5304020289/10000000000 : ℝ)^87 ≤ (9195479215063/20000000000000 : ℝ)^71 := by
    have hnat : (5304020289 : ℕ)^87*20000000000000^71 ≤ 9195479215063^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304020289 10000000000 9195479215063 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5646969073/10000000000 : ℝ), (-389038381/5000000000 : ℝ), (5304020289/10000000000 : ℝ)] ![(24823127141367/50000000000000 : ℝ), (4376349620943/100000000000000 : ℝ), (9195479215063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5646969073/10000000000 : ℝ)|^87 ≤ (24823127141367/50000000000000 : ℝ)^71
        have hw : |(5646969073/10000000000 : ℝ)|=(5646969073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389038381/5000000000 : ℝ)|^87 ≤ (4376349620943/100000000000000 : ℝ)^71
        have hw : |(-389038381/5000000000 : ℝ)|=(389038381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5304020289/10000000000 : ℝ)|^87 ≤ (9195479215063/20000000000000 : ℝ)^71
        have hw : |(5304020289/10000000000 : ℝ)|=(5304020289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2074890057/5000000000 : ℝ)*x 0 + (3420039413/5000000000 : ℝ)*x 1 + (-598528743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074890057/5000000000 : ℝ)^87 ≤ (6807320945483/20000000000000 : ℝ)^71 := by
    have hnat : (2074890057 : ℕ)^87*20000000000000^71 ≤ 6807320945483^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074890057 5000000000 6807320945483 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3420039413/5000000000 : ℝ)^87 ≤ (31395093649457/50000000000000 : ℝ)^71 := by
    have hnat : (3420039413 : ℕ)^87*50000000000000^71 ≤ 31395093649457^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3420039413 5000000000 31395093649457 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598528743/10000000000 : ℝ)^87 ≤ (634641591827/20000000000000 : ℝ)^71 := by
    have hnat : (598528743 : ℕ)^87*20000000000000^71 ≤ 634641591827^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598528743 10000000000 634641591827 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074890057/5000000000 : ℝ), (3420039413/5000000000 : ℝ), (-598528743/10000000000 : ℝ)] ![(6807320945483/20000000000000 : ℝ), (31395093649457/50000000000000 : ℝ), (634641591827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074890057/5000000000 : ℝ)|^87 ≤ (6807320945483/20000000000000 : ℝ)^71
        have hw : |(2074890057/5000000000 : ℝ)|=(2074890057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3420039413/5000000000 : ℝ)|^87 ≤ (31395093649457/50000000000000 : ℝ)^71
        have hw : |(3420039413/5000000000 : ℝ)|=(3420039413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-598528743/10000000000 : ℝ)|^87 ≤ (634641591827/20000000000000 : ℝ)^71
        have hw : |(-598528743/10000000000 : ℝ)|=(598528743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325061_s1_s1_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8236278987/10000000000 : ℝ)*x 0 + (773150593/5000000000 : ℝ)*x 1 + (412936539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8236278987/10000000000 : ℝ)^87 ≤ (788389556831/1000000000000 : ℝ)^71 := by
    have hnat : (8236278987 : ℕ)^87*1000000000000^71 ≤ 788389556831^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8236278987 10000000000 788389556831 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773150593/5000000000 : ℝ)^87 ≤ (10153126546601/100000000000000 : ℝ)^71 := by
    have hnat : (773150593 : ℕ)^87*100000000000000^71 ≤ 10153126546601^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773150593 5000000000 10153126546601 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412936539/2500000000 : ℝ)^87 ≤ (5503958879747/50000000000000 : ℝ)^71 := by
    have hnat : (412936539 : ℕ)^87*50000000000000^71 ≤ 5503958879747^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412936539 2500000000 5503958879747 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8236278987/10000000000 : ℝ), (773150593/5000000000 : ℝ), (412936539/2500000000 : ℝ)] ![(788389556831/1000000000000 : ℝ), (10153126546601/100000000000000 : ℝ), (5503958879747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8236278987/10000000000 : ℝ)|^87 ≤ (788389556831/1000000000000 : ℝ)^71
        have hw : |(8236278987/10000000000 : ℝ)|=(8236278987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773150593/5000000000 : ℝ)|^87 ≤ (10153126546601/100000000000000 : ℝ)^71
        have hw : |(773150593/5000000000 : ℝ)|=(773150593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412936539/2500000000 : ℝ)|^87 ≤ (5503958879747/50000000000000 : ℝ)^71
        have hw : |(412936539/2500000000 : ℝ)|=(412936539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325061_s1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((68417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67693/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67693/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31423/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31423/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6523/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6523/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39307/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35437/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35437/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (68417/100000 : ℝ) ^ (85/16 : ℝ) ≤ (13314010447786051437/100000000000000000000 : ℝ) := by
    have hpowers : (68417/100000 : ℝ)^85 ≤ (13314010447786051437/100000000000000000000 : ℝ)^16 := by
      have hnat : (68417 : ℕ)^85*100000000000000000000^16 ≤ 13314010447786051437^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68417 100000 13314010447786051437 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68417/100000 : ℝ)) (X := (13314010447786051437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (113314010447786051437/100000000000000000000 : ℝ) ≤ (1279758740562589/1250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (113314010447786051437/100000000000000000000 : ℝ)^16 ≤ (1279758740562589/1250000000000000 : ℝ)^85 := by
      have hnat : (113314010447786051437 : ℕ)^16*1250000000000000^85 ≤ 1279758740562589^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113314010447786051437 100000000000000000000 1279758740562589 1250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1279758740562589/1250000000000000 : ℝ)) (X := (113314010447786051437/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (63314010447786051437/50000000000000000000 : ℝ) ≤ (2090882974746609/2000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (63314010447786051437/50000000000000000000 : ℝ)^16 ≤ (2090882974746609/2000000000000000 : ℝ)^85 := by
      have hnat : (63314010447786051437 : ℕ)^16*2000000000000000^85 ≤ 2090882974746609^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63314010447786051437 50000000000000000000 2090882974746609 2000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2090882974746609/2000000000000000 : ℝ)) (X := (63314010447786051437/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29758740562589/855212500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(216344949232333/6841700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (68417/100000 : ℝ)) (alpha := (29758740562589/855212500000000 : ℝ)) (beta := (216344949232333/6841700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68417/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29758740562589/855212500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(216344949232333/6841700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (67693/100000 : ℝ) ^ (85/16 : ℝ) ≤ (629120355375021687/5000000000000000000 : ℝ) := by
    have hpowers : (67693/100000 : ℝ)^85 ≤ (629120355375021687/5000000000000000000 : ℝ)^16 := by
      have hnat : (67693 : ℕ)^85*5000000000000000000^16 ≤ 629120355375021687^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67693 100000 629120355375021687 5000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67693/100000 : ℝ)) (X := (629120355375021687/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (5629120355375021687/5000000000000000000 : ℝ) ≤ (10225594588111961/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (5629120355375021687/5000000000000000000 : ℝ)^16 ≤ (10225594588111961/10000000000000000 : ℝ)^85 := by
      have hnat : (5629120355375021687 : ℕ)^16*10000000000000000^85 ≤ 10225594588111961^85*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629120355375021687 5000000000000000000 10225594588111961 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10225594588111961/10000000000000000 : ℝ)) (X := (5629120355375021687/5000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3129120355375021687/2500000000000000000 : ℝ) ≤ (10431568198849763/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3129120355375021687/2500000000000000000 : ℝ)^16 ≤ (10431568198849763/10000000000000000 : ℝ)^85 := by
      have hnat : (3129120355375021687 : ℕ)^16*10000000000000000^85 ≤ 10431568198849763^85*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3129120355375021687 2500000000000000000 10431568198849763 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10431568198849763/10000000000000000 : ℝ)) (X := (3129120355375021687/2500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(225594588111961/6769300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(102986805368901/3384650000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (67693/100000 : ℝ)) (alpha := (225594588111961/6769300000000000 : ℝ)) (beta := (102986805368901/3384650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (67693/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(225594588111961/6769300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(102986805368901/3384650000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (31423/50000 : ℝ) ^ (85/16 : ℝ) ≤ (8479104119553894857/100000000000000000000 : ℝ) := by
    have hpowers : (31423/50000 : ℝ)^85 ≤ (8479104119553894857/100000000000000000000 : ℝ)^16 := by
      have hnat : (31423 : ℕ)^85*100000000000000000000^16 ≤ 8479104119553894857^16*50000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31423 50000 8479104119553894857 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31423/50000 : ℝ)) (X := (8479104119553894857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (108479104119553894857/100000000000000000000 : ℝ) ≤ (10154379297785599/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (108479104119553894857/100000000000000000000 : ℝ)^16 ≤ (10154379297785599/10000000000000000 : ℝ)^85 := by
      have hnat : (108479104119553894857 : ℕ)^16*10000000000000000^85 ≤ 10154379297785599^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108479104119553894857 100000000000000000000 10154379297785599 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10154379297785599/10000000000000000 : ℝ)) (X := (108479104119553894857/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (58479104119553894857/50000000000000000000 : ℝ) ≤ (10299254265418879/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (58479104119553894857/50000000000000000000 : ℝ)^16 ≤ (10299254265418879/10000000000000000 : ℝ)^85 := by
      have hnat : (58479104119553894857 : ℕ)^16*10000000000000000^85 ≤ 10299254265418879^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58479104119553894857 50000000000000000000 10299254265418879 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10299254265418879/10000000000000000 : ℝ)) (X := (58479104119553894857/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(154379297785599/6284600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(226367136927/9819687500000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (31423/50000 : ℝ)) (alpha := (154379297785599/6284600000000000 : ℝ)) (beta := (226367136927/9819687500000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31423/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(154379297785599/6284600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(226367136927/9819687500000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-877413647/5000000000 : ℝ)*X 0 0+(34458877/78125000 : ℝ)*X 0 1+(363462939/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2314214207/5000000000 : ℝ)*X 1 0+(-109450391/625000000 : ℝ)*X 1 1+(5611692667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((585785327/1250000000 : ℝ)*X 2 0+(1558257653/2500000000 : ℝ)*X 2 1+(-395350531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6503190407/10000000000 : ℝ)*X 0 0+(617469901/2500000000 : ℝ)*X 0 1+(188063747/625000000 : ℝ)*X 0 2+(6503190407/10000000000 : ℝ)*X 1 0+(617469901/2500000000 : ℝ)*X 1 1+(188063747/625000000 : ℝ)*X 1 2+(6503190407/10000000000 : ℝ)*X 2 0+(617469901/2500000000 : ℝ)*X 2 1+(188063747/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1763554617/10000000000 : ℝ)*X 0 0+(970339233/2500000000 : ℝ)*X 0 1+(1258967191/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((532392867/1250000000 : ℝ)*X 1 0+(-1280761149/10000000000 : ℝ)*X 1 1+(6302779201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4317458971/10000000000 : ℝ)*X 2 0+(6919409843/10000000000 : ℝ)*X 2 1+(-150981531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6487044153/10000000000 : ℝ)*X 0 0+(3716326431/10000000000 : ℝ)*X 0 1+(340517497/2000000000 : ℝ)*X 0 2+(6487044153/10000000000 : ℝ)*X 1 0+(3716326431/10000000000 : ℝ)*X 1 1+(340517497/2000000000 : ℝ)*X 1 2+(6487044153/10000000000 : ℝ)*X 2 0+(3716326431/10000000000 : ℝ)*X 2 1+(340517497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-107190963/1250000000 : ℝ)*X 0 0+(916219757/2000000000 : ℝ)*X 0 1+(1572250879/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4237649583/10000000000 : ℝ)*X 1 0+(-329288269/2500000000 : ℝ)*X 1 1+(3148475303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((112705211/200000000 : ℝ)*X 2 0+(1133454899/2000000000 : ℝ)*X 2 1+(-156812411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7794968667/10000000000 : ℝ)*X 0 0+(1047840199/5000000000 : ℝ)*X 0 1+(1720191151/10000000000 : ℝ)*X 0 2+(7794968667/10000000000 : ℝ)*X 1 0+(1047840199/5000000000 : ℝ)*X 1 1+(1720191151/10000000000 : ℝ)*X 1 2+(7794968667/10000000000 : ℝ)*X 2 0+(1047840199/5000000000 : ℝ)*X 2 1+(1720191151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-787500449/10000000000 : ℝ)*X 0 0+(5182213547/10000000000 : ℝ)*X 0 1+(1152092529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5646969073/10000000000 : ℝ)*X 1 0+(-389038381/5000000000 : ℝ)*X 1 1+(5304020289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2074890057/5000000000 : ℝ)*X 2 0+(3420039413/5000000000 : ℝ)*X 2 1+(-598528743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8236278987/10000000000 : ℝ)*X 0 0+(773150593/5000000000 : ℝ)*X 0 1+(412936539/2500000000 : ℝ)*X 0 2+(8236278987/10000000000 : ℝ)*X 1 0+(773150593/5000000000 : ℝ)*X 1 1+(412936539/2500000000 : ℝ)*X 1 2+(8236278987/10000000000 : ℝ)*X 2 0+(773150593/5000000000 : ℝ)*X 2 1+(412936539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((6523/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6523/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11261881781762379996384712679271/727654866494815000000000000000000000 : ℝ) := by norm_num
    linear_combination (1322067/1000000000000 : ℝ)*(base50) + (550646099883/500000000000 : ℝ)*(base59) + (1921761/1000000000000 : ℝ)*(base60) + (131802891137/25000000000 : ℝ)*(major_s1_0) + (131802891137/25000000000 : ℝ)*(major_s1_1) + (131802891137/25000000000 : ℝ)*(major_s1_2) + (115153919/1000000000000 : ℝ)*(sp_s1_0) + (50880929/1000000000000 : ℝ)*(sp_s1_6) + (1584074322327/200000000000 : ℝ)*(sp_s1_7) + (49490171129/6250000000 : ℝ)*(sp_s1_8) + (495019739531/62500000000 : ℝ)*(sp_s1_9) + (1311844242743/500000000000 : ℝ)*(sp_s1_13) + (1029692457/500000000000 : ℝ)*(sp_s1_15) + (170933059/1000000000000 : ℝ)*(sp_s1_23) + (524747873283/200000000000 : ℝ)*(f.failure) + (3960243382777/500000000000 : ℝ)*(f.sum) + (6587198385636831621/10635585695000000000000000000000 : ℝ)*base63 + (131226017402281/157115000000000000000000000 : ℝ)*base65 + (284889899897611/676930000000000000000000000 : ℝ)*base66 + (84319686262577/314230000000000000000000000 : ℝ)*base69 + (1724877915864780483/2149867391000000000000000000000 : ℝ)*base71 + (467399668123/68417000000000000000000000 : ℝ)*base72 + (141521354351851/676930000000000000000000000 : ℝ)*base74 + (118602677360493/171042500000000000000000000 : ℝ)*base76 + (20174631074549794561/46313519810000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (12737/20000000000000000 : ℝ)*base87 + (12737/20000000000000000 : ℝ)*base89 + (12737/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39307/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31639622794248963703390959265053/3638274332474075000000000000000000000 : ℝ) := by norm_num
    linear_combination (9467/8000000000 : ℝ)*(base19) + (457369/1000000000000 : ℝ)*(base39) + (52350080821/100000000000 : ℝ)*(base59) + (1242505472371/250000000000 : ℝ)*(major_s1_0) + (1242505472371/250000000000 : ℝ)*(major_s1_1) + (1242505472371/250000000000 : ℝ)*(major_s1_2) + (22426713/1000000000000 : ℝ)*(sp_s1_2) + (19325557/1000000000000 : ℝ)*(sp_s1_6) + (2226793/50000000000 : ℝ)*(sp_s1_7) + (7466598004789/1000000000000 : ℝ)*(sp_s1_14) + (3733320678637/500000000000 : ℝ)*(sp_s1_15) + (466663757121/62500000000 : ℝ)*(sp_s1_16) + (247328268887/100000000000 : ℝ)*(sp_s1_20) + (9632511/100000000000 : ℝ)*(sp_s1_27) + (1236699169769/500000000000 : ℝ)*(f.failure) + (7466642540649/1000000000000 : ℝ)*(f.sum) + (29918822048435788119/53177928475000000000000000000000 : ℝ)*base63 + (14187744584533/62846000000000000000000000 : ℝ)*base65 + (562970850245857/1692325000000000000000000000 : ℝ)*base67 + (739298677436807/785575000000000000000000000 : ℝ)*base69 + (33077104133341697/26873342387500000000000000000000 : ℝ)*base70 + (212483418460107/427606250000000000000000000 : ℝ)*base73 + (2538661582044407/3384650000000000000000000000 : ℝ)*base75 + (153143824453533/427606250000000000000000000 : ℝ)*base77 + (52147291379900405683/115783799525000000000000000000000 : ℝ)*base79 + (13091/50000000000000000 : ℝ)*base87 + (13091/50000000000000000 : ℝ)*base89 + (13091/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35437/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35437/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10124749771998171184933432637337/1039506952135450000000000000000000000 : ℝ) := by norm_num
    linear_combination (5013099/500000000000 : ℝ)*(base11) + (268411/40000000000 : ℝ)*(base15) + (298542515571/1000000000000 : ℝ)*(base40) + (519706985303/1000000000000 : ℝ)*(base59) + (1069793941979/250000000000 : ℝ)*(major_s1_0) + (1069793941979/250000000000 : ℝ)*(major_s1_1) + (1069793941979/250000000000 : ℝ)*(major_s1_2) + (31219/200000000000 : ℝ)*(sp_s1_1) + (7906283/1000000000000 : ℝ)*(sp_s1_2) + (5216293/100000000000 : ℝ)*(sp_s1_9) + (12556150003/1953125000 : ℝ)*(sp_s1_21) + (1607187990341/250000000000 : ℝ)*(sp_s1_22) + (3214349379261/500000000000 : ℝ)*(sp_s1_23) + (532397365359/250000000000 : ℝ)*(sp_s1_27) + (532397365359/250000000000 : ℝ)*(f.failure) + (3214379413867/500000000000 : ℝ)*(f.sum) + (5059916416190791481/15193693850000000000000000000000 : ℝ)*base63 + (4427150879017/5611250000000000000000000 : ℝ)*base65 + (502744562260019/846162500000000000000000000 : ℝ)*base67 + (177996887605073/224450000000000000000000000 : ℝ)*base69 + (490649158016856169/959762228125000000000000000000 : ℝ)*base71 + (1543040142465969/3420850000000000000000000000 : ℝ)*base73 + (57884901389723/211540625000000000000000000 : ℝ)*base75 + (358696133316747/1710425000000000000000000000 : ℝ)*base76 + (2488782326559659369/14472974940625000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (27899/25000000000000000 : ℝ)*base86 + (27899/25000000000000000 : ℝ)*base88 + (27899/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((68417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67693/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67693/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31423/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31423/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6523/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6523/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39307/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35437/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35437/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c325061_s1 p hpa hpb X hX hprev0

#print axioms solution

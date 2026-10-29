-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:15:38.737225+00:00
-- url     : https://prove2.me/submissions/d96529d7-2982-4e92-afec-ce0daa21ea1b

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
theorem collision_support_c317061_s1_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-50892839/312500000 : ℝ)*x 0 + (2265937111/5000000000 : ℝ)*x 1 + (1506081267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50892839/312500000 : ℝ)^39 ≤ (5097672456003/50000000000000 : ℝ)^31 := by
    have hnat : (50892839 : ℕ)^39*50000000000000^31 ≤ 5097672456003^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50892839 312500000 5097672456003 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265937111/5000000000 : ℝ)^39 ≤ (36946674719967/100000000000000 : ℝ)^31 := by
    have hnat : (2265937111 : ℕ)^39*100000000000000^31 ≤ 36946674719967^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265937111 5000000000 36946674719967 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506081267/2500000000 : ℝ)^39 ≤ (13214495090471/25000000000000 : ℝ)^31 := by
    have hnat : (1506081267 : ℕ)^39*25000000000000^31 ≤ 13214495090471^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506081267 2500000000 13214495090471 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50892839/312500000 : ℝ), (2265937111/5000000000 : ℝ), (1506081267/2500000000 : ℝ)] ![(5097672456003/50000000000000 : ℝ), (36946674719967/100000000000000 : ℝ), (13214495090471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50892839/312500000 : ℝ)|^39 ≤ (5097672456003/50000000000000 : ℝ)^31
        have hw : |(-50892839/312500000 : ℝ)|=(50892839/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265937111/5000000000 : ℝ)|^39 ≤ (36946674719967/100000000000000 : ℝ)^31
        have hw : |(2265937111/5000000000 : ℝ)|=(2265937111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506081267/2500000000 : ℝ)|^39 ≤ (13214495090471/25000000000000 : ℝ)^31
        have hw : |(1506081267/2500000000 : ℝ)|=(1506081267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4704507947/10000000000 : ℝ)*x 0 + (-1610190313/10000000000 : ℝ)*x 1 + (293787873/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4704507947/10000000000 : ℝ)^39 ≤ (19362959986419/50000000000000 : ℝ)^31 := by
    have hnat : (4704507947 : ℕ)^39*50000000000000^31 ≤ 19362959986419^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704507947 10000000000 19362959986419 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1610190313/10000000000 : ℝ)^39 ≤ (10050793736277/100000000000000 : ℝ)^31 := by
    have hnat : (1610190313 : ℕ)^39*100000000000000^31 ≤ 10050793736277^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610190313 10000000000 10050793736277 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293787873/500000000 : ℝ)^39 ≤ (12805821569181/25000000000000 : ℝ)^31 := by
    have hnat : (293787873 : ℕ)^39*25000000000000^31 ≤ 12805821569181^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293787873 500000000 12805821569181 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4704507947/10000000000 : ℝ), (-1610190313/10000000000 : ℝ), (293787873/500000000 : ℝ)] ![(19362959986419/50000000000000 : ℝ), (10050793736277/100000000000000 : ℝ), (12805821569181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4704507947/10000000000 : ℝ)|^39 ≤ (19362959986419/50000000000000 : ℝ)^31
        have hw : |(4704507947/10000000000 : ℝ)|=(4704507947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1610190313/10000000000 : ℝ)|^39 ≤ (10050793736277/100000000000000 : ℝ)^31
        have hw : |(-1610190313/10000000000 : ℝ)|=(1610190313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(293787873/500000000 : ℝ)|^39 ≤ (12805821569181/25000000000000 : ℝ)^31
        have hw : |(293787873/500000000 : ℝ)|=(293787873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (955715939/2000000000 : ℝ)*x 0 + (6486304581/10000000000 : ℝ)*x 1 + (-532537917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955715939/2000000000 : ℝ)^39 ≤ (4936819570011/12500000000000 : ℝ)^31 := by
    have hnat : (955715939 : ℕ)^39*12500000000000^31 ≤ 4936819570011^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955715939 2000000000 4936819570011 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6486304581/10000000000 : ℝ)^39 ≤ (7250876953879/12500000000000 : ℝ)^31 := by
    have hnat : (6486304581 : ℕ)^39*12500000000000^31 ≤ 7250876953879^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6486304581 10000000000 7250876953879 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532537917/10000000000 : ℝ)^39 ≤ (1249213896363/50000000000000 : ℝ)^31 := by
    have hnat : (532537917 : ℕ)^39*50000000000000^31 ≤ 1249213896363^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532537917 10000000000 1249213896363 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(955715939/2000000000 : ℝ), (6486304581/10000000000 : ℝ), (-532537917/10000000000 : ℝ)] ![(4936819570011/12500000000000 : ℝ), (7250876953879/12500000000000 : ℝ), (1249213896363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(955715939/2000000000 : ℝ)|^39 ≤ (4936819570011/12500000000000 : ℝ)^31
        have hw : |(955715939/2000000000 : ℝ)|=(955715939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6486304581/10000000000 : ℝ)|^39 ≤ (7250876953879/12500000000000 : ℝ)^31
        have hw : |(6486304581/10000000000 : ℝ)|=(6486304581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532537917/10000000000 : ℝ)|^39 ≤ (1249213896363/50000000000000 : ℝ)^31
        have hw : |(-532537917/10000000000 : ℝ)|=(532537917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6582305069/10000000000 : ℝ)*x 0 + (2570638567/10000000000 : ℝ)*x 1 + (3088389597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6582305069/10000000000 : ℝ)^39 ≤ (14772289951561/25000000000000 : ℝ)^31 := by
    have hnat : (6582305069 : ℕ)^39*25000000000000^31 ≤ 14772289951561^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6582305069 10000000000 14772289951561 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570638567/10000000000 : ℝ)^39 ≤ (9052396004649/50000000000000 : ℝ)^31 := by
    have hnat : (2570638567 : ℕ)^39*50000000000000^31 ≤ 9052396004649^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570638567 10000000000 9052396004649 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3088389597/10000000000 : ℝ)^39 ≤ (11403024084257/50000000000000 : ℝ)^31 := by
    have hnat : (3088389597 : ℕ)^39*50000000000000^31 ≤ 11403024084257^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088389597 10000000000 11403024084257 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6582305069/10000000000 : ℝ), (2570638567/10000000000 : ℝ), (3088389597/10000000000 : ℝ)] ![(14772289951561/25000000000000 : ℝ), (9052396004649/50000000000000 : ℝ), (11403024084257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6582305069/10000000000 : ℝ)|^39 ≤ (14772289951561/25000000000000 : ℝ)^31
        have hw : |(6582305069/10000000000 : ℝ)|=(6582305069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570638567/10000000000 : ℝ)|^39 ≤ (9052396004649/50000000000000 : ℝ)^31
        have hw : |(2570638567/10000000000 : ℝ)|=(2570638567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3088389597/10000000000 : ℝ)|^39 ≤ (11403024084257/50000000000000 : ℝ)^31
        have hw : |(3088389597/10000000000 : ℝ)|=(3088389597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-112002001/625000000 : ℝ)*x 0 + (3468462691/10000000000 : ℝ)*x 1 + (34241873/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112002001/625000000 : ℝ)^39 ≤ (11499019232991/100000000000000 : ℝ)^31 := by
    have hnat : (112002001 : ℕ)^39*100000000000000^31 ≤ 11499019232991^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112002001 625000000 11499019232991 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3468462691/10000000000 : ℝ)^39 ≤ (26391417177751/100000000000000 : ℝ)^31 := by
    have hnat : (3468462691 : ℕ)^39*100000000000000^31 ≤ 26391417177751^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3468462691 10000000000 26391417177751 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34241873/50000000 : ℝ)^39 ≤ (62109563575711/100000000000000 : ℝ)^31 := by
    have hnat : (34241873 : ℕ)^39*100000000000000^31 ≤ 62109563575711^31*50000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34241873 50000000 62109563575711 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112002001/625000000 : ℝ), (3468462691/10000000000 : ℝ), (34241873/50000000 : ℝ)] ![(11499019232991/100000000000000 : ℝ), (26391417177751/100000000000000 : ℝ), (62109563575711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112002001/625000000 : ℝ)|^39 ≤ (11499019232991/100000000000000 : ℝ)^31
        have hw : |(-112002001/625000000 : ℝ)|=(112002001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3468462691/10000000000 : ℝ)|^39 ≤ (26391417177751/100000000000000 : ℝ)^31
        have hw : |(3468462691/10000000000 : ℝ)|=(3468462691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34241873/50000000 : ℝ)|^39 ≤ (62109563575711/100000000000000 : ℝ)^31
        have hw : |(34241873/50000000 : ℝ)|=(34241873/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (156534939/400000000 : ℝ)*x 0 + (-300743229/2500000000 : ℝ)*x 1 + (6866511367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156534939/400000000 : ℝ)^39 ≤ (7679682285633/25000000000000 : ℝ)^31 := by
    have hnat : (156534939 : ℕ)^39*25000000000000^31 ≤ 7679682285633^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156534939 400000000 7679682285633 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300743229/2500000000 : ℝ)^39 ≤ (6964701705007/100000000000000 : ℝ)^31 := by
    have hnat : (300743229 : ℕ)^39*100000000000000^31 ≤ 6964701705007^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300743229 2500000000 6964701705007 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6866511367/10000000000 : ℝ)^39 ≤ (62316569150521/100000000000000 : ℝ)^31 := by
    have hnat : (6866511367 : ℕ)^39*100000000000000^31 ≤ 62316569150521^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6866511367 10000000000 62316569150521 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156534939/400000000 : ℝ), (-300743229/2500000000 : ℝ), (6866511367/10000000000 : ℝ)] ![(7679682285633/25000000000000 : ℝ), (6964701705007/100000000000000 : ℝ), (62316569150521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156534939/400000000 : ℝ)|^39 ≤ (7679682285633/25000000000000 : ℝ)^31
        have hw : |(156534939/400000000 : ℝ)|=(156534939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300743229/2500000000 : ℝ)|^39 ≤ (6964701705007/100000000000000 : ℝ)^31
        have hw : |(-300743229/2500000000 : ℝ)|=(300743229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6866511367/10000000000 : ℝ)|^39 ≤ (62316569150521/100000000000000 : ℝ)^31
        have hw : |(6866511367/10000000000 : ℝ)|=(6866511367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3992787027/10000000000 : ℝ)*x 0 + (3700941287/5000000000 : ℝ)*x 1 + (-820013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3992787027/10000000000 : ℝ)^39 ≤ (7876253324887/25000000000000 : ℝ)^31 := by
    have hnat : (3992787027 : ℕ)^39*25000000000000^31 ≤ 7876253324887^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992787027 10000000000 7876253324887 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3700941287/5000000000 : ℝ)^39 ≤ (68489508052469/100000000000000 : ℝ)^31 := by
    have hnat : (3700941287 : ℕ)^39*100000000000000^31 ≤ 68489508052469^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3700941287 5000000000 68489508052469 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820013/2000000000 : ℝ)^39 ≤ (5478633183/100000000000000 : ℝ)^31 := by
    have hnat : (820013 : ℕ)^39*100000000000000^31 ≤ 5478633183^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820013 2000000000 5478633183 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3992787027/10000000000 : ℝ), (3700941287/5000000000 : ℝ), (-820013/2000000000 : ℝ)] ![(7876253324887/25000000000000 : ℝ), (68489508052469/100000000000000 : ℝ), (5478633183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3992787027/10000000000 : ℝ)|^39 ≤ (7876253324887/25000000000000 : ℝ)^31
        have hw : |(3992787027/10000000000 : ℝ)|=(3992787027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3700941287/5000000000 : ℝ)|^39 ≤ (68489508052469/100000000000000 : ℝ)^31
        have hw : |(3700941287/5000000000 : ℝ)|=(3700941287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-820013/2000000000 : ℝ)|^39 ≤ (5478633183/100000000000000 : ℝ)^31
        have hw : |(-820013/2000000000 : ℝ)|=(820013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5458389187/10000000000 : ℝ)*x 0 + (5044114229/10000000000 : ℝ)*x 1 + (867243167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5458389187/10000000000 : ℝ)^39 ≤ (2918032954019/6250000000000 : ℝ)^31 := by
    have hnat : (5458389187 : ℕ)^39*6250000000000^31 ≤ 2918032954019^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458389187 10000000000 2918032954019 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5044114229/10000000000 : ℝ)^39 ≤ (21137530622437/50000000000000 : ℝ)^31 := by
    have hnat : (5044114229 : ℕ)^39*50000000000000^31 ≤ 21137530622437^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044114229 10000000000 21137530622437 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (867243167/5000000000 : ℝ)^39 ≤ (2759102870089/25000000000000 : ℝ)^31 := by
    have hnat : (867243167 : ℕ)^39*25000000000000^31 ≤ 2759102870089^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867243167 5000000000 2759102870089 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5458389187/10000000000 : ℝ), (5044114229/10000000000 : ℝ), (867243167/5000000000 : ℝ)] ![(2918032954019/6250000000000 : ℝ), (21137530622437/50000000000000 : ℝ), (2759102870089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5458389187/10000000000 : ℝ)|^39 ≤ (2918032954019/6250000000000 : ℝ)^31
        have hw : |(5458389187/10000000000 : ℝ)|=(5458389187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5044114229/10000000000 : ℝ)|^39 ≤ (21137530622437/50000000000000 : ℝ)^31
        have hw : |(5044114229/10000000000 : ℝ)|=(5044114229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(867243167/5000000000 : ℝ)|^39 ≤ (2759102870089/25000000000000 : ℝ)^31
        have hw : |(867243167/5000000000 : ℝ)|=(867243167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-135680879/2000000000 : ℝ)*x 0 + (3858949379/10000000000 : ℝ)*x 1 + (7224393091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135680879/2000000000 : ℝ)^39 ≤ (3387952692109/100000000000000 : ℝ)^31 := by
    have hnat : (135680879 : ℕ)^39*100000000000000^31 ≤ 3387952692109^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135680879 2000000000 3387952692109 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3858949379/10000000000 : ℝ)^39 ≤ (30182237018083/100000000000000 : ℝ)^31 := by
    have hnat : (3858949379 : ℕ)^39*100000000000000^31 ≤ 30182237018083^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858949379 10000000000 30182237018083 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7224393091/10000000000 : ℝ)^39 ≤ (33214905140911/50000000000000 : ℝ)^31 := by
    have hnat : (7224393091 : ℕ)^39*50000000000000^31 ≤ 33214905140911^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7224393091 10000000000 33214905140911 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135680879/2000000000 : ℝ), (3858949379/10000000000 : ℝ), (7224393091/10000000000 : ℝ)] ![(3387952692109/100000000000000 : ℝ), (30182237018083/100000000000000 : ℝ), (33214905140911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135680879/2000000000 : ℝ)|^39 ≤ (3387952692109/100000000000000 : ℝ)^31
        have hw : |(-135680879/2000000000 : ℝ)|=(135680879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3858949379/10000000000 : ℝ)|^39 ≤ (30182237018083/100000000000000 : ℝ)^31
        have hw : |(3858949379/10000000000 : ℝ)|=(3858949379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7224393091/10000000000 : ℝ)|^39 ≤ (33214905140911/50000000000000 : ℝ)^31
        have hw : |(7224393091/10000000000 : ℝ)|=(7224393091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3241847727/10000000000 : ℝ)*x 0 + (-744383501/5000000000 : ℝ)*x 1 + (3621820253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3241847727/10000000000 : ℝ)^39 ≤ (24240721598653/100000000000000 : ℝ)^31 := by
    have hnat : (3241847727 : ℕ)^39*100000000000000^31 ≤ 24240721598653^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241847727 10000000000 24240721598653 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744383501/5000000000 : ℝ)^39 ≤ (9106734299341/100000000000000 : ℝ)^31 := by
    have hnat : (744383501 : ℕ)^39*100000000000000^31 ≤ 9106734299341^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744383501 5000000000 9106734299341 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3621820253/5000000000 : ℝ)^39 ≤ (66652544089303/100000000000000 : ℝ)^31 := by
    have hnat : (3621820253 : ℕ)^39*100000000000000^31 ≤ 66652544089303^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3621820253 5000000000 66652544089303 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3241847727/10000000000 : ℝ), (-744383501/5000000000 : ℝ), (3621820253/5000000000 : ℝ)] ![(24240721598653/100000000000000 : ℝ), (9106734299341/100000000000000 : ℝ), (66652544089303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3241847727/10000000000 : ℝ)|^39 ≤ (24240721598653/100000000000000 : ℝ)^31
        have hw : |(3241847727/10000000000 : ℝ)|=(3241847727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-744383501/5000000000 : ℝ)|^39 ≤ (9106734299341/100000000000000 : ℝ)^31
        have hw : |(-744383501/5000000000 : ℝ)|=(744383501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3621820253/5000000000 : ℝ)|^39 ≤ (66652544089303/100000000000000 : ℝ)^31
        have hw : |(3621820253/5000000000 : ℝ)|=(3621820253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1322153437/2000000000 : ℝ)*x 0 + (2436168897/5000000000 : ℝ)*x 1 + (-374669/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322153437/2000000000 : ℝ)^39 ≤ (59410778948873/100000000000000 : ℝ)^31 := by
    have hnat : (1322153437 : ℕ)^39*100000000000000^31 ≤ 59410778948873^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322153437 2000000000 59410778948873 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2436168897/5000000000 : ℝ)^39 ≤ (40471890412881/100000000000000 : ℝ)^31 := by
    have hnat : (2436168897 : ℕ)^39*100000000000000^31 ≤ 40471890412881^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436168897 5000000000 40471890412881 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374669/80000000 : ℝ)^39 ≤ (46932251/40000000000 : ℝ)^31 := by
    have hnat : (374669 : ℕ)^39*40000000000^31 ≤ 46932251^31*80000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374669 80000000 46932251 40000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322153437/2000000000 : ℝ), (2436168897/5000000000 : ℝ), (-374669/80000000 : ℝ)] ![(59410778948873/100000000000000 : ℝ), (40471890412881/100000000000000 : ℝ), (46932251/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322153437/2000000000 : ℝ)|^39 ≤ (59410778948873/100000000000000 : ℝ)^31
        have hw : |(1322153437/2000000000 : ℝ)|=(1322153437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2436168897/5000000000 : ℝ)|^39 ≤ (40471890412881/100000000000000 : ℝ)^31
        have hw : |(2436168897/5000000000 : ℝ)|=(2436168897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-374669/80000000 : ℝ)|^39 ≤ (46932251/40000000000 : ℝ)^31
        have hw : |(-374669/80000000 : ℝ)|=(374669/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (155886867/200000000 : ℝ)*x 0 + (503533981/2000000000 : ℝ)*x 1 + (755252789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155886867/200000000 : ℝ)^39 ≤ (7308894121437/10000000000000 : ℝ)^31 := by
    have hnat : (155886867 : ℕ)^39*10000000000000^31 ≤ 7308894121437^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155886867 200000000 7308894121437 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503533981/2000000000 : ℝ)^39 ≤ (8818360216923/50000000000000 : ℝ)^31 := by
    have hnat : (503533981 : ℕ)^39*50000000000000^31 ≤ 8818360216923^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503533981 2000000000 8818360216923 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755252789/5000000000 : ℝ)^39 ≤ (4637169170621/50000000000000 : ℝ)^31 := by
    have hnat : (755252789 : ℕ)^39*50000000000000^31 ≤ 4637169170621^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755252789 5000000000 4637169170621 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(155886867/200000000 : ℝ), (503533981/2000000000 : ℝ), (755252789/5000000000 : ℝ)] ![(7308894121437/10000000000000 : ℝ), (8818360216923/50000000000000 : ℝ), (4637169170621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(155886867/200000000 : ℝ)|^39 ≤ (7308894121437/10000000000000 : ℝ)^31
        have hw : |(155886867/200000000 : ℝ)|=(155886867/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503533981/2000000000 : ℝ)|^39 ≤ (8818360216923/50000000000000 : ℝ)^31
        have hw : |(503533981/2000000000 : ℝ)|=(503533981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755252789/5000000000 : ℝ)|^39 ≤ (4637169170621/50000000000000 : ℝ)^31
        have hw : |(755252789/5000000000 : ℝ)|=(755252789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-127972239/2500000000 : ℝ)*x 0 + (2903709587/5000000000 : ℝ)*x 1 + (2750518417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127972239/2500000000 : ℝ)^39 ≤ (237716773381/10000000000000 : ℝ)^31 := by
    have hnat : (127972239 : ℕ)^39*10000000000000^31 ≤ 237716773381^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127972239 2500000000 237716773381 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2903709587/5000000000 : ℝ)^39 ≤ (25237458075221/50000000000000 : ℝ)^31 := by
    have hnat : (2903709587 : ℕ)^39*50000000000000^31 ≤ 25237458075221^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2903709587 5000000000 25237458075221 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750518417/5000000000 : ℝ)^39 ≤ (47147916103403/100000000000000 : ℝ)^31 := by
    have hnat : (2750518417 : ℕ)^39*100000000000000^31 ≤ 47147916103403^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750518417 5000000000 47147916103403 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127972239/2500000000 : ℝ), (2903709587/5000000000 : ℝ), (2750518417/5000000000 : ℝ)] ![(237716773381/10000000000000 : ℝ), (25237458075221/50000000000000 : ℝ), (47147916103403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127972239/2500000000 : ℝ)|^39 ≤ (237716773381/10000000000000 : ℝ)^31
        have hw : |(-127972239/2500000000 : ℝ)|=(127972239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2903709587/5000000000 : ℝ)|^39 ≤ (25237458075221/50000000000000 : ℝ)^31
        have hw : |(2903709587/5000000000 : ℝ)|=(2903709587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750518417/5000000000 : ℝ)|^39 ≤ (47147916103403/100000000000000 : ℝ)^31
        have hw : |(2750518417/5000000000 : ℝ)|=(2750518417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6365321517/10000000000 : ℝ)*x 0 + (-2921517/62500000 : ℝ)*x 1 + (4944782177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6365321517/10000000000 : ℝ)^39 ≤ (28324571056331/50000000000000 : ℝ)^31 := by
    have hnat : (6365321517 : ℕ)^39*50000000000000^31 ≤ 28324571056331^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6365321517 10000000000 28324571056331 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2921517/62500000 : ℝ)^39 ≤ (1060235906287/50000000000000 : ℝ)^31 := by
    have hnat : (2921517 : ℕ)^39*50000000000000^31 ≤ 1060235906287^31*62500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921517 62500000 1060235906287 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4944782177/10000000000 : ℝ)^39 ≤ (41230386066459/100000000000000 : ℝ)^31 := by
    have hnat : (4944782177 : ℕ)^39*100000000000000^31 ≤ 41230386066459^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4944782177 10000000000 41230386066459 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6365321517/10000000000 : ℝ), (-2921517/62500000 : ℝ), (4944782177/10000000000 : ℝ)] ![(28324571056331/50000000000000 : ℝ), (1060235906287/50000000000000 : ℝ), (41230386066459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6365321517/10000000000 : ℝ)|^39 ≤ (28324571056331/50000000000000 : ℝ)^31
        have hw : |(6365321517/10000000000 : ℝ)|=(6365321517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2921517/62500000 : ℝ)|^39 ≤ (1060235906287/50000000000000 : ℝ)^31
        have hw : |(-2921517/62500000 : ℝ)|=(2921517/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4944782177/10000000000 : ℝ)|^39 ≤ (41230386066459/100000000000000 : ℝ)^31
        have hw : |(4944782177/10000000000 : ℝ)|=(4944782177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (426861901/1250000000 : ℝ)*x 0 + (7694747993/10000000000 : ℝ)*x 1 + (-120521967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426861901/1250000000 : ℝ)^39 ≤ (25879664433459/100000000000000 : ℝ)^31 := by
    have hnat : (426861901 : ℕ)^39*100000000000000^31 ≤ 25879664433459^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426861901 1250000000 25879664433459 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7694747993/10000000000 : ℝ)^39 ≤ (4494746796353/6250000000000 : ℝ)^31 := by
    have hnat : (7694747993 : ℕ)^39*6250000000000^31 ≤ 4494746796353^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7694747993 10000000000 4494746796353 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120521967/2500000000 : ℝ)^39 ≤ (2204386806079/100000000000000 : ℝ)^31 := by
    have hnat : (120521967 : ℕ)^39*100000000000000^31 ≤ 2204386806079^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120521967 2500000000 2204386806079 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426861901/1250000000 : ℝ), (7694747993/10000000000 : ℝ), (-120521967/2500000000 : ℝ)] ![(25879664433459/100000000000000 : ℝ), (4494746796353/6250000000000 : ℝ), (2204386806079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426861901/1250000000 : ℝ)|^39 ≤ (25879664433459/100000000000000 : ℝ)^31
        have hw : |(426861901/1250000000 : ℝ)|=(426861901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7694747993/10000000000 : ℝ)|^39 ≤ (4494746796353/6250000000000 : ℝ)^31
        have hw : |(7694747993/10000000000 : ℝ)|=(7694747993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120521967/2500000000 : ℝ)|^39 ≤ (2204386806079/100000000000000 : ℝ)^31
        have hw : |(-120521967/2500000000 : ℝ)|=(120521967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317061_s1_s1_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8510996847/10000000000 : ℝ)*x 0 + (60775071/400000000 : ℝ)*x 1 + (738456573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8510996847/10000000000 : ℝ)^39 ≤ (5102592430149/6250000000000 : ℝ)^31 := by
    have hnat : (8510996847 : ℕ)^39*6250000000000^31 ≤ 5102592430149^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8510996847 10000000000 5102592430149 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60775071/400000000 : ℝ)^39 ≤ (2335728668193/25000000000000 : ℝ)^31 := by
    have hnat : (60775071 : ℕ)^39*25000000000000^31 ≤ 2335728668193^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60775071 400000000 2335728668193 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738456573/5000000000 : ℝ)^39 ≤ (2253901608649/25000000000000 : ℝ)^31 := by
    have hnat : (738456573 : ℕ)^39*25000000000000^31 ≤ 2253901608649^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738456573 5000000000 2253901608649 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8510996847/10000000000 : ℝ), (60775071/400000000 : ℝ), (738456573/5000000000 : ℝ)] ![(5102592430149/6250000000000 : ℝ), (2335728668193/25000000000000 : ℝ), (2253901608649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8510996847/10000000000 : ℝ)|^39 ≤ (5102592430149/6250000000000 : ℝ)^31
        have hw : |(8510996847/10000000000 : ℝ)|=(8510996847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60775071/400000000 : ℝ)|^39 ≤ (2335728668193/25000000000000 : ℝ)^31
        have hw : |(60775071/400000000 : ℝ)|=(60775071/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738456573/5000000000 : ℝ)|^39 ≤ (2253901608649/25000000000000 : ℝ)^31
        have hw : |(738456573/5000000000 : ℝ)|=(738456573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317061_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((78021/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78021/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15359/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15359/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(73009/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27829/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27829/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12637/25000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (78021/100000 : ℝ) ^ (77/16 : ℝ) ≤ (30287812172209314459/100000000000000000000 : ℝ) := by
    have hpowers : (78021/100000 : ℝ)^77 ≤ (30287812172209314459/100000000000000000000 : ℝ)^16 := by
      have hnat : (78021 : ℕ)^77*100000000000000000000^16 ≤ 30287812172209314459^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78021 100000 30287812172209314459 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78021/100000 : ℝ)) (X := (30287812172209314459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (130287812172209314459/100000000000000000000 : ℝ) ≤ (10565160828227487/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (130287812172209314459/100000000000000000000 : ℝ)^16 ≤ (10565160828227487/10000000000000000 : ℝ)^77 := by
      have hnat : (130287812172209314459 : ℕ)^16*10000000000000000^77 ≤ 10565160828227487^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130287812172209314459 100000000000000000000 10565160828227487 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10565160828227487/10000000000000000 : ℝ)) (X := (130287812172209314459/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (80287812172209314459/50000000000000000000 : ℝ) ≤ (11034143360149927/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (80287812172209314459/50000000000000000000 : ℝ)^16 ≤ (11034143360149927/10000000000000000 : ℝ)^77 := by
      have hnat : (80287812172209314459 : ℕ)^16*10000000000000000^77 ≤ 11034143360149927^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80287812172209314459 50000000000000000000 11034143360149927 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11034143360149927/10000000000000000 : ℝ)) (X := (80287812172209314459/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(565160828227487/7802100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11724563298061/195052500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (78021/100000 : ℝ)) (alpha := (565160828227487/7802100000000000 : ℝ)) (beta := (11724563298061/195052500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (78021/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(565160828227487/7802100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11724563298061/195052500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (15359/20000 : ℝ) ^ (77/16 : ℝ) ≤ (3508122980246808731/12500000000000000000 : ℝ) := by
    have hpowers : (15359/20000 : ℝ)^77 ≤ (3508122980246808731/12500000000000000000 : ℝ)^16 := by
      have hnat : (15359 : ℕ)^77*12500000000000000000^16 ≤ 3508122980246808731^16*20000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15359 20000 3508122980246808731 12500000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15359/20000 : ℝ)) (X := (3508122980246808731/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (16008122980246808731/12500000000000000000 : ℝ) ≤ (1052745030010069/1000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (16008122980246808731/12500000000000000000 : ℝ)^16 ≤ (1052745030010069/1000000000000000 : ℝ)^77 := by
      have hnat : (16008122980246808731 : ℕ)^16*1000000000000000^77 ≤ 1052745030010069^77*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16008122980246808731 12500000000000000000 1052745030010069 1000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1052745030010069/1000000000000000 : ℝ)) (X := (16008122980246808731/12500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (9758122980246808731/6250000000000000000 : ℝ) ≤ (10969957352394269/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (9758122980246808731/6250000000000000000 : ℝ)^16 ≤ (10969957352394269/10000000000000000 : ℝ)^77 := by
      have hnat : (9758122980246808731 : ℕ)^16*10000000000000000^77 ≤ 10969957352394269^77*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9758122980246808731 6250000000000000000 10969957352394269 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10969957352394269/10000000000000000 : ℝ)) (X := (9758122980246808731/6250000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(52745030010069/767950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(442507052293579/7679500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (15359/20000 : ℝ)) (alpha := (52745030010069/767950000000000 : ℝ)) (beta := (442507052293579/7679500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15359/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(52745030010069/767950000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(442507052293579/7679500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (73009/100000 : ℝ) ^ (77/16 : ℝ) ≤ (5500965656153975149/25000000000000000000 : ℝ) := by
    have hpowers : (73009/100000 : ℝ)^77 ≤ (5500965656153975149/25000000000000000000 : ℝ)^16 := by
      have hnat : (73009 : ℕ)^77*25000000000000000000^16 ≤ 5500965656153975149^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73009 100000 5500965656153975149 25000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73009/100000 : ℝ)) (X := (5500965656153975149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (30500965656153975149/25000000000000000000 : ℝ) ≤ (1042192052465727/1000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (30500965656153975149/25000000000000000000 : ℝ)^16 ≤ (1042192052465727/1000000000000000 : ℝ)^77 := by
      have hnat : (30500965656153975149 : ℕ)^16*1000000000000000^77 ≤ 1042192052465727^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30500965656153975149 25000000000000000000 1042192052465727 1000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1042192052465727/1000000000000000 : ℝ)) (X := (30500965656153975149/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (18000965656153975149/12500000000000000000 : ℝ) ≤ (10787264635066731/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (18000965656153975149/12500000000000000000 : ℝ)^16 ≤ (10787264635066731/10000000000000000 : ℝ)^77 := by
      have hnat : (18000965656153975149 : ℕ)^16*10000000000000000^77 ≤ 10787264635066731^77*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18000965656153975149 12500000000000000000 10787264635066731 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10787264635066731/10000000000000000 : ℝ)) (X := (18000965656153975149/12500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(42192052465727/730090000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(365344110409461/7300900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (73009/100000 : ℝ)) (alpha := (42192052465727/730090000000000 : ℝ)) (beta := (365344110409461/7300900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (73009/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(42192052465727/730090000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(365344110409461/7300900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-50892839/312500000 : ℝ)*X 0 0+(2265937111/5000000000 : ℝ)*X 0 1+(1506081267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4704507947/10000000000 : ℝ)*X 1 0+(-1610190313/10000000000 : ℝ)*X 1 1+(293787873/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((955715939/2000000000 : ℝ)*X 2 0+(6486304581/10000000000 : ℝ)*X 2 1+(-532537917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6582305069/10000000000 : ℝ)*X 0 0+(2570638567/10000000000 : ℝ)*X 0 1+(3088389597/10000000000 : ℝ)*X 0 2+(6582305069/10000000000 : ℝ)*X 1 0+(2570638567/10000000000 : ℝ)*X 1 1+(3088389597/10000000000 : ℝ)*X 1 2+(6582305069/10000000000 : ℝ)*X 2 0+(2570638567/10000000000 : ℝ)*X 2 1+(3088389597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-112002001/625000000 : ℝ)*X 0 0+(3468462691/10000000000 : ℝ)*X 0 1+(34241873/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((156534939/400000000 : ℝ)*X 1 0+(-300743229/2500000000 : ℝ)*X 1 1+(6866511367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3992787027/10000000000 : ℝ)*X 2 0+(3700941287/5000000000 : ℝ)*X 2 1+(-820013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5458389187/10000000000 : ℝ)*X 0 0+(5044114229/10000000000 : ℝ)*X 0 1+(867243167/5000000000 : ℝ)*X 0 2+(5458389187/10000000000 : ℝ)*X 1 0+(5044114229/10000000000 : ℝ)*X 1 1+(867243167/5000000000 : ℝ)*X 1 2+(5458389187/10000000000 : ℝ)*X 2 0+(5044114229/10000000000 : ℝ)*X 2 1+(867243167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-135680879/2000000000 : ℝ)*X 0 0+(3858949379/10000000000 : ℝ)*X 0 1+(7224393091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3241847727/10000000000 : ℝ)*X 1 0+(-744383501/5000000000 : ℝ)*X 1 1+(3621820253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1322153437/2000000000 : ℝ)*X 2 0+(2436168897/5000000000 : ℝ)*X 2 1+(-374669/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((155886867/200000000 : ℝ)*X 0 0+(503533981/2000000000 : ℝ)*X 0 1+(755252789/5000000000 : ℝ)*X 0 2+(155886867/200000000 : ℝ)*X 1 0+(503533981/2000000000 : ℝ)*X 1 1+(755252789/5000000000 : ℝ)*X 1 2+(155886867/200000000 : ℝ)*X 2 0+(503533981/2000000000 : ℝ)*X 2 1+(755252789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-127972239/2500000000 : ℝ)*X 0 0+(2903709587/5000000000 : ℝ)*X 0 1+(2750518417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6365321517/10000000000 : ℝ)*X 1 0+(-2921517/62500000 : ℝ)*X 1 1+(4944782177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((426861901/1250000000 : ℝ)*X 2 0+(7694747993/10000000000 : ℝ)*X 2 1+(-120521967/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8510996847/10000000000 : ℝ)*X 0 0+(60775071/400000000 : ℝ)*X 0 1+(738456573/5000000000 : ℝ)*X 0 2+(8510996847/10000000000 : ℝ)*X 1 0+(60775071/400000000 : ℝ)*X 1 1+(738456573/5000000000 : ℝ)*X 1 2+(8510996847/10000000000 : ℝ)*X 2 0+(60775071/400000000 : ℝ)*X 2 1+(738456573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((10373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1224984552420104738890018673/99860378250000000000000000000000 : ℝ) := by norm_num
    linear_combination (109848461751/250000000000 : ℝ)*(base7) + (1931/15625000000 : ℝ)*(base50) + (453962254669/1000000000000 : ℝ)*(base59) + (1743228481439/500000000000 : ℝ)*(major_s1_0) + (1743228481439/500000000000 : ℝ)*(major_s1_1) + (1743228481439/500000000000 : ℝ)*(major_s1_2) + (12680877/500000000000 : ℝ)*(sp_s1_0) + (1099871/250000000000 : ℝ)*(sp_s1_6) + (478198127303/100000000000 : ℝ)*(sp_s1_7) + (1195508415067/250000000000 : ℝ)*(sp_s1_8) + (2391024727631/500000000000 : ℝ)*(sp_s1_9) + (1188898047107/500000000000 : ℝ)*(sp_s1_13) + (42820477/1000000000000 : ℝ)*(sp_s1_14) + (7897497/500000000000 : ℝ)*(sp_s1_15) + (969203323347/500000000000 : ℝ)*(f.failure) + (2391024727631/500000000000 : ℝ)*(f.sum) + (31788346415369359177/56067261550000000000000000000000 : ℝ)*base62 + (1513067238115273/1825225000000000000000000000 : ℝ)*base65 + (1689225370776439/959937500000000000000000000 : ℝ)*base67 + (207230167960569/365045000000000000000000000 : ℝ)*base69 + (7061159692047171533/71202939862500000000000000000000 : ℝ)*base70 + (31429517931163/48763125000000000000000000 : ℝ)*base73 + (46069464106311/383975000000000000000000000 : ℝ)*base75 + (2287232612677483/3901050000000000000000000000 : ℝ)*base77 + (158092710623285199851/299581134750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (30943/25000000000000000 : ℝ)*base86 + (30943/25000000000000000 : ℝ)*base88 + (30943/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27829/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27829/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29990085939829647653220802483121/2430235451884750000000000000000000000 : ℝ) := by norm_num
    linear_combination (620646431421/1000000000000 : ℝ)*(base7) + (4867159/500000000000 : ℝ)*(base53) + (10029149687/500000000000 : ℝ)*(base59) + (588818384173/250000000000 : ℝ)*(major_s1_0) + (588818384173/250000000000 : ℝ)*(major_s1_1) + (1177631901187/500000000000 : ℝ)*(major_s1_2) + (2137039/500000000000 : ℝ)*(sp_s1_6) + (1642067/62500000000 : ℝ)*(sp_s1_7) + (5442227/200000000000 : ℝ)*(sp_s1_8) + (3044425305437/1000000000000 : ℝ)*(sp_s1_14) + (1522212183687/500000000000 : ℝ)*(sp_s1_15) + (3044461312827/1000000000000 : ℝ)*(sp_s1_16) + (482516961399/250000000000 : ℝ)*(sp_s1_20) + (63551659/1000000000000 : ℝ)*(sp_s1_27) + (1309489239913/1000000000000 : ℝ)*(f.failure) + (3044461312827/1000000000000 : ℝ)*(f.sum) + (4709394853164659251/28033630775000000000000000000000 : ℝ)*base63 + (1019369499668023/3650450000000000000000000000 : ℝ)*base65 + (849129293441209/3839750000000000000000000000 : ℝ)*base67 + (30301409293787/91261250000000000000000000 : ℝ)*base69 + (1526750222535903871/17800734965625000000000000000000 : ℝ)*base71 + (156540555076651/780210000000000000000000000 : ℝ)*base73 + (89633396838749/383975000000000000000000000 : ℝ)*base75 + (1160968007229757/3901050000000000000000000000 : ℝ)*base77 + (33527804977828474139/299581134750000000000000000000000 : ℝ)*base79 + (16003/50000000000000000 : ℝ)*base87 + (16003/50000000000000000 : ℝ)*base89 + (16003/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12637/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23355553047389524802889103721519/2430235451884750000000000000000000000 : ℝ) := by norm_num
    linear_combination (380839519151/1000000000000 : ℝ)*(base7) + (5967923/1000000000000 : ℝ)*(base11) + (189589409917/1000000000000 : ℝ)*(base40) + (134705450549/1000000000000 : ℝ)*(base59) + (2436414578147/1000000000000 : ℝ)*(major_s1_0) + (2436414578147/1000000000000 : ℝ)*(major_s1_1) + (2436414578147/1000000000000 : ℝ)*(major_s1_2) + (118831/40000000000 : ℝ)*(sp_s1_1) + (492069/250000000000 : ℝ)*(sp_s1_2) + (24510791/250000000000 : ℝ)*(sp_s1_9) + (1649703228149/500000000000 : ℝ)*(sp_s1_21) + (3299409453447/1000000000000 : ℝ)*(sp_s1_22) + (1649656206391/500000000000 : ℝ)*(sp_s1_23) + (867720851009/500000000000 : ℝ)*(sp_s1_27) + (1354602182867/1000000000000 : ℝ)*(f.failure) + (3299412424221/1000000000000 : ℝ)*(f.sum) + (2636310428436381337/14016815387500000000000000000000 : ℝ)*base62 + (4591950936190947/7300900000000000000000000000 : ℝ)*base64 + (3123671142603887/7679500000000000000000000000 : ℝ)*base66 + (723753164389561/730090000000000000000000000 : ℝ)*base68 + (25315225165831086239/142405879725000000000000000000000 : ℝ)*base70 + (838467122433319/780210000000000000000000000 : ℝ)*base72 + (669644962782107/767950000000000000000000000 : ℝ)*base74 + (5961821862856691/7802100000000000000000000000 : ℝ)*base76 + (164429287669409020027/599162269500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (62177/50000000000000000 : ℝ)*base87 + (62177/50000000000000000 : ℝ)*base89 + (62177/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((78021/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78021/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15359/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15359/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(73009/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27829/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27829/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12637/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317061_s1 p hpa hpb X hX hprev0

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306059_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:57:34.633994+00:00
-- url     : https://prove2.me/submissions/259cbc06-772c-4190-8965-2cd73856922f

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
theorem collision_support_c306059_s4_s4_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-87584993/250000000 : ℝ)*x 0 + (3479104421/10000000000 : ℝ)*x 1 + (5861074517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87584993/250000000 : ℝ)^135 ≤ (12645672475311/50000000000000 : ℝ)^103 := by
    have hnat : (87584993 : ℕ)^135*50000000000000^103 ≤ 12645672475311^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87584993 250000000 12645672475311 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3479104421/10000000000 : ℝ)^135 ≤ (12530856534883/50000000000000 : ℝ)^103 := by
    have hnat : (3479104421 : ℕ)^135*50000000000000^103 ≤ 12530856534883^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3479104421 10000000000 12530856534883 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5861074517/10000000000 : ℝ)^135 ≤ (49646941957127/100000000000000 : ℝ)^103 := by
    have hnat : (5861074517 : ℕ)^135*100000000000000^103 ≤ 49646941957127^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5861074517 10000000000 49646941957127 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87584993/250000000 : ℝ), (3479104421/10000000000 : ℝ), (5861074517/10000000000 : ℝ)] ![(12645672475311/50000000000000 : ℝ), (12530856534883/50000000000000 : ℝ), (49646941957127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87584993/250000000 : ℝ)|^135 ≤ (12645672475311/50000000000000 : ℝ)^103
        have hw : |(-87584993/250000000 : ℝ)|=(87584993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3479104421/10000000000 : ℝ)|^135 ≤ (12530856534883/50000000000000 : ℝ)^103
        have hw : |(3479104421/10000000000 : ℝ)|=(3479104421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5861074517/10000000000 : ℝ)|^135 ≤ (49646941957127/100000000000000 : ℝ)^103
        have hw : |(5861074517/10000000000 : ℝ)|=(5861074517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1740562699/5000000000 : ℝ)*x 0 + (-216048119/625000000 : ℝ)*x 1 + (5898975529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740562699/5000000000 : ℝ)^135 ≤ (25080795794523/100000000000000 : ℝ)^103 := by
    have hnat : (1740562699 : ℕ)^135*100000000000000^103 ≤ 25080795794523^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740562699 5000000000 25080795794523 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216048119/625000000 : ℝ)^135 ≤ (4970210577737/20000000000000 : ℝ)^103 := by
    have hnat : (216048119 : ℕ)^135*20000000000000^103 ≤ 4970210577737^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216048119 625000000 4970210577737 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5898975529/10000000000 : ℝ)^135 ≤ (50068151304601/100000000000000 : ℝ)^103 := by
    have hnat : (5898975529 : ℕ)^135*100000000000000^103 ≤ 50068151304601^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5898975529 10000000000 50068151304601 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1740562699/5000000000 : ℝ), (-216048119/625000000 : ℝ), (5898975529/10000000000 : ℝ)] ![(25080795794523/100000000000000 : ℝ), (4970210577737/20000000000000 : ℝ), (50068151304601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1740562699/5000000000 : ℝ)|^135 ≤ (25080795794523/100000000000000 : ℝ)^103
        have hw : |(1740562699/5000000000 : ℝ)|=(1740562699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216048119/625000000 : ℝ)|^135 ≤ (4970210577737/20000000000000 : ℝ)^103
        have hw : |(-216048119/625000000 : ℝ)|=(216048119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5898975529/10000000000 : ℝ)|^135 ≤ (50068151304601/100000000000000 : ℝ)^103
        have hw : |(5898975529/10000000000 : ℝ)|=(5898975529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5647151271/10000000000 : ℝ)*x 0 + (1124587663/2000000000 : ℝ)*x 1 + (-70200983/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5647151271/10000000000 : ℝ)^135 ≤ (47285488759223/100000000000000 : ℝ)^103 := by
    have hnat : (5647151271 : ℕ)^135*100000000000000^103 ≤ 47285488759223^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5647151271 10000000000 47285488759223 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124587663/2000000000 : ℝ)^135 ≤ (11754983639359/25000000000000 : ℝ)^103 := by
    have hnat : (1124587663 : ℕ)^135*25000000000000^103 ≤ 11754983639359^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124587663 2000000000 11754983639359 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70200983/625000000 : ℝ)^135 ≤ (355911041773/6250000000000 : ℝ)^103 := by
    have hnat : (70200983 : ℕ)^135*6250000000000^103 ≤ 355911041773^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70200983 625000000 355911041773 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5647151271/10000000000 : ℝ), (1124587663/2000000000 : ℝ), (-70200983/625000000 : ℝ)] ![(47285488759223/100000000000000 : ℝ), (11754983639359/25000000000000 : ℝ), (355911041773/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5647151271/10000000000 : ℝ)|^135 ≤ (47285488759223/100000000000000 : ℝ)^103
        have hw : |(5647151271/10000000000 : ℝ)|=(5647151271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124587663/2000000000 : ℝ)|^135 ≤ (11754983639359/25000000000000 : ℝ)^103
        have hw : |(1124587663/2000000000 : ℝ)|=(1124587663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70200983/625000000 : ℝ)|^135 ≤ (355911041773/6250000000000 : ℝ)^103
        have hw : |(-70200983/625000000 : ℝ)|=(70200983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-79/5000000000 : ℝ)*x 0 + (79/5000000000 : ℝ)*x 1 + (9999999999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79/5000000000 : ℝ)^135 ≤ (1489/25000000000000 : ℝ)^103 := by
    have hnat : (79 : ℕ)^135*25000000000000^103 ≤ 1489^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79 5000000000 1489 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79/5000000000 : ℝ)^135 ≤ (1489/25000000000000 : ℝ)^103 := by
    have hnat : (79 : ℕ)^135*25000000000000^103 ≤ 1489^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79 5000000000 1489 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999999/10000000000 : ℝ)^135 ≤ (49999999993447/50000000000000 : ℝ)^103 := by
    have hnat : (9999999999 : ℕ)^135*50000000000000^103 ≤ 49999999993447^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 49999999993447 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79/5000000000 : ℝ), (79/5000000000 : ℝ), (9999999999/10000000000 : ℝ)] ![(1489/25000000000000 : ℝ), (1489/25000000000000 : ℝ), (49999999993447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79/5000000000 : ℝ)|^135 ≤ (1489/25000000000000 : ℝ)^103
        have hw : |(-79/5000000000 : ℝ)|=(79/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79/5000000000 : ℝ)|^135 ≤ (1489/25000000000000 : ℝ)^103
        have hw : |(79/5000000000 : ℝ)|=(79/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9999999999/10000000000 : ℝ)|^135 ≤ (49999999993447/50000000000000 : ℝ)^103
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (444628999/1000000000 : ℝ)*x 0 + (2299260821/5000000000 : ℝ)*x 1 + (245040839/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444628999/1000000000 : ℝ)^135 ≤ (34565104369697/100000000000000 : ℝ)^103 := by
    have hnat : (444628999 : ℕ)^135*100000000000000^103 ≤ 34565104369697^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444628999 1000000000 34565104369697 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299260821/5000000000 : ℝ)^135 ≤ (18062198187799/50000000000000 : ℝ)^103 := by
    have hnat : (2299260821 : ℕ)^135*50000000000000^103 ≤ 18062198187799^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299260821 5000000000 18062198187799 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245040839/625000000 : ℝ)^135 ≤ (915953101097/3125000000000 : ℝ)^103 := by
    have hnat : (245040839 : ℕ)^135*3125000000000^103 ≤ 915953101097^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245040839 625000000 915953101097 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(444628999/1000000000 : ℝ), (2299260821/5000000000 : ℝ), (245040839/625000000 : ℝ)] ![(34565104369697/100000000000000 : ℝ), (18062198187799/50000000000000 : ℝ), (915953101097/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(444628999/1000000000 : ℝ)|^135 ≤ (34565104369697/100000000000000 : ℝ)^103
        have hw : |(444628999/1000000000 : ℝ)|=(444628999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2299260821/5000000000 : ℝ)|^135 ≤ (18062198187799/50000000000000 : ℝ)^103
        have hw : |(2299260821/5000000000 : ℝ)|=(2299260821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(245040839/625000000 : ℝ)|^135 ≤ (915953101097/3125000000000 : ℝ)^103
        have hw : |(245040839/625000000 : ℝ)|=(245040839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-674961137/2000000000 : ℝ)*x 0 + (3059626113/10000000000 : ℝ)*x 1 + (6314534317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674961137/2000000000 : ℝ)^135 ≤ (24081596967771/100000000000000 : ℝ)^103 := by
    have hnat : (674961137 : ℕ)^135*100000000000000^103 ≤ 24081596967771^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674961137 2000000000 24081596967771 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059626113/10000000000 : ℝ)^135 ≤ (1058878203471/5000000000000 : ℝ)^103 := by
    have hnat : (3059626113 : ℕ)^135*5000000000000^103 ≤ 1058878203471^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059626113 10000000000 1058878203471 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6314534317/10000000000 : ℝ)^135 ≤ (27370419475891/50000000000000 : ℝ)^103 := by
    have hnat : (6314534317 : ℕ)^135*50000000000000^103 ≤ 27370419475891^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6314534317 10000000000 27370419475891 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-674961137/2000000000 : ℝ), (3059626113/10000000000 : ℝ), (6314534317/10000000000 : ℝ)] ![(24081596967771/100000000000000 : ℝ), (1058878203471/5000000000000 : ℝ), (27370419475891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-674961137/2000000000 : ℝ)|^135 ≤ (24081596967771/100000000000000 : ℝ)^103
        have hw : |(-674961137/2000000000 : ℝ)|=(674961137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059626113/10000000000 : ℝ)|^135 ≤ (1058878203471/5000000000000 : ℝ)^103
        have hw : |(3059626113/10000000000 : ℝ)|=(3059626113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6314534317/10000000000 : ℝ)|^135 ≤ (27370419475891/50000000000000 : ℝ)^103
        have hw : |(6314534317/10000000000 : ℝ)|=(6314534317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3357991133/10000000000 : ℝ)*x 0 + (-94664401/312500000 : ℝ)*x 1 + (6352535739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3357991133/10000000000 : ℝ)^135 ≤ (23924458789889/100000000000000 : ℝ)^103 := by
    have hnat : (3357991133 : ℕ)^135*100000000000000^103 ≤ 23924458789889^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357991133 10000000000 23924458789889 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94664401/312500000 : ℝ)^135 ≤ (20902515175873/100000000000000 : ℝ)^103 := by
    have hnat : (94664401 : ℕ)^135*100000000000000^103 ≤ 20902515175873^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94664401 312500000 20902515175873 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6352535739/10000000000 : ℝ)^135 ≤ (27586513007849/50000000000000 : ℝ)^103 := by
    have hnat : (6352535739 : ℕ)^135*50000000000000^103 ≤ 27586513007849^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6352535739 10000000000 27586513007849 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3357991133/10000000000 : ℝ), (-94664401/312500000 : ℝ), (6352535739/10000000000 : ℝ)] ![(23924458789889/100000000000000 : ℝ), (20902515175873/100000000000000 : ℝ), (27586513007849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3357991133/10000000000 : ℝ)|^135 ≤ (23924458789889/100000000000000 : ℝ)^103
        have hw : |(3357991133/10000000000 : ℝ)|=(3357991133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94664401/312500000 : ℝ)|^135 ≤ (20902515175873/100000000000000 : ℝ)^103
        have hw : |(-94664401/312500000 : ℝ)|=(94664401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6352535739/10000000000 : ℝ)|^135 ≤ (27586513007849/50000000000000 : ℝ)^103
        have hw : |(6352535739/10000000000 : ℝ)|=(6352535739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2741593691/5000000000 : ℝ)*x 0 + (6028013933/10000000000 : ℝ)*x 1 + (-344169623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2741593691/5000000000 : ℝ)^135 ≤ (22747097705651/50000000000000 : ℝ)^103 := by
    have hnat : (2741593691 : ℕ)^135*50000000000000^103 ≤ 22747097705651^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741593691 5000000000 22747097705651 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6028013933/10000000000 : ℝ)^135 ≤ (51508495876571/100000000000000 : ℝ)^103 := by
    have hnat : (6028013933 : ℕ)^135*100000000000000^103 ≤ 51508495876571^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6028013933 10000000000 51508495876571 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344169623/5000000000 : ℝ)^135 ≤ (1498654347947/50000000000000 : ℝ)^103 := by
    have hnat : (344169623 : ℕ)^135*50000000000000^103 ≤ 1498654347947^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344169623 5000000000 1498654347947 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2741593691/5000000000 : ℝ), (6028013933/10000000000 : ℝ), (-344169623/5000000000 : ℝ)] ![(22747097705651/50000000000000 : ℝ), (51508495876571/100000000000000 : ℝ), (1498654347947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2741593691/5000000000 : ℝ)|^135 ≤ (22747097705651/50000000000000 : ℝ)^103
        have hw : |(2741593691/5000000000 : ℝ)|=(2741593691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6028013933/10000000000 : ℝ)|^135 ≤ (51508495876571/100000000000000 : ℝ)^103
        have hw : |(6028013933/10000000000 : ℝ)|=(6028013933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344169623/5000000000 : ℝ)|^135 ≤ (1498654347947/50000000000000 : ℝ)^103
        have hw : |(-344169623/5000000000 : ℝ)|=(344169623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2127997231/5000000000 : ℝ)*x 0 + (2794484219/5000000000 : ℝ)*x 1 + (3008266591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127997231/5000000000 : ℝ)^135 ≤ (16319590240517/50000000000000 : ℝ)^103 := by
    have hnat : (2127997231 : ℕ)^135*50000000000000^103 ≤ 16319590240517^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127997231 5000000000 16319590240517 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794484219/5000000000 : ℝ)^135 ≤ (23323985285131/50000000000000 : ℝ)^103 := by
    have hnat : (2794484219 : ℕ)^135*50000000000000^103 ≤ 23323985285131^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794484219 5000000000 23323985285131 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008266591/10000000000 : ℝ)^135 ≤ (20712848930113/100000000000000 : ℝ)^103 := by
    have hnat : (3008266591 : ℕ)^135*100000000000000^103 ≤ 20712848930113^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008266591 10000000000 20712848930113 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127997231/5000000000 : ℝ), (2794484219/5000000000 : ℝ), (3008266591/10000000000 : ℝ)] ![(16319590240517/50000000000000 : ℝ), (23323985285131/50000000000000 : ℝ), (20712848930113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127997231/5000000000 : ℝ)|^135 ≤ (16319590240517/50000000000000 : ℝ)^103
        have hw : |(2127997231/5000000000 : ℝ)|=(2127997231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794484219/5000000000 : ℝ)|^135 ≤ (23323985285131/50000000000000 : ℝ)^103
        have hw : |(2794484219/5000000000 : ℝ)|=(2794484219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008266591/10000000000 : ℝ)|^135 ≤ (20712848930113/100000000000000 : ℝ)^103
        have hw : |(3008266591/10000000000 : ℝ)|=(3008266591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-614787621/2000000000 : ℝ)*x 0 + (838660103/2500000000 : ℝ)*x 1 + (1263936273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (614787621/2000000000 : ℝ)^135 ≤ (4261499409547/20000000000000 : ℝ)^103 := by
    have hnat : (614787621 : ℕ)^135*20000000000000^103 ≤ 4261499409547^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614787621 2000000000 4261499409547 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (838660103/2500000000 : ℝ)^135 ≤ (1493323389371/6250000000000 : ℝ)^103 := by
    have hnat : (838660103 : ℕ)^135*6250000000000^103 ≤ 1493323389371^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838660103 2500000000 1493323389371 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1263936273/2000000000 : ℝ)^135 ≤ (54799328714523/100000000000000 : ℝ)^103 := by
    have hnat : (1263936273 : ℕ)^135*100000000000000^103 ≤ 54799328714523^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263936273 2000000000 54799328714523 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-614787621/2000000000 : ℝ), (838660103/2500000000 : ℝ), (1263936273/2000000000 : ℝ)] ![(4261499409547/20000000000000 : ℝ), (1493323389371/6250000000000 : ℝ), (54799328714523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-614787621/2000000000 : ℝ)|^135 ≤ (4261499409547/20000000000000 : ℝ)^103
        have hw : |(-614787621/2000000000 : ℝ)|=(614787621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(838660103/2500000000 : ℝ)|^135 ≤ (1493323389371/6250000000000 : ℝ)^103
        have hw : |(838660103/2500000000 : ℝ)|=(838660103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1263936273/2000000000 : ℝ)|^135 ≤ (54799328714523/100000000000000 : ℝ)^103
        have hw : |(1263936273/2000000000 : ℝ)|=(1263936273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1525740957/5000000000 : ℝ)*x 0 + (-3330133593/10000000000 : ℝ)*x 1 + (1271536681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1525740957/5000000000 : ℝ)^135 ≤ (4220742053967/20000000000000 : ℝ)^103 := by
    have hnat : (1525740957 : ℕ)^135*20000000000000^103 ≤ 4220742053967^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525740957 5000000000 4220742053967 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3330133593/10000000000 : ℝ)^135 ≤ (11832328905521/50000000000000 : ℝ)^103 := by
    have hnat : (3330133593 : ℕ)^135*50000000000000^103 ≤ 11832328905521^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3330133593 10000000000 11832328905521 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271536681/2000000000 : ℝ)^135 ≤ (55231631902937/100000000000000 : ℝ)^103 := by
    have hnat : (1271536681 : ℕ)^135*100000000000000^103 ≤ 55231631902937^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271536681 2000000000 55231631902937 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1525740957/5000000000 : ℝ), (-3330133593/10000000000 : ℝ), (1271536681/2000000000 : ℝ)] ![(4220742053967/20000000000000 : ℝ), (11832328905521/50000000000000 : ℝ), (55231631902937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1525740957/5000000000 : ℝ)|^135 ≤ (4220742053967/20000000000000 : ℝ)^103
        have hw : |(1525740957/5000000000 : ℝ)|=(1525740957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3330133593/10000000000 : ℝ)|^135 ≤ (11832328905521/50000000000000 : ℝ)^103
        have hw : |(-3330133593/10000000000 : ℝ)|=(3330133593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271536681/2000000000 : ℝ)|^135 ≤ (55231631902937/100000000000000 : ℝ)^103
        have hw : |(1271536681/2000000000 : ℝ)|=(1271536681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6143886473/10000000000 : ℝ)*x 0 + (2682902471/5000000000 : ℝ)*x 1 + (-683192243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6143886473/10000000000 : ℝ)^135 ≤ (10562015192563/20000000000000 : ℝ)^103 := by
    have hnat : (6143886473 : ℕ)^135*20000000000000^103 ≤ 10562015192563^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6143886473 10000000000 10562015192563 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2682902471/5000000000 : ℝ)^135 ≤ (22110978145821/50000000000000 : ℝ)^103 := by
    have hnat : (2682902471 : ℕ)^135*50000000000000^103 ≤ 22110978145821^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682902471 5000000000 22110978145821 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683192243/10000000000 : ℝ)^135 ≤ (741991934427/25000000000000 : ℝ)^103 := by
    have hnat : (683192243 : ℕ)^135*25000000000000^103 ≤ 741991934427^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683192243 10000000000 741991934427 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6143886473/10000000000 : ℝ), (2682902471/5000000000 : ℝ), (-683192243/10000000000 : ℝ)] ![(10562015192563/20000000000000 : ℝ), (22110978145821/50000000000000 : ℝ), (741991934427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6143886473/10000000000 : ℝ)|^135 ≤ (10562015192563/20000000000000 : ℝ)^103
        have hw : |(6143886473/10000000000 : ℝ)|=(6143886473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2682902471/5000000000 : ℝ)|^135 ≤ (22110978145821/50000000000000 : ℝ)^103
        have hw : |(2682902471/5000000000 : ℝ)|=(2682902471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683192243/10000000000 : ℝ)|^135 ≤ (741991934427/25000000000000 : ℝ)^103
        have hw : |(-683192243/10000000000 : ℝ)|=(683192243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1054280073/2000000000 : ℝ)*x 0 + (4603813279/10000000000 : ℝ)*x 1 + (2997540181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054280073/2000000000 : ℝ)^135 ≤ (21602503542911/50000000000000 : ℝ)^103 := by
    have hnat : (1054280073 : ℕ)^135*50000000000000^103 ≤ 21602503542911^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054280073 2000000000 21602503542911 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4603813279/10000000000 : ℝ)^135 ≤ (36178890108237/100000000000000 : ℝ)^103 := by
    have hnat : (4603813279 : ℕ)^135*100000000000000^103 ≤ 36178890108237^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603813279 10000000000 36178890108237 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2997540181/10000000000 : ℝ)^135 ≤ (20616102791547/100000000000000 : ℝ)^103 := by
    have hnat : (2997540181 : ℕ)^135*100000000000000^103 ≤ 20616102791547^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997540181 10000000000 20616102791547 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054280073/2000000000 : ℝ), (4603813279/10000000000 : ℝ), (2997540181/10000000000 : ℝ)] ![(21602503542911/50000000000000 : ℝ), (36178890108237/100000000000000 : ℝ), (20616102791547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054280073/2000000000 : ℝ)|^135 ≤ (21602503542911/50000000000000 : ℝ)^103
        have hw : |(1054280073/2000000000 : ℝ)|=(1054280073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4603813279/10000000000 : ℝ)|^135 ≤ (36178890108237/100000000000000 : ℝ)^103
        have hw : |(4603813279/10000000000 : ℝ)|=(4603813279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2997540181/10000000000 : ℝ)|^135 ≤ (20616102791547/100000000000000 : ℝ)^103
        have hw : |(2997540181/10000000000 : ℝ)|=(2997540181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3511532443/10000000000 : ℝ)*x 0 + (872379113/2500000000 : ℝ)*x 1 + (1169055137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3511532443/10000000000 : ℝ)^135 ≤ (25368323771501/100000000000000 : ℝ)^103 := by
    have hnat : (3511532443 : ℕ)^135*100000000000000^103 ≤ 25368323771501^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3511532443 10000000000 25368323771501 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872379113/2500000000 : ℝ)^135 ≤ (25160063666629/100000000000000 : ℝ)^103 := by
    have hnat : (872379113 : ℕ)^135*100000000000000^103 ≤ 25160063666629^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872379113 2500000000 25160063666629 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169055137/2000000000 : ℝ)^135 ≤ (9894322508471/20000000000000 : ℝ)^103 := by
    have hnat : (1169055137 : ℕ)^135*20000000000000^103 ≤ 9894322508471^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169055137 2000000000 9894322508471 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3511532443/10000000000 : ℝ), (872379113/2500000000 : ℝ), (1169055137/2000000000 : ℝ)] ![(25368323771501/100000000000000 : ℝ), (25160063666629/100000000000000 : ℝ), (9894322508471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3511532443/10000000000 : ℝ)|^135 ≤ (25368323771501/100000000000000 : ℝ)^103
        have hw : |(-3511532443/10000000000 : ℝ)|=(3511532443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872379113/2500000000 : ℝ)|^135 ≤ (25160063666629/100000000000000 : ℝ)^103
        have hw : |(872379113/2500000000 : ℝ)|=(872379113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1169055137/2000000000 : ℝ)|^135 ≤ (9894322508471/20000000000000 : ℝ)^103
        have hw : |(1169055137/2000000000 : ℝ)|=(1169055137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (349157703/1000000000 : ℝ)*x 0 + (-21655083/62500000 : ℝ)*x 1 + (5883277621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (349157703/1000000000 : ℝ)^135 ≤ (5035907683567/20000000000000 : ℝ)^103 := by
    have hnat : (349157703 : ℕ)^135*20000000000000^103 ≤ 5035907683567^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349157703 1000000000 5035907683567 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21655083/62500000 : ℝ)^135 ≤ (3115858725279/12500000000000 : ℝ)^103 := by
    have hnat : (21655083 : ℕ)^135*12500000000000^103 ≤ 3115858725279^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21655083 62500000 3115858725279 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5883277621/10000000000 : ℝ)^135 ≤ (1995743670249/4000000000000 : ℝ)^103 := by
    have hnat : (5883277621 : ℕ)^135*4000000000000^103 ≤ 1995743670249^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5883277621 10000000000 1995743670249 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(349157703/1000000000 : ℝ), (-21655083/62500000 : ℝ), (5883277621/10000000000 : ℝ)] ![(5035907683567/20000000000000 : ℝ), (3115858725279/12500000000000 : ℝ), (1995743670249/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(349157703/1000000000 : ℝ)|^135 ≤ (5035907683567/20000000000000 : ℝ)^103
        have hw : |(349157703/1000000000 : ℝ)|=(349157703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21655083/62500000 : ℝ)|^135 ≤ (3115858725279/12500000000000 : ℝ)^103
        have hw : |(-21655083/62500000 : ℝ)|=(21655083/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5883277621/10000000000 : ℝ)|^135 ≤ (1995743670249/4000000000000 : ℝ)^103
        have hw : |(5883277621/10000000000 : ℝ)|=(5883277621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6282339453/10000000000 : ℝ)*x 0 + (1001773517/2000000000 : ℝ)*x 1 + (-1050736201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6282339453/10000000000 : ℝ)^135 ≤ (27187660481251/50000000000000 : ℝ)^103 := by
    have hnat : (6282339453 : ℕ)^135*50000000000000^103 ≤ 27187660481251^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6282339453 10000000000 27187660481251 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001773517/2000000000 : ℝ)^135 ≤ (1616273090411/4000000000000 : ℝ)^103 := by
    have hnat : (1001773517 : ℕ)^135*4000000000000^103 ≤ 1616273090411^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001773517 2000000000 1616273090411 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050736201/10000000000 : ℝ)^135 ≤ (652231469907/12500000000000 : ℝ)^103 := by
    have hnat : (1050736201 : ℕ)^135*12500000000000^103 ≤ 652231469907^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050736201 10000000000 652231469907 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6282339453/10000000000 : ℝ), (1001773517/2000000000 : ℝ), (-1050736201/10000000000 : ℝ)] ![(27187660481251/50000000000000 : ℝ), (1616273090411/4000000000000 : ℝ), (652231469907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6282339453/10000000000 : ℝ)|^135 ≤ (27187660481251/50000000000000 : ℝ)^103
        have hw : |(6282339453/10000000000 : ℝ)|=(6282339453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001773517/2000000000 : ℝ)|^135 ≤ (1616273090411/4000000000000 : ℝ)^103
        have hw : |(1001773517/2000000000 : ℝ)|=(1001773517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050736201/10000000000 : ℝ)|^135 ≤ (652231469907/12500000000000 : ℝ)^103
        have hw : |(-1050736201/10000000000 : ℝ)|=(1050736201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306059_s4_s4_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (197127791/625000000 : ℝ)*x 0 + (1181849507/2000000000 : ℝ)*x 1 + (3763400207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197127791/625000000 : ℝ)^135 ≤ (11019104373821/50000000000000 : ℝ)^103 := by
    have hnat : (197127791 : ℕ)^135*50000000000000^103 ≤ 11019104373821^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197127791 625000000 11019104373821 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181849507/2000000000 : ℝ)^135 ≤ (25091226698663/50000000000000 : ℝ)^103 := by
    have hnat : (1181849507 : ℕ)^135*50000000000000^103 ≤ 25091226698663^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181849507 2000000000 25091226698663 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3763400207/10000000000 : ℝ)^135 ≤ (13889668914999/50000000000000 : ℝ)^103 := by
    have hnat : (3763400207 : ℕ)^135*50000000000000^103 ≤ 13889668914999^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763400207 10000000000 13889668914999 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(197127791/625000000 : ℝ), (1181849507/2000000000 : ℝ), (3763400207/10000000000 : ℝ)] ![(11019104373821/50000000000000 : ℝ), (25091226698663/50000000000000 : ℝ), (13889668914999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(197127791/625000000 : ℝ)|^135 ≤ (11019104373821/50000000000000 : ℝ)^103
        have hw : |(197127791/625000000 : ℝ)|=(197127791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1181849507/2000000000 : ℝ)|^135 ≤ (25091226698663/50000000000000 : ℝ)^103
        have hw : |(1181849507/2000000000 : ℝ)|=(1181849507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3763400207/10000000000 : ℝ)|^135 ≤ (13889668914999/50000000000000 : ℝ)^103
        have hw : |(3763400207/10000000000 : ℝ)|=(3763400207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306059_s4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((4137/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4137/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5879/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5879/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6247/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6247/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30713/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30713/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1711/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1711/20000 : ℝ)*X 1 2) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (4137/6250 : ℝ) ^ (67/16 : ℝ) ≤ (8883682946974799077/50000000000000000000 : ℝ) := by
    have hpowers : (4137/6250 : ℝ)^67 ≤ (8883682946974799077/50000000000000000000 : ℝ)^16 := by
      have hnat : (4137 : ℕ)^67*50000000000000000000^16 ≤ 8883682946974799077^16*6250^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4137 6250 8883682946974799077 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4137/6250 : ℝ)) (X := (8883682946974799077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (58883682946974799077/50000000000000000000 : ℝ) ≤ (10398272267678217/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (58883682946974799077/50000000000000000000 : ℝ)^16 ≤ (10398272267678217/10000000000000000 : ℝ)^67 := by
      have hnat : (58883682946974799077 : ℕ)^16*10000000000000000^67 ≤ 10398272267678217^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58883682946974799077 50000000000000000000 10398272267678217 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10398272267678217/10000000000000000 : ℝ)) (X := (58883682946974799077/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (33883682946974799077/25000000000000000000 : ℝ) ≤ (5376559745488503/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (33883682946974799077/25000000000000000000 : ℝ)^16 ≤ (5376559745488503/5000000000000000 : ℝ)^67 := by
      have hnat : (33883682946974799077 : ℕ)^16*5000000000000000^67 ≤ 5376559745488503^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33883682946974799077 25000000000000000000 5376559745488503 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5376559745488503/5000000000000000 : ℝ)) (X := (33883682946974799077/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(398272267678217/6619200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(118282407766263/2206400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (4137/6250 : ℝ)) (alpha := (398272267678217/6619200000000000 : ℝ)) (beta := (118282407766263/2206400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4137/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(398272267678217/6619200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(118282407766263/2206400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (15911/25000 : ℝ) ^ (67/16 : ℝ) ≤ (7537102087435740099/50000000000000000000 : ℝ) := by
    have hpowers : (15911/25000 : ℝ)^67 ≤ (7537102087435740099/50000000000000000000 : ℝ)^16 := by
      have hnat : (15911 : ℕ)^67*50000000000000000000^16 ≤ 7537102087435740099^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15911 25000 7537102087435740099 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15911/25000 : ℝ)) (X := (7537102087435740099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (57537102087435740099/50000000000000000000 : ℝ) ≤ (10340984941159607/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (57537102087435740099/50000000000000000000 : ℝ)^16 ≤ (10340984941159607/10000000000000000 : ℝ)^67 := by
      have hnat : (57537102087435740099 : ℕ)^16*10000000000000000^67 ≤ 10340984941159607^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57537102087435740099 50000000000000000000 10340984941159607 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10340984941159607/10000000000000000 : ℝ)) (X := (57537102087435740099/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (32537102087435740099/25000000000000000000 : ℝ) ≤ (2129897378200701/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (32537102087435740099/25000000000000000000 : ℝ)^16 ≤ (2129897378200701/2000000000000000 : ℝ)^67 := by
      have hnat : (32537102087435740099 : ℕ)^16*2000000000000000^67 ≤ 2129897378200701^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32537102087435740099 25000000000000000000 2129897378200701 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2129897378200701/2000000000000000 : ℝ)) (X := (32537102087435740099/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(340984941159607/6364400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(154250974921949/3182200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (15911/25000 : ℝ)) (alpha := (340984941159607/6364400000000000 : ℝ)) (beta := (154250974921949/3182200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15911/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(340984941159607/6364400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(154250974921949/3182200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (5879/20000 : ℝ) ^ (67/16 : ℝ) ≤ (593465029330620291/100000000000000000000 : ℝ) := by
    have hpowers : (5879/20000 : ℝ)^67 ≤ (593465029330620291/100000000000000000000 : ℝ)^16 := by
      have hnat : (5879 : ℕ)^67*100000000000000000000^16 ≤ 593465029330620291^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5879 20000 593465029330620291 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5879/20000 : ℝ)) (X := (593465029330620291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (100593465029330620291/100000000000000000000 : ℝ) ≤ (5007070199581967/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (100593465029330620291/100000000000000000000 : ℝ)^16 ≤ (5007070199581967/5000000000000000 : ℝ)^67 := by
      have hnat : (100593465029330620291 : ℕ)^16*5000000000000000^67 ≤ 5007070199581967^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100593465029330620291 100000000000000000000 5007070199581967 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007070199581967/5000000000000000 : ℝ)) (X := (100593465029330620291/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (50593465029330620291/50000000000000000000 : ℝ) ≤ (10028217438923713/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50593465029330620291/50000000000000000000 : ℝ)^16 ≤ (10028217438923713/10000000000000000 : ℝ)^67 := by
      have hnat : (50593465029330620291 : ℕ)^16*10000000000000000^67 ≤ 10028217438923713^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50593465029330620291 50000000000000000000 10028217438923713 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028217438923713/10000000000000000 : ℝ)) (X := (50593465029330620291/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7070199581967/1469750000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(14077039759779/2939500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (5879/20000 : ℝ)) (alpha := (7070199581967/1469750000000000 : ℝ)) (beta := (14077039759779/2939500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5879/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7070199581967/1469750000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(14077039759779/2939500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-87584993/250000000 : ℝ)*X 0 0+(3479104421/10000000000 : ℝ)*X 0 1+(5861074517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((1740562699/5000000000 : ℝ)*X 1 0+(-216048119/625000000 : ℝ)*X 1 1+(5898975529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((5647151271/10000000000 : ℝ)*X 2 0+(1124587663/2000000000 : ℝ)*X 2 1+(-70200983/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_5 : ((-79/5000000000 : ℝ)*X 0 0+(79/5000000000 : ℝ)*X 0 1+(9999999999/10000000000 : ℝ)*X 0 2+(-79/5000000000 : ℝ)*X 1 0+(79/5000000000 : ℝ)*X 1 1+(9999999999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((444628999/1000000000 : ℝ)*X 0 0+(2299260821/5000000000 : ℝ)*X 0 1+(245040839/625000000 : ℝ)*X 0 2+(444628999/1000000000 : ℝ)*X 1 0+(2299260821/5000000000 : ℝ)*X 1 1+(245040839/625000000 : ℝ)*X 1 2+(444628999/1000000000 : ℝ)*X 2 0+(2299260821/5000000000 : ℝ)*X 2 1+(245040839/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-674961137/2000000000 : ℝ)*X 0 0+(3059626113/10000000000 : ℝ)*X 0 1+(6314534317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((3357991133/10000000000 : ℝ)*X 1 0+(-94664401/312500000 : ℝ)*X 1 1+(6352535739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2741593691/5000000000 : ℝ)*X 2 0+(6028013933/10000000000 : ℝ)*X 2 1+(-344169623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((2127997231/5000000000 : ℝ)*X 0 0+(2794484219/5000000000 : ℝ)*X 0 1+(3008266591/10000000000 : ℝ)*X 0 2+(2127997231/5000000000 : ℝ)*X 1 0+(2794484219/5000000000 : ℝ)*X 1 1+(3008266591/10000000000 : ℝ)*X 1 2+(2127997231/5000000000 : ℝ)*X 2 0+(2794484219/5000000000 : ℝ)*X 2 1+(3008266591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-614787621/2000000000 : ℝ)*X 0 0+(838660103/2500000000 : ℝ)*X 0 1+(1263936273/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((1525740957/5000000000 : ℝ)*X 1 0+(-3330133593/10000000000 : ℝ)*X 1 1+(1271536681/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((6143886473/10000000000 : ℝ)*X 2 0+(2682902471/5000000000 : ℝ)*X 2 1+(-683192243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((1054280073/2000000000 : ℝ)*X 0 0+(4603813279/10000000000 : ℝ)*X 0 1+(2997540181/10000000000 : ℝ)*X 0 2+(1054280073/2000000000 : ℝ)*X 1 0+(4603813279/10000000000 : ℝ)*X 1 1+(2997540181/10000000000 : ℝ)*X 1 2+(1054280073/2000000000 : ℝ)*X 2 0+(4603813279/10000000000 : ℝ)*X 2 1+(2997540181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-3511532443/10000000000 : ℝ)*X 0 0+(872379113/2500000000 : ℝ)*X 0 1+(1169055137/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((349157703/1000000000 : ℝ)*X 1 0+(-21655083/62500000 : ℝ)*X 1 1+(5883277621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((6282339453/10000000000 : ℝ)*X 2 0+(1001773517/2000000000 : ℝ)*X 2 1+(-1050736201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((197127791/625000000 : ℝ)*X 0 0+(1181849507/2000000000 : ℝ)*X 0 1+(3763400207/10000000000 : ℝ)*X 0 2+(197127791/625000000 : ℝ)*X 1 0+(1181849507/2000000000 : ℝ)*X 1 1+(3763400207/10000000000 : ℝ)*X 1 2+(197127791/625000000 : ℝ)*X 2 0+(1181849507/2000000000 : ℝ)*X 2 1+(3763400207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306059_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((6247/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6247/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8212515141201135604053/734875000000000000000000000 : ℝ) := by norm_num
    linear_combination (489105351703/250000000000 : ℝ)*(base60) + (4275042220349/500000000000 : ℝ)*(major_s4_0) + (4275042220349/500000000000 : ℝ)*(major_s4_1) + (8550754257097/1000000000000 : ℝ)*(major_s4_2) + (10299177/250000000000 : ℝ)*(sp_s4_0) + (27902707/1000000000000 : ℝ)*(sp_s4_1) + (102878803/1000000000000 : ℝ)*(sp_s4_2) + (1674541/2500000000 : ℝ)*(sp_s4_5) + (288870466313/25000000000 : ℝ)*(sp_s4_7) + (11554637047117/1000000000000 : ℝ)*(sp_s4_8) + (5777378485213/500000000000 : ℝ)*(sp_s4_9) + (5545258954983/1000000000000 : ℝ)*(sp_s4_13) + (38979881/200000000000 : ℝ)*(sp_s4_15) + (46352047/1000000000000 : ℝ)*(sp_s4_27) + (554530530703/100000000000 : ℝ)*(f.failure) + (11554859849229/1000000000000 : ℝ)*(f.sum) + (46307053642788921771/93540769000000000000000000000000 : ℝ)*base62 + (450649327799913/2939500000000000000000000000 : ℝ)*base65 + (520331599989179/1591100000000000000000000000 : ℝ)*base66 + (46197234157803/183718750000000000000000000 : ℝ)*base68 + (6072137333718439817/97285692000000000000000000000000 : ℝ)*base70 + (1025736960991573/1103200000000000000000000000 : ℝ)*base72 + (301857746097783/3182200000000000000000000000 : ℝ)*base75 + (536067705199813/3309600000000000000000000000 : ℝ)*base77 + (409520387362387907/2507573600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (3621/5000000000000000 : ℝ)*base86 + (3621/5000000000000000 : ℝ)*base88 + (1379/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30713/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30713/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36522199138004560426138733547/2106003599200000000000000000000000 : ℝ) := by norm_num
    linear_combination (1927600124151/1000000000000 : ℝ)*(base60) + (8430777970739/1000000000000 : ℝ)*(major_s4_0) + (8430777970739/1000000000000 : ℝ)*(major_s4_1) + (187188618431/6250000000 : ℝ)*(major_s4_2) + (42655603/1000000000000 : ℝ)*(sp_s4_0) + (1127251/25000000000 : ℝ)*(sp_s4_1) + (21519400978221/1000000000000 : ℝ)*(sp_s4_5) + (62589589/1000000000000 : ℝ)*(sp_s4_6) + (42374811/200000000000 : ℝ)*(sp_s4_7) + (2848342150249/250000000000 : ℝ)*(sp_s4_14) + (2278715608123/200000000000 : ℝ)*(sp_s4_15) + (2278691642367/200000000000 : ℝ)*(sp_s4_16) + (2733932220291/500000000000 : ℝ)*(sp_s4_20) + (8245941/50000000000 : ℝ)*(sp_s4_23) + (5467927030171/1000000000000 : ℝ)*(f.failure) + (2278724626131/200000000000 : ℝ)*(f.sum) + (1634724879328518897/7483261520000000000000000000000 : ℝ)*base62 + (6501120049463/36743750000000000000000000 : ℝ)*base65 + (879609684668051/3182200000000000000000000000 : ℝ)*base67 + (11346414336601/73487500000000000000000000 : ℝ)*base68 + (5277832038237569213/38914276800000000000000000000000 : ℝ)*base71 + (787314370920523/2206400000000000000000000000 : ℝ)*base72 + (2646963842220627/6364400000000000000000000000 : ℝ)*base74 + (2298092803696757/6619200000000000000000000000 : ℝ)*base76 + (198958869428480563/5015147200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (22903/50000000000000000 : ℝ)*base87 + (22903/50000000000000000 : ℝ)*base89 + (22903/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1711/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1711/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (176789061723852332669851641927/36855062986000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64619/200000000000 : ℝ)*(base8) + (658861/1000000000000 : ℝ)*(base40) + (775963/1000000000000 : ℝ)*(base50) + (177650554679/200000000000 : ℝ)*(base60) + (5923655850501/1000000000000 : ℝ)*(major_s4_0) + (5923655850501/1000000000000 : ℝ)*(major_s4_1) + (5923655850501/1000000000000 : ℝ)*(major_s4_2) + (30184879/1000000000000 : ℝ)*(sp_s4_2) + (18564947/500000000000 : ℝ)*(sp_s4_13) + (26852529/1000000000000 : ℝ)*(sp_s4_16) + (3908896587/488281250 : ℝ)*(sp_s4_21) + (8005420533271/1000000000000 : ℝ)*(sp_s4_22) + (8005363495863/1000000000000 : ℝ)*(sp_s4_23) + (30734819511/8000000000 : ℝ)*(sp_s4_27) + (1875922641/488281250 : ℝ)*(f.failure) + (8005420533271/1000000000000 : ℝ)*(f.sum) + (49131186943423588769/187081538000000000000000000000000 : ℝ)*base63 + (453220451194271/2939500000000000000000000000 : ℝ)*base64 + (1266447980444131/3182200000000000000000000000 : ℝ)*base66 + (44014093387517/1469750000000000000000000000 : ℝ)*base68 + (25707552797868500339/64857128000000000000000000000000 : ℝ)*base70 + (148303503885037/2206400000000000000000000000 : ℝ)*base72 + (969647612472187/6364400000000000000000000000 : ℝ)*base75 + (961327004610961/2206400000000000000000000000 : ℝ)*base76 + (2670954929509570117/5015147200000000000000000000000 : ℝ)*base78 + (1161/3125000000000000 : ℝ)*base86 + (1161/3125000000000000 : ℝ)*base88 + (1161/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((4137/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4137/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5879/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5879/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6247/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6247/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30713/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30713/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1711/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1711/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306059_s4 p hpa hpb X hX hprev3

#print axioms solution

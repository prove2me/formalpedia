-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:03:20.366031+00:00
-- url     : https://prove2.me/submissions/7e7d47b9-13c1-485d-a8b1-1c45b128965b

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
theorem collision_support_c311086_s2_s2_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-421591451/5000000000 : ℝ)*x 0 + (-1442496551/2500000000 : ℝ)*x 1 + (5515316099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421591451/5000000000 : ℝ)^9 ≤ (415951124941/10000000000000 : ℝ)^7 := by
    have hnat : (421591451 : ℕ)^9*10000000000000^7 ≤ 415951124941^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421591451 5000000000 415951124941 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1442496551/2500000000 : ℝ)^9 ≤ (49310453436287/100000000000000 : ℝ)^7 := by
    have hnat : (1442496551 : ℕ)^9*100000000000000^7 ≤ 49310453436287^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442496551 2500000000 49310453436287 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515316099/10000000000 : ℝ)^9 ≤ (1454063602927/3125000000000 : ℝ)^7 := by
    have hnat : (5515316099 : ℕ)^9*3125000000000^7 ≤ 1454063602927^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515316099 10000000000 1454063602927 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421591451/5000000000 : ℝ), (-1442496551/2500000000 : ℝ), (5515316099/10000000000 : ℝ)] ![(415951124941/10000000000000 : ℝ), (49310453436287/100000000000000 : ℝ), (1454063602927/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421591451/5000000000 : ℝ)|^9 ≤ (415951124941/10000000000000 : ℝ)^7
        have hw : |(-421591451/5000000000 : ℝ)|=(421591451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1442496551/2500000000 : ℝ)|^9 ≤ (49310453436287/100000000000000 : ℝ)^7
        have hw : |(-1442496551/2500000000 : ℝ)|=(1442496551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515316099/10000000000 : ℝ)|^9 ≤ (1454063602927/3125000000000 : ℝ)^7
        have hw : |(5515316099/10000000000 : ℝ)|=(5515316099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5589984131/10000000000 : ℝ)*x 0 + (-1825071493/5000000000 : ℝ)*x 1 + (-3432596889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5589984131/10000000000 : ℝ)^9 ≤ (23670758370079/50000000000000 : ℝ)^7 := by
    have hnat : (5589984131 : ℕ)^9*50000000000000^7 ≤ 23670758370079^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589984131 10000000000 23670758370079 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1825071493/5000000000 : ℝ)^9 ≤ (27368787431329/100000000000000 : ℝ)^7 := by
    have hnat : (1825071493 : ℕ)^9*100000000000000^7 ≤ 27368787431329^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825071493 5000000000 27368787431329 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3432596889/10000000000 : ℝ)^9 ≤ (1264484791243/5000000000000 : ℝ)^7 := by
    have hnat : (3432596889 : ℕ)^9*5000000000000^7 ≤ 1264484791243^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432596889 10000000000 1264484791243 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5589984131/10000000000 : ℝ), (-1825071493/5000000000 : ℝ), (-3432596889/10000000000 : ℝ)] ![(23670758370079/50000000000000 : ℝ), (27368787431329/100000000000000 : ℝ), (1264484791243/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5589984131/10000000000 : ℝ)|^9 ≤ (23670758370079/50000000000000 : ℝ)^7
        have hw : |(5589984131/10000000000 : ℝ)|=(5589984131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1825071493/5000000000 : ℝ)|^9 ≤ (27368787431329/100000000000000 : ℝ)^7
        have hw : |(-1825071493/5000000000 : ℝ)|=(1825071493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3432596889/10000000000 : ℝ)|^9 ≤ (1264484791243/5000000000000 : ℝ)^7
        have hw : |(-3432596889/10000000000 : ℝ)|=(3432596889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (907302047/2000000000 : ℝ)*x 0 + (-833328149/2500000000 : ℝ)*x 1 + (2425518987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907302047/2000000000 : ℝ)^9 ≤ (36194487909943/100000000000000 : ℝ)^7 := by
    have hnat : (907302047 : ℕ)^9*100000000000000^7 ≤ 36194487909943^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907302047 2000000000 36194487909943 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833328149/2500000000 : ℝ)^9 ≤ (24353137060301/100000000000000 : ℝ)^7 := by
    have hnat : (833328149 : ℕ)^9*100000000000000^7 ≤ 24353137060301^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833328149 2500000000 24353137060301 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2425518987/5000000000 : ℝ)^9 ≤ (2465773438513/6250000000000 : ℝ)^7 := by
    have hnat : (2425518987 : ℕ)^9*6250000000000^7 ≤ 2465773438513^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425518987 5000000000 2465773438513 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(907302047/2000000000 : ℝ), (-833328149/2500000000 : ℝ), (2425518987/5000000000 : ℝ)] ![(36194487909943/100000000000000 : ℝ), (24353137060301/100000000000000 : ℝ), (2465773438513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(907302047/2000000000 : ℝ)|^9 ≤ (36194487909943/100000000000000 : ℝ)^7
        have hw : |(907302047/2000000000 : ℝ)|=(907302047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-833328149/2500000000 : ℝ)|^9 ≤ (24353137060301/100000000000000 : ℝ)^7
        have hw : |(-833328149/2500000000 : ℝ)|=(833328149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2425518987/5000000000 : ℝ)|^9 ≤ (2465773438513/6250000000000 : ℝ)^7
        have hw : |(2425518987/5000000000 : ℝ)|=(2425518987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-361096629/5000000000 : ℝ)*x 0 + (-652120551/1000000000 : ℝ)*x 1 + (299750521/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361096629/5000000000 : ℝ)^9 ≤ (3408430239581/100000000000000 : ℝ)^7 := by
    have hnat : (361096629 : ℕ)^9*100000000000000^7 ≤ 3408430239581^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361096629 5000000000 3408430239581 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652120551/1000000000 : ℝ)^9 ≤ (57713672625323/100000000000000 : ℝ)^7 := by
    have hnat : (652120551 : ℕ)^9*100000000000000^7 ≤ 57713672625323^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652120551 1000000000 57713672625323 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299750521/625000000 : ℝ)^9 ≤ (19438948561421/50000000000000 : ℝ)^7 := by
    have hnat : (299750521 : ℕ)^9*50000000000000^7 ≤ 19438948561421^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299750521 625000000 19438948561421 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361096629/5000000000 : ℝ), (-652120551/1000000000 : ℝ), (299750521/625000000 : ℝ)] ![(3408430239581/100000000000000 : ℝ), (57713672625323/100000000000000 : ℝ), (19438948561421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361096629/5000000000 : ℝ)|^9 ≤ (3408430239581/100000000000000 : ℝ)^7
        have hw : |(-361096629/5000000000 : ℝ)|=(361096629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-652120551/1000000000 : ℝ)|^9 ≤ (57713672625323/100000000000000 : ℝ)^7
        have hw : |(-652120551/1000000000 : ℝ)|=(652120551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299750521/625000000 : ℝ)|^9 ≤ (19438948561421/50000000000000 : ℝ)^7
        have hw : |(299750521/625000000 : ℝ)|=(299750521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (734007389/1250000000 : ℝ)*x 0 + (3399942547/10000000000 : ℝ)*x 1 + (839475919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (734007389/1250000000 : ℝ)^9 ≤ (50434827351161/100000000000000 : ℝ)^7 := by
    have hnat : (734007389 : ℕ)^9*100000000000000^7 ≤ 50434827351161^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734007389 1250000000 50434827351161 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3399942547/10000000000 : ℝ)^9 ≤ (6245199605819/25000000000000 : ℝ)^7 := by
    have hnat : (3399942547 : ℕ)^9*25000000000000^7 ≤ 6245199605819^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3399942547 10000000000 6245199605819 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839475919/2500000000 : ℝ)^9 ≤ (24584374209907/100000000000000 : ℝ)^7 := by
    have hnat : (839475919 : ℕ)^9*100000000000000^7 ≤ 24584374209907^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839475919 2500000000 24584374209907 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(734007389/1250000000 : ℝ), (3399942547/10000000000 : ℝ), (839475919/2500000000 : ℝ)] ![(50434827351161/100000000000000 : ℝ), (6245199605819/25000000000000 : ℝ), (24584374209907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(734007389/1250000000 : ℝ)|^9 ≤ (50434827351161/100000000000000 : ℝ)^7
        have hw : |(734007389/1250000000 : ℝ)|=(734007389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3399942547/10000000000 : ℝ)|^9 ≤ (6245199605819/25000000000000 : ℝ)^7
        have hw : |(3399942547/10000000000 : ℝ)|=(3399942547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(839475919/2500000000 : ℝ)|^9 ≤ (24584374209907/100000000000000 : ℝ)^7
        have hw : |(839475919/2500000000 : ℝ)|=(839475919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1171655673/2000000000 : ℝ)*x 0 + (-1707592279/5000000000 : ℝ)*x 1 + (-839689717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171655673/2000000000 : ℝ)^9 ≤ (6285337310101/12500000000000 : ℝ)^7 := by
    have hnat : (1171655673 : ℕ)^9*12500000000000^7 ≤ 6285337310101^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171655673 2000000000 6285337310101 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1707592279/5000000000 : ℝ)^9 ≤ (5024975387913/20000000000000 : ℝ)^7 := by
    have hnat : (1707592279 : ℕ)^9*20000000000000^7 ≤ 5024975387913^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707592279 5000000000 5024975387913 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839689717/2500000000 : ℝ)^9 ≤ (192128316883/781250000000 : ℝ)^7 := by
    have hnat : (839689717 : ℕ)^9*781250000000^7 ≤ 192128316883^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839689717 2500000000 192128316883 781250000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1171655673/2000000000 : ℝ), (-1707592279/5000000000 : ℝ), (-839689717/2500000000 : ℝ)] ![(6285337310101/12500000000000 : ℝ), (5024975387913/20000000000000 : ℝ), (192128316883/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1171655673/2000000000 : ℝ)|^9 ≤ (6285337310101/12500000000000 : ℝ)^7
        have hw : |(1171655673/2000000000 : ℝ)|=(1171655673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1707592279/5000000000 : ℝ)|^9 ≤ (5024975387913/20000000000000 : ℝ)^7
        have hw : |(-1707592279/5000000000 : ℝ)|=(1707592279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-839689717/2500000000 : ℝ)|^9 ≤ (192128316883/781250000000 : ℝ)^7
        have hw : |(-839689717/2500000000 : ℝ)|=(839689717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (886235641/2500000000 : ℝ)*x 0 + (-296242437/1250000000 : ℝ)*x 1 + (6540583201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886235641/2500000000 : ℝ)^9 ≤ (13179414667421/50000000000000 : ℝ)^7 := by
    have hnat : (886235641 : ℕ)^9*50000000000000^7 ≤ 13179414667421^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886235641 2500000000 13179414667421 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296242437/1250000000 : ℝ)^9 ≤ (15706910215251/100000000000000 : ℝ)^7 := by
    have hnat : (296242437 : ℕ)^9*100000000000000^7 ≤ 15706910215251^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296242437 1250000000 15706910215251 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6540583201/10000000000 : ℝ)^9 ≤ (57934260435067/100000000000000 : ℝ)^7 := by
    have hnat : (6540583201 : ℕ)^9*100000000000000^7 ≤ 57934260435067^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6540583201 10000000000 57934260435067 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(886235641/2500000000 : ℝ), (-296242437/1250000000 : ℝ), (6540583201/10000000000 : ℝ)] ![(13179414667421/50000000000000 : ℝ), (15706910215251/100000000000000 : ℝ), (57934260435067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(886235641/2500000000 : ℝ)|^9 ≤ (13179414667421/50000000000000 : ℝ)^7
        have hw : |(886235641/2500000000 : ℝ)|=(886235641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296242437/1250000000 : ℝ)|^9 ≤ (15706910215251/100000000000000 : ℝ)^7
        have hw : |(-296242437/1250000000 : ℝ)|=(296242437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6540583201/10000000000 : ℝ)|^9 ≤ (57934260435067/100000000000000 : ℝ)^7
        have hw : |(6540583201/10000000000 : ℝ)|=(6540583201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-341530789/10000000000 : ℝ)*x 0 + (-1397754661/2500000000 : ℝ)*x 1 + (5954390381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341530789/10000000000 : ℝ)^9 ≤ (162674632709/12500000000000 : ℝ)^7 := by
    have hnat : (341530789 : ℕ)^9*12500000000000^7 ≤ 162674632709^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341530789 10000000000 162674632709 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397754661/2500000000 : ℝ)^9 ≤ (47352781540431/100000000000000 : ℝ)^7 := by
    have hnat : (1397754661 : ℕ)^9*100000000000000^7 ≤ 47352781540431^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397754661 2500000000 47352781540431 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5954390381/10000000000 : ℝ)^9 ≤ (51345821379741/100000000000000 : ℝ)^7 := by
    have hnat : (5954390381 : ℕ)^9*100000000000000^7 ≤ 51345821379741^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954390381 10000000000 51345821379741 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341530789/10000000000 : ℝ), (-1397754661/2500000000 : ℝ), (5954390381/10000000000 : ℝ)] ![(162674632709/12500000000000 : ℝ), (47352781540431/100000000000000 : ℝ), (51345821379741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341530789/10000000000 : ℝ)|^9 ≤ (162674632709/12500000000000 : ℝ)^7
        have hw : |(-341530789/10000000000 : ℝ)|=(341530789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1397754661/2500000000 : ℝ)|^9 ≤ (47352781540431/100000000000000 : ℝ)^7
        have hw : |(-1397754661/2500000000 : ℝ)|=(1397754661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5954390381/10000000000 : ℝ)|^9 ≤ (51345821379741/100000000000000 : ℝ)^7
        have hw : |(5954390381/10000000000 : ℝ)|=(5954390381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (12875461/20000000 : ℝ)*x 0 + (3297520279/10000000000 : ℝ)*x 1 + (2772466587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12875461/20000000 : ℝ)^9 ≤ (28382785996573/50000000000000 : ℝ)^7 := by
    have hnat : (12875461 : ℕ)^9*50000000000000^7 ≤ 28382785996573^7*20000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12875461 20000000 28382785996573 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3297520279/10000000000 : ℝ)^9 ≤ (24017442167529/100000000000000 : ℝ)^7 := by
    have hnat : (3297520279 : ℕ)^9*100000000000000^7 ≤ 24017442167529^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3297520279 10000000000 24017442167529 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2772466587/10000000000 : ℝ)^9 ≤ (4804246454907/25000000000000 : ℝ)^7 := by
    have hnat : (2772466587 : ℕ)^9*25000000000000^7 ≤ 4804246454907^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772466587 10000000000 4804246454907 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12875461/20000000 : ℝ), (3297520279/10000000000 : ℝ), (2772466587/10000000000 : ℝ)] ![(28382785996573/50000000000000 : ℝ), (24017442167529/100000000000000 : ℝ), (4804246454907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12875461/20000000 : ℝ)|^9 ≤ (28382785996573/50000000000000 : ℝ)^7
        have hw : |(12875461/20000000 : ℝ)|=(12875461/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3297520279/10000000000 : ℝ)|^9 ≤ (24017442167529/100000000000000 : ℝ)^7
        have hw : |(3297520279/10000000000 : ℝ)|=(3297520279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2772466587/10000000000 : ℝ)|^9 ≤ (4804246454907/25000000000000 : ℝ)^7
        have hw : |(2772466587/10000000000 : ℝ)|=(2772466587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1491554647/2500000000 : ℝ)*x 0 + (-1831159233/5000000000 : ℝ)*x 1 + (-2974598699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1491554647/2500000000 : ℝ)^9 ≤ (1029539947427/2000000000000 : ℝ)^7 := by
    have hnat : (1491554647 : ℕ)^9*2000000000000^7 ≤ 1029539947427^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491554647 2500000000 1029539947427 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831159233/5000000000 : ℝ)^9 ≤ (6871554622457/25000000000000 : ℝ)^7 := by
    have hnat : (1831159233 : ℕ)^9*25000000000000^7 ≤ 6871554622457^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831159233 5000000000 6871554622457 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2974598699/10000000000 : ℝ)^9 ≤ (657399504029/3125000000000 : ℝ)^7 := by
    have hnat : (2974598699 : ℕ)^9*3125000000000^7 ≤ 657399504029^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974598699 10000000000 657399504029 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1491554647/2500000000 : ℝ), (-1831159233/5000000000 : ℝ), (-2974598699/10000000000 : ℝ)] ![(1029539947427/2000000000000 : ℝ), (6871554622457/25000000000000 : ℝ), (657399504029/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1491554647/2500000000 : ℝ)|^9 ≤ (1029539947427/2000000000000 : ℝ)^7
        have hw : |(1491554647/2500000000 : ℝ)|=(1491554647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1831159233/5000000000 : ℝ)|^9 ≤ (6871554622457/25000000000000 : ℝ)^7
        have hw : |(-1831159233/5000000000 : ℝ)|=(1831159233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2974598699/10000000000 : ℝ)|^9 ≤ (657399504029/3125000000000 : ℝ)^7
        have hw : |(-2974598699/10000000000 : ℝ)|=(2974598699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3721195531/10000000000 : ℝ)*x 0 + (-2734562133/10000000000 : ℝ)*x 1 + (1221767877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3721195531/10000000000 : ℝ)^9 ≤ (28055650659681/100000000000000 : ℝ)^7 := by
    have hnat : (3721195531 : ℕ)^9*100000000000000^7 ≤ 28055650659681^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721195531 10000000000 28055650659681 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734562133/10000000000 : ℝ)^9 ≤ (18879852382849/100000000000000 : ℝ)^7 := by
    have hnat : (2734562133 : ℕ)^9*100000000000000^7 ≤ 18879852382849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734562133 10000000000 18879852382849 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221767877/2000000000 : ℝ)^9 ≤ (6633062118783/12500000000000 : ℝ)^7 := by
    have hnat : (1221767877 : ℕ)^9*12500000000000^7 ≤ 6633062118783^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221767877 2000000000 6633062118783 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3721195531/10000000000 : ℝ), (-2734562133/10000000000 : ℝ), (1221767877/2000000000 : ℝ)] ![(28055650659681/100000000000000 : ℝ), (18879852382849/100000000000000 : ℝ), (6633062118783/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3721195531/10000000000 : ℝ)|^9 ≤ (28055650659681/100000000000000 : ℝ)^7
        have hw : |(3721195531/10000000000 : ℝ)|=(3721195531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2734562133/10000000000 : ℝ)|^9 ≤ (18879852382849/100000000000000 : ℝ)^7
        have hw : |(-2734562133/10000000000 : ℝ)|=(2734562133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1221767877/2000000000 : ℝ)|^9 ≤ (6633062118783/12500000000000 : ℝ)^7
        have hw : |(1221767877/2000000000 : ℝ)|=(1221767877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-141289231/5000000000 : ℝ)*x 0 + (-6273596347/10000000000 : ℝ)*x 1 + (2643503683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141289231/5000000000 : ℝ)^9 ≤ (2040033761/200000000000 : ℝ)^7 := by
    have hnat : (141289231 : ℕ)^9*200000000000^7 ≤ 2040033761^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141289231 5000000000 2040033761 200000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6273596347/10000000000 : ℝ)^9 ≤ (54911608324941/100000000000000 : ℝ)^7 := by
    have hnat : (6273596347 : ℕ)^9*100000000000000^7 ≤ 54911608324941^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6273596347 10000000000 54911608324941 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2643503683/5000000000 : ℝ)^9 ≤ (44068374774467/100000000000000 : ℝ)^7 := by
    have hnat : (2643503683 : ℕ)^9*100000000000000^7 ≤ 44068374774467^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643503683 5000000000 44068374774467 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-141289231/5000000000 : ℝ), (-6273596347/10000000000 : ℝ), (2643503683/5000000000 : ℝ)] ![(2040033761/200000000000 : ℝ), (54911608324941/100000000000000 : ℝ), (44068374774467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-141289231/5000000000 : ℝ)|^9 ≤ (2040033761/200000000000 : ℝ)^7
        have hw : |(-141289231/5000000000 : ℝ)|=(141289231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6273596347/10000000000 : ℝ)|^9 ≤ (54911608324941/100000000000000 : ℝ)^7
        have hw : |(-6273596347/10000000000 : ℝ)|=(6273596347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2643503683/5000000000 : ℝ)|^9 ≤ (44068374774467/100000000000000 : ℝ)^7
        have hw : |(2643503683/5000000000 : ℝ)|=(2643503683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (81208551/125000000 : ℝ)*x 0 + (615563031/2000000000 : ℝ)*x 1 + (731205983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81208551/125000000 : ℝ)^9 ≤ (3589674934351/6250000000000 : ℝ)^7 := by
    have hnat : (81208551 : ℕ)^9*6250000000000^7 ≤ 3589674934351^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81208551 125000000 3589674934351 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615563031/2000000000 : ℝ)^9 ≤ (21979920376673/100000000000000 : ℝ)^7 := by
    have hnat : (615563031 : ℕ)^9*100000000000000^7 ≤ 21979920376673^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615563031 2000000000 21979920376673 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731205983/2500000000 : ℝ)^9 ≤ (5146320166343/25000000000000 : ℝ)^7 := by
    have hnat : (731205983 : ℕ)^9*25000000000000^7 ≤ 5146320166343^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731205983 2500000000 5146320166343 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81208551/125000000 : ℝ), (615563031/2000000000 : ℝ), (731205983/2500000000 : ℝ)] ![(3589674934351/6250000000000 : ℝ), (21979920376673/100000000000000 : ℝ), (5146320166343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81208551/125000000 : ℝ)|^9 ≤ (3589674934351/6250000000000 : ℝ)^7
        have hw : |(81208551/125000000 : ℝ)|=(81208551/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615563031/2000000000 : ℝ)|^9 ≤ (21979920376673/100000000000000 : ℝ)^7
        have hw : |(615563031/2000000000 : ℝ)|=(615563031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(731205983/2500000000 : ℝ)|^9 ≤ (5146320166343/25000000000000 : ℝ)^7
        have hw : |(731205983/2500000000 : ℝ)|=(731205983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2716783351/5000000000 : ℝ)*x 0 + (-149492489/400000000 : ℝ)*x 1 + (-1761164363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716783351/5000000000 : ℝ)^9 ≤ (45645188360651/100000000000000 : ℝ)^7 := by
    have hnat : (2716783351 : ℕ)^9*100000000000000^7 ≤ 45645188360651^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716783351 5000000000 45645188360651 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149492489/400000000 : ℝ)^9 ≤ (2821197500989/10000000000000 : ℝ)^7 := by
    have hnat : (149492489 : ℕ)^9*10000000000000^7 ≤ 2821197500989^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149492489 400000000 2821197500989 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761164363/5000000000 : ℝ)^9 ≤ (26142836621719/100000000000000 : ℝ)^7 := by
    have hnat : (1761164363 : ℕ)^9*100000000000000^7 ≤ 26142836621719^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761164363 5000000000 26142836621719 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716783351/5000000000 : ℝ), (-149492489/400000000 : ℝ), (-1761164363/5000000000 : ℝ)] ![(45645188360651/100000000000000 : ℝ), (2821197500989/10000000000000 : ℝ), (26142836621719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716783351/5000000000 : ℝ)|^9 ≤ (45645188360651/100000000000000 : ℝ)^7
        have hw : |(2716783351/5000000000 : ℝ)|=(2716783351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149492489/400000000 : ℝ)|^9 ≤ (2821197500989/10000000000000 : ℝ)^7
        have hw : |(-149492489/400000000 : ℝ)|=(149492489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761164363/5000000000 : ℝ)|^9 ≤ (26142836621719/100000000000000 : ℝ)^7
        have hw : |(-1761164363/5000000000 : ℝ)|=(1761164363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311086_s2_s2_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (49393507/100000000 : ℝ)*x 0 + (-734052777/2500000000 : ℝ)*x 1 + (4801334589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49393507/100000000 : ℝ)^9 ≤ (40378201068417/100000000000000 : ℝ)^7 := by
    have hnat : (49393507 : ℕ)^9*100000000000000^7 ≤ 40378201068417^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49393507 100000000 40378201068417 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (734052777/2500000000 : ℝ)^9 ≤ (10344190351593/50000000000000 : ℝ)^7 := by
    have hnat : (734052777 : ℕ)^9*50000000000000^7 ≤ 10344190351593^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734052777 2500000000 10344190351593 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4801334589/10000000000 : ℝ)^9 ≤ (38933418211851/100000000000000 : ℝ)^7 := by
    have hnat : (4801334589 : ℕ)^9*100000000000000^7 ≤ 38933418211851^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801334589 10000000000 38933418211851 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(49393507/100000000 : ℝ), (-734052777/2500000000 : ℝ), (4801334589/10000000000 : ℝ)] ![(40378201068417/100000000000000 : ℝ), (10344190351593/50000000000000 : ℝ), (38933418211851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(49393507/100000000 : ℝ)|^9 ≤ (40378201068417/100000000000000 : ℝ)^7
        have hw : |(49393507/100000000 : ℝ)|=(49393507/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-734052777/2500000000 : ℝ)|^9 ≤ (10344190351593/50000000000000 : ℝ)^7
        have hw : |(-734052777/2500000000 : ℝ)|=(734052777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4801334589/10000000000 : ℝ)|^9 ≤ (38933418211851/100000000000000 : ℝ)^7
        have hw : |(4801334589/10000000000 : ℝ)|=(4801334589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311086_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((49129/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49129/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-71403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-71403/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68943/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6193/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6193/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8071/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8071/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6421/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6421/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (49129/100000 : ℝ) ^ (71/16 : ℝ) ≤ (4268861250368779579/100000000000000000000 : ℝ) := by
    have hpowers : (49129/100000 : ℝ)^71 ≤ (4268861250368779579/100000000000000000000 : ℝ)^16 := by
      have hnat : (49129 : ℕ)^71*100000000000000000000^16 ≤ 4268861250368779579^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49129 100000 4268861250368779579 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (49129/100000 : ℝ)) (X := (4268861250368779579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (104268861250368779579/100000000000000000000 : ℝ) ≤ (10094648107618513/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (104268861250368779579/100000000000000000000 : ℝ)^16 ≤ (10094648107618513/10000000000000000 : ℝ)^71 := by
      have hnat : (104268861250368779579 : ℕ)^16*10000000000000000^71 ≤ 10094648107618513^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104268861250368779579 100000000000000000000 10094648107618513 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10094648107618513/10000000000000000 : ℝ)) (X := (104268861250368779579/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (54268861250368779579/50000000000000000000 : ℝ) ≤ (10186340443604803/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (54268861250368779579/50000000000000000000 : ℝ)^16 ≤ (10186340443604803/10000000000000000 : ℝ)^71 := by
      have hnat : (54268861250368779579 : ℕ)^16*10000000000000000^71 ≤ 10186340443604803^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54268861250368779579 50000000000000000000 10186340443604803 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10186340443604803/10000000000000000 : ℝ)) (X := (54268861250368779579/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(94648107618513/4912900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(9169233598629/491290000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (49129/100000 : ℝ)) (alpha := (94648107618513/4912900000000000 : ℝ)) (beta := (9169233598629/491290000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (49129/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(94648107618513/4912900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(9169233598629/491290000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (71403/100000 : ℝ) ^ (71/16 : ℝ) ≤ (11215968771306836943/50000000000000000000 : ℝ) := by
    have hpowers : (71403/100000 : ℝ)^71 ≤ (11215968771306836943/50000000000000000000 : ℝ)^16 := by
      have hnat : (71403 : ℕ)^71*50000000000000000000^16 ≤ 11215968771306836943^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71403 100000 11215968771306836943 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71403/100000 : ℝ)) (X := (11215968771306836943/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (61215968771306836943/50000000000000000000 : ℝ) ≤ (10466639386168027/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (61215968771306836943/50000000000000000000 : ℝ)^16 ≤ (10466639386168027/10000000000000000 : ℝ)^71 := by
      have hnat : (61215968771306836943 : ℕ)^16*10000000000000000^71 ≤ 10466639386168027^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61215968771306836943 50000000000000000000 10466639386168027 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10466639386168027/10000000000000000 : ℝ)) (X := (61215968771306836943/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (36215968771306836943/25000000000000000000 : ℝ) ≤ (10871080162655593/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (36215968771306836943/25000000000000000000 : ℝ)^16 ≤ (10871080162655593/10000000000000000 : ℝ)^71 := by
      have hnat : (36215968771306836943 : ℕ)^16*10000000000000000^71 ≤ 10871080162655593^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36215968771306836943 25000000000000000000 10871080162655593 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10871080162655593/10000000000000000 : ℝ)) (X := (36215968771306836943/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(155546462056009/2380100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(67406796081261/1190050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (71403/100000 : ℝ)) (alpha := (155546462056009/2380100000000000 : ℝ)) (beta := (67406796081261/1190050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (71403/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(155546462056009/2380100000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(67406796081261/1190050000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (68943/100000 : ℝ) ^ (71/16 : ℝ) ≤ (2399994107911170043/12500000000000000000 : ℝ) := by
    have hpowers : (68943/100000 : ℝ)^71 ≤ (2399994107911170043/12500000000000000000 : ℝ)^16 := by
      have hnat : (68943 : ℕ)^71*12500000000000000000^16 ≤ 2399994107911170043^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68943 100000 2399994107911170043 12500000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68943/100000 : ℝ)) (X := (2399994107911170043/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (14899994107911170043/12500000000000000000 : ℝ) ≤ (10403727696470717/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (14899994107911170043/12500000000000000000 : ℝ)^16 ≤ (10403727696470717/10000000000000000 : ℝ)^71 := by
      have hnat : (14899994107911170043 : ℕ)^16*10000000000000000^71 ≤ 10403727696470717^71*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14899994107911170043 12500000000000000000 10403727696470717 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10403727696470717/10000000000000000 : ℝ)) (X := (14899994107911170043/12500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (8649994107911170043/6250000000000000000 : ℝ) ≤ (10759826027808661/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (8649994107911170043/6250000000000000000 : ℝ)^16 ≤ (10759826027808661/10000000000000000 : ℝ)^71 := by
      have hnat : (8649994107911170043 : ℕ)^16*10000000000000000^71 ≤ 10759826027808661^71*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8649994107911170043 6250000000000000000 10759826027808661 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10759826027808661/10000000000000000 : ℝ)) (X := (8649994107911170043/6250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(403727696470717/6894300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(44512291417243/861787500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (68943/100000 : ℝ)) (alpha := (403727696470717/6894300000000000 : ℝ)) (beta := (44512291417243/861787500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (68943/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(403727696470717/6894300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(44512291417243/861787500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-421591451/5000000000 : ℝ)*X 0 0+(-1442496551/2500000000 : ℝ)*X 0 1+(5515316099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5589984131/10000000000 : ℝ)*X 2 0+(-1825071493/5000000000 : ℝ)*X 2 1+(-3432596889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((907302047/2000000000 : ℝ)*X 0 0+(-833328149/2500000000 : ℝ)*X 0 1+(2425518987/5000000000 : ℝ)*X 0 2+(907302047/2000000000 : ℝ)*X 1 0+(-833328149/2500000000 : ℝ)*X 1 1+(2425518987/5000000000 : ℝ)*X 1 2+(907302047/2000000000 : ℝ)*X 2 0+(-833328149/2500000000 : ℝ)*X 2 1+(2425518987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-361096629/5000000000 : ℝ)*X 0 0+(-652120551/1000000000 : ℝ)*X 0 1+(299750521/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((734007389/1250000000 : ℝ)*X 1 0+(3399942547/10000000000 : ℝ)*X 1 1+(839475919/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1171655673/2000000000 : ℝ)*X 2 0+(-1707592279/5000000000 : ℝ)*X 2 1+(-839689717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((886235641/2500000000 : ℝ)*X 0 0+(-296242437/1250000000 : ℝ)*X 0 1+(6540583201/10000000000 : ℝ)*X 0 2+(886235641/2500000000 : ℝ)*X 1 0+(-296242437/1250000000 : ℝ)*X 1 1+(6540583201/10000000000 : ℝ)*X 1 2+(886235641/2500000000 : ℝ)*X 2 0+(-296242437/1250000000 : ℝ)*X 2 1+(6540583201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-341530789/10000000000 : ℝ)*X 0 0+(-1397754661/2500000000 : ℝ)*X 0 1+(5954390381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((12875461/20000000 : ℝ)*X 1 0+(3297520279/10000000000 : ℝ)*X 1 1+(2772466587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1491554647/2500000000 : ℝ)*X 2 0+(-1831159233/5000000000 : ℝ)*X 2 1+(-2974598699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3721195531/10000000000 : ℝ)*X 0 0+(-2734562133/10000000000 : ℝ)*X 0 1+(1221767877/2000000000 : ℝ)*X 0 2+(3721195531/10000000000 : ℝ)*X 1 0+(-2734562133/10000000000 : ℝ)*X 1 1+(1221767877/2000000000 : ℝ)*X 1 2+(3721195531/10000000000 : ℝ)*X 2 0+(-2734562133/10000000000 : ℝ)*X 2 1+(1221767877/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-141289231/5000000000 : ℝ)*X 0 0+(-6273596347/10000000000 : ℝ)*X 0 1+(2643503683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((81208551/125000000 : ℝ)*X 1 0+(615563031/2000000000 : ℝ)*X 1 1+(731205983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2716783351/5000000000 : ℝ)*X 2 0+(-149492489/400000000 : ℝ)*X 2 1+(-1761164363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((49393507/100000000 : ℝ)*X 0 0+(-734052777/2500000000 : ℝ)*X 0 1+(4801334589/10000000000 : ℝ)*X 0 2+(49393507/100000000 : ℝ)*X 1 0+(-734052777/2500000000 : ℝ)*X 1 1+(4801334589/10000000000 : ℝ)*X 1 2+(49393507/100000000 : ℝ)*X 2 0+(-734052777/2500000000 : ℝ)*X 2 1+(4801334589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((6193/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6193/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45635341620669823913839541091/3359015937468625000000000000000000 : ℝ) := by norm_num
    linear_combination (738106099637/1000000000000 : ℝ)*(base40) + (100279/40000000000 : ℝ)*(base50) + (1167683/200000000000 : ℝ)*(base60) + (481075686279/100000000000 : ℝ)*(major_s2_0) + (481075686279/100000000000 : ℝ)*(major_s2_1) + (481075686279/100000000000 : ℝ)*(major_s2_2) + (13496243/1000000000000 : ℝ)*(sp_s2_0) + (67035273/200000000000 : ℝ)*(sp_s2_2) + (3347122818869/500000000000 : ℝ)*(sp_s2_7) + (6694332192779/1000000000000 : ℝ)*(sp_s2_8) + (836742758399/125000000000 : ℝ)*(sp_s2_9) + (731794251039/250000000000 : ℝ)*(sp_s2_13) + (27474611/500000000000 : ℝ)*(sp_s2_16) + (36529399/500000000000 : ℝ)*(sp_s2_21) + (731794251039/250000000000 : ℝ)*(f.failure) + (6694332192779/1000000000000 : ℝ)*(f.sum) + (1578352555983384399/5469707810000000000000000000000 : ℝ)*base62 + (13110401432381/114905000000000000000000000 : ℝ)*base65 + (51629832962431/119005000000000000000000000 : ℝ)*base67 + (71803551511089/229810000000000000000000000 : ℝ)*base69 + (268034742791701903/5645167745000000000000000000000 : ℝ)*base71 + (14900454154907/49129000000000000000000000 : ℝ)*base73 + (78373540640777/238010000000000000000000000 : ℝ)*base74 + (181064967335707/491290000000000000000000000 : ℝ)*base76 + (389644817025536041/730824580625000000000000000000 : ℝ)*base79 + (1893/6250000000000000 : ℝ)*base87 + (1893/6250000000000000 : ℝ)*base89 + (1893/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-8071/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8071/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (105548647012167650418858528297/16795079687343125000000000000000000 : ℝ) := by norm_num
    linear_combination (641623/125000000000 : ℝ)*(base39) + (967828038669/500000000000 : ℝ)*(base40) + (236042386027/500000000000 : ℝ)*(base60) + (463228087221/62500000000 : ℝ)*(major_s2_0) + (463228087221/62500000000 : ℝ)*(major_s2_1) + (463228087221/62500000000 : ℝ)*(major_s2_2) + (22039471/1000000000000 : ℝ)*(sp_s2_0) + (130738159/1000000000000 : ℝ)*(sp_s2_13) + (1289193208721/125000000000 : ℝ)*(sp_s2_14) + (5156723438249/500000000000 : ℝ)*(sp_s2_15) + (10313567709239/1000000000000 : ℝ)*(sp_s2_16) + (2254782819653/500000000000 : ℝ)*(sp_s2_20) + (60416371/500000000000 : ℝ)*(sp_s2_22) + (1304381/40000000000 : ℝ)*(sp_s2_27) + (4509728986989/1000000000000 : ℝ)*(f.failure) + (10313567709239/1000000000000 : ℝ)*(f.sum) + (3722988711889638603/6837134762500000000000000000000 : ℝ)*base62 + (453177930763113/574525000000000000000000000 : ℝ)*base65 + (1351589638897243/1190050000000000000000000000 : ℝ)*base66 + (929345620958179/574525000000000000000000000 : ℝ)*base68 + (1907083681486077701/28225838725000000000000000000000 : ℝ)*base70 + (107812541823789/61411250000000000000000000 : ℝ)*base72 + (573954751200537/595025000000000000000000000 : ℝ)*base74 + (425514629954801/614112500000000000000000000 : ℝ)*base77 + (60719683279032489417/58465966450000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (17043/25000000000000000 : ℝ)*base87 + (17043/25000000000000000 : ℝ)*base89 + (17043/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6421/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6421/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (419413443874666861567412005273/83975398436715625000000000000000000 : ℝ) := by norm_num
    linear_combination (31689/62500000000 : ℝ)*(base39) + (965687100851/500000000000 : ℝ)*(base40) + (846149/1000000000000 : ℝ)*(base50) + (6848442317897/1000000000000 : ℝ)*(major_s2_0) + (6848442317897/1000000000000 : ℝ)*(major_s2_1) + (6848442317897/1000000000000 : ℝ)*(major_s2_2) + (19783051/1000000000000 : ℝ)*(sp_s2_2) + (665519/50000000000 : ℝ)*(sp_s2_6) + (3517893/100000000000 : ℝ)*(sp_s2_7) + (2110977/31250000000 : ℝ)*(sp_s2_15) + (1905962115919/200000000000 : ℝ)*(sp_s2_21) + (9529778207261/1000000000000 : ℝ)*(sp_s2_22) + (9529825975473/1000000000000 : ℝ)*(sp_s2_23) + (2083511951029/500000000000 : ℝ)*(sp_s2_27) + (2083518606219/500000000000 : ℝ)*(f.failure) + (381193830341/40000000000 : ℝ)*(f.sum) + (85125427521531921089/164091234300000000000000000000000 : ℝ)*base62 + (1670576755018051/3447150000000000000000000000 : ℝ)*base65 + (143153526638247/2380100000000000000000000000 : ℝ)*base66 + (3545453778713251/6894300000000000000000000000 : ℝ)*base68 + (69641229629636271739/338710064700000000000000000000000 : ℝ)*base70 + (42443003171909/98258000000000000000000000 : ℝ)*base72 + (200739966851509/595025000000000000000000000 : ℝ)*base74 + (933041071775889/4912900000000000000000000000 : ℝ)*base76 + (323240419834953503/116931932900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (7553/12500000000000000 : ℝ)*base87 + (7553/12500000000000000 : ℝ)*base89 + (7553/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((49129/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49129/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-71403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-71403/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68943/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6193/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6193/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8071/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8071/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6421/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6421/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311086_s2 p hpa hpb X hX hprev1

#print axioms solution

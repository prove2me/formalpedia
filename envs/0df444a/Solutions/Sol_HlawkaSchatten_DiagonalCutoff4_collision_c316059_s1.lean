-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316059_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:20.639682+00:00
-- url     : https://prove2.me/submissions/7b70814d-a55e-4127-b46c-d12fc83eb454

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
theorem collision_support_c316059_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (99745427/312500000 : ℝ)*x 0 + (-159338867/500000000 : ℝ)*x 1 + (6023340483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99745427/312500000 : ℝ)^77 ≤ (591419842883/2500000000000 : ℝ)^61 := by
    have hnat : (99745427 : ℕ)^77*2500000000000^61 ≤ 591419842883^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99745427 312500000 591419842883 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159338867/500000000 : ℝ)^77 ≤ (472186226649/2000000000000 : ℝ)^61 := by
    have hnat : (159338867 : ℕ)^77*2000000000000^61 ≤ 472186226649^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159338867 500000000 472186226649 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6023340483/10000000000 : ℝ)^77 ≤ (3295868433809/6250000000000 : ℝ)^61 := by
    have hnat : (6023340483 : ℕ)^77*6250000000000^61 ≤ 3295868433809^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6023340483 10000000000 3295868433809 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99745427/312500000 : ℝ), (-159338867/500000000 : ℝ), (6023340483/10000000000 : ℝ)] ![(591419842883/2500000000000 : ℝ), (472186226649/2000000000000 : ℝ), (3295868433809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99745427/312500000 : ℝ)|^77 ≤ (591419842883/2500000000000 : ℝ)^61
        have hw : |(99745427/312500000 : ℝ)|=(99745427/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159338867/500000000 : ℝ)|^77 ≤ (472186226649/2000000000000 : ℝ)^61
        have hw : |(-159338867/500000000 : ℝ)|=(159338867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6023340483/10000000000 : ℝ)|^77 ≤ (3295868433809/6250000000000 : ℝ)^61
        have hw : |(6023340483/10000000000 : ℝ)|=(6023340483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2966956421/5000000000 : ℝ)*x 0 + (5425475161/10000000000 : ℝ)*x 1 + (-457575983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2966956421/5000000000 : ℝ)^77 ≤ (404277615227/781250000000 : ℝ)^61 := by
    have hnat : (2966956421 : ℕ)^77*781250000000^61 ≤ 404277615227^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966956421 5000000000 404277615227 781250000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425475161/10000000000 : ℝ)^77 ≤ (4621491037493/10000000000000 : ℝ)^61 := by
    have hnat : (5425475161 : ℕ)^77*10000000000000^61 ≤ 4621491037493^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425475161 10000000000 4621491037493 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457575983/10000000000 : ℝ)^77 ≤ (31836794799/1562500000000 : ℝ)^61 := by
    have hnat : (457575983 : ℕ)^77*1562500000000^61 ≤ 31836794799^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457575983 10000000000 31836794799 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2966956421/5000000000 : ℝ), (5425475161/10000000000 : ℝ), (-457575983/10000000000 : ℝ)] ![(404277615227/781250000000 : ℝ), (4621491037493/10000000000000 : ℝ), (31836794799/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2966956421/5000000000 : ℝ)|^77 ≤ (404277615227/781250000000 : ℝ)^61
        have hw : |(2966956421/5000000000 : ℝ)|=(2966956421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425475161/10000000000 : ℝ)|^77 ≤ (4621491037493/10000000000000 : ℝ)^61
        have hw : |(5425475161/10000000000 : ℝ)|=(5425475161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457575983/10000000000 : ℝ)|^77 ≤ (31836794799/1562500000000 : ℝ)^61
        have hw : |(-457575983/10000000000 : ℝ)|=(457575983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1939503493/5000000000 : ℝ)*x 0 + (2603431497/5000000000 : ℝ)*x 1 + (3425663637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939503493/5000000000 : ℝ)^77 ≤ (48413220177/160000000000 : ℝ)^61 := by
    have hnat : (1939503493 : ℕ)^77*160000000000^61 ≤ 48413220177^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939503493 5000000000 48413220177 160000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603431497/5000000000 : ℝ)^77 ≤ (43876852762183/100000000000000 : ℝ)^61 := by
    have hnat : (2603431497 : ℕ)^77*100000000000000^61 ≤ 43876852762183^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603431497 5000000000 43876852762183 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3425663637/10000000000 : ℝ)^77 ≤ (25864884613957/100000000000000 : ℝ)^61 := by
    have hnat : (3425663637 : ℕ)^77*100000000000000^61 ≤ 25864884613957^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3425663637 10000000000 25864884613957 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1939503493/5000000000 : ℝ), (2603431497/5000000000 : ℝ), (3425663637/10000000000 : ℝ)] ![(48413220177/160000000000 : ℝ), (43876852762183/100000000000000 : ℝ), (25864884613957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1939503493/5000000000 : ℝ)|^77 ≤ (48413220177/160000000000 : ℝ)^61
        have hw : |(1939503493/5000000000 : ℝ)|=(1939503493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603431497/5000000000 : ℝ)|^77 ≤ (43876852762183/100000000000000 : ℝ)^61
        have hw : |(2603431497/5000000000 : ℝ)|=(2603431497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3425663637/10000000000 : ℝ)|^77 ≤ (25864884613957/100000000000000 : ℝ)^61
        have hw : |(3425663637/10000000000 : ℝ)|=(3425663637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3004007407/10000000000 : ℝ)*x 0 + (2787507747/10000000000 : ℝ)*x 1 + (406764479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3004007407/10000000000 : ℝ)^77 ≤ (21913136294251/100000000000000 : ℝ)^61 := by
    have hnat : (3004007407 : ℕ)^77*100000000000000^61 ≤ 21913136294251^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004007407 10000000000 21913136294251 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787507747/10000000000 : ℝ)^77 ≤ (19938798758491/100000000000000 : ℝ)^61 := by
    have hnat : (2787507747 : ℕ)^77*100000000000000^61 ≤ 19938798758491^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787507747 10000000000 19938798758491 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406764479/625000000 : ℝ)^77 ≤ (58148064927441/100000000000000 : ℝ)^61 := by
    have hnat : (406764479 : ℕ)^77*100000000000000^61 ≤ 58148064927441^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406764479 625000000 58148064927441 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3004007407/10000000000 : ℝ), (2787507747/10000000000 : ℝ), (406764479/625000000 : ℝ)] ![(21913136294251/100000000000000 : ℝ), (19938798758491/100000000000000 : ℝ), (58148064927441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3004007407/10000000000 : ℝ)|^77 ≤ (21913136294251/100000000000000 : ℝ)^61
        have hw : |(-3004007407/10000000000 : ℝ)|=(3004007407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787507747/10000000000 : ℝ)|^77 ≤ (19938798758491/100000000000000 : ℝ)^61
        have hw : |(2787507747/10000000000 : ℝ)|=(2787507747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(406764479/625000000 : ℝ)|^77 ≤ (58148064927441/100000000000000 : ℝ)^61
        have hw : |(406764479/625000000 : ℝ)|=(406764479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1511046389/5000000000 : ℝ)*x 0 + (-2761174479/10000000000 : ℝ)*x 1 + (1302901873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1511046389/5000000000 : ℝ)^77 ≤ (176638378757/800000000000 : ℝ)^61 := by
    have hnat : (1511046389 : ℕ)^77*800000000000^61 ≤ 176638378757^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511046389 5000000000 176638378757 800000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761174479/10000000000 : ℝ)^77 ≤ (19701328676043/100000000000000 : ℝ)^61 := by
    have hnat : (2761174479 : ℕ)^77*100000000000000^61 ≤ 19701328676043^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761174479 10000000000 19701328676043 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302901873/2000000000 : ℝ)^77 ≤ (58218873966869/100000000000000 : ℝ)^61 := by
    have hnat : (1302901873 : ℕ)^77*100000000000000^61 ≤ 58218873966869^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302901873 2000000000 58218873966869 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1511046389/5000000000 : ℝ), (-2761174479/10000000000 : ℝ), (1302901873/2000000000 : ℝ)] ![(176638378757/800000000000 : ℝ), (19701328676043/100000000000000 : ℝ), (58218873966869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1511046389/5000000000 : ℝ)|^77 ≤ (176638378757/800000000000 : ℝ)^61
        have hw : |(1511046389/5000000000 : ℝ)|=(1511046389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2761174479/10000000000 : ℝ)|^77 ≤ (19701328676043/100000000000000 : ℝ)^61
        have hw : |(-2761174479/10000000000 : ℝ)|=(2761174479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1302901873/2000000000 : ℝ)|^77 ≤ (58218873966869/100000000000000 : ℝ)^61
        have hw : |(1302901873/2000000000 : ℝ)|=(1302901873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5710267103/10000000000 : ℝ)*x 0 + (2918575319/5000000000 : ℝ)*x 1 + (-2630491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5710267103/10000000000 : ℝ)^77 ≤ (3081120029217/6250000000000 : ℝ)^61 := by
    have hnat : (5710267103 : ℕ)^77*6250000000000^61 ≤ 3081120029217^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710267103 10000000000 3081120029217 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2918575319/5000000000 : ℝ)^77 ≤ (6335582644077/12500000000000 : ℝ)^61 := by
    have hnat : (2918575319 : ℕ)^77*12500000000000^61 ≤ 6335582644077^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2918575319 5000000000 6335582644077 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630491/2500000000 : ℝ)^77 ≤ (8709183779/50000000000000 : ℝ)^61 := by
    have hnat : (2630491 : ℕ)^77*50000000000000^61 ≤ 8709183779^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630491 2500000000 8709183779 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5710267103/10000000000 : ℝ), (2918575319/5000000000 : ℝ), (-2630491/2500000000 : ℝ)] ![(3081120029217/6250000000000 : ℝ), (6335582644077/12500000000000 : ℝ), (8709183779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5710267103/10000000000 : ℝ)|^77 ≤ (3081120029217/6250000000000 : ℝ)^61
        have hw : |(5710267103/10000000000 : ℝ)|=(5710267103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2918575319/5000000000 : ℝ)|^77 ≤ (6335582644077/12500000000000 : ℝ)^61
        have hw : |(2918575319/5000000000 : ℝ)|=(2918575319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2630491/2500000000 : ℝ)|^77 ≤ (8709183779/50000000000000 : ℝ)^61
        have hw : |(-2630491/2500000000 : ℝ)|=(2630491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3521335243/10000000000 : ℝ)*x 0 + (3236430621/5000000000 : ℝ)*x 1 + (1139960579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3521335243/10000000000 : ℝ)^77 ≤ (26780023061919/100000000000000 : ℝ)^61 := by
    have hnat : (3521335243 : ℕ)^77*100000000000000^61 ≤ 26780023061919^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3521335243 10000000000 26780023061919 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3236430621/5000000000 : ℝ)^77 ≤ (14437360258677/25000000000000 : ℝ)^61 := by
    have hnat : (3236430621 : ℕ)^77*25000000000000^61 ≤ 14437360258677^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3236430621 5000000000 14437360258677 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139960579/5000000000 : ℝ)^77 ≤ (1547053589539/10000000000000 : ℝ)^61 := by
    have hnat : (1139960579 : ℕ)^77*10000000000000^61 ≤ 1547053589539^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139960579 5000000000 1547053589539 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3521335243/10000000000 : ℝ), (3236430621/5000000000 : ℝ), (1139960579/5000000000 : ℝ)] ![(26780023061919/100000000000000 : ℝ), (14437360258677/25000000000000 : ℝ), (1547053589539/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3521335243/10000000000 : ℝ)|^77 ≤ (26780023061919/100000000000000 : ℝ)^61
        have hw : |(3521335243/10000000000 : ℝ)|=(3521335243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3236430621/5000000000 : ℝ)|^77 ≤ (14437360258677/25000000000000 : ℝ)^61
        have hw : |(3236430621/5000000000 : ℝ)|=(3236430621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139960579/5000000000 : ℝ)|^77 ≤ (1547053589539/10000000000000 : ℝ)^61
        have hw : |(1139960579/5000000000 : ℝ)|=(1139960579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2777683913/10000000000 : ℝ)*x 0 + (3015461333/10000000000 : ℝ)*x 1 + (1626684147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2777683913/10000000000 : ℝ)^77 ≤ (9925069773641/50000000000000 : ℝ)^61 := by
    have hnat : (2777683913 : ℕ)^77*50000000000000^61 ≤ 9925069773641^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777683913 10000000000 9925069773641 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015461333/10000000000 : ℝ)^77 ≤ (11009328260457/50000000000000 : ℝ)^61 := by
    have hnat : (3015461333 : ℕ)^77*50000000000000^61 ≤ 11009328260457^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015461333 10000000000 11009328260457 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1626684147/2500000000 : ℝ)^77 ≤ (29065601963529/50000000000000 : ℝ)^61 := by
    have hnat : (1626684147 : ℕ)^77*50000000000000^61 ≤ 29065601963529^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626684147 2500000000 29065601963529 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2777683913/10000000000 : ℝ), (3015461333/10000000000 : ℝ), (1626684147/2500000000 : ℝ)] ![(9925069773641/50000000000000 : ℝ), (11009328260457/50000000000000 : ℝ), (29065601963529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2777683913/10000000000 : ℝ)|^77 ≤ (9925069773641/50000000000000 : ℝ)^61
        have hw : |(-2777683913/10000000000 : ℝ)|=(2777683913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015461333/10000000000 : ℝ)|^77 ≤ (11009328260457/50000000000000 : ℝ)^61
        have hw : |(3015461333/10000000000 : ℝ)|=(3015461333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1626684147/2500000000 : ℝ)|^77 ≤ (29065601963529/50000000000000 : ℝ)^61
        have hw : |(1626684147/2500000000 : ℝ)|=(1626684147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2768378799/10000000000 : ℝ)*x 0 + (-15084421/50000000 : ℝ)*x 1 + (407063291/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2768378799/10000000000 : ℝ)^77 ≤ (154423730817/781250000000 : ℝ)^61 := by
    have hnat : (2768378799 : ℕ)^77*781250000000^61 ≤ 154423730817^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768378799 10000000000 154423730817 781250000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15084421/50000000 : ℝ)^77 ≤ (22031772149859/100000000000000 : ℝ)^61 := by
    have hnat : (15084421 : ℕ)^77*100000000000000^61 ≤ 22031772149859^61*50000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15084421 50000000 22031772149859 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407063291/625000000 : ℝ)^77 ≤ (58201990281041/100000000000000 : ℝ)^61 := by
    have hnat : (407063291 : ℕ)^77*100000000000000^61 ≤ 58201990281041^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407063291 625000000 58201990281041 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2768378799/10000000000 : ℝ), (-15084421/50000000 : ℝ), (407063291/625000000 : ℝ)] ![(154423730817/781250000000 : ℝ), (22031772149859/100000000000000 : ℝ), (58201990281041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2768378799/10000000000 : ℝ)|^77 ≤ (154423730817/781250000000 : ℝ)^61
        have hw : |(2768378799/10000000000 : ℝ)|=(2768378799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15084421/50000000 : ℝ)|^77 ≤ (22031772149859/100000000000000 : ℝ)^61
        have hw : |(-15084421/50000000 : ℝ)|=(15084421/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(407063291/625000000 : ℝ)|^77 ≤ (58201990281041/100000000000000 : ℝ)^61
        have hw : |(407063291/625000000 : ℝ)|=(407063291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3170129781/5000000000 : ℝ)*x 0 + (5192043371/10000000000 : ℝ)*x 1 + (-6008977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3170129781/5000000000 : ℝ)^77 ≤ (7032515530679/12500000000000 : ℝ)^61 := by
    have hnat : (3170129781 : ℕ)^77*12500000000000^61 ≤ 7032515530679^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170129781 5000000000 7032515530679 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192043371/10000000000 : ℝ)^77 ≤ (21859637466789/50000000000000 : ℝ)^61 := by
    have hnat : (5192043371 : ℕ)^77*50000000000000^61 ≤ 21859637466789^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192043371 10000000000 21859637466789 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008977/5000000000 : ℝ)^77 ≤ (10300408609/50000000000000 : ℝ)^61 := by
    have hnat : (6008977 : ℕ)^77*50000000000000^61 ≤ 10300408609^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008977 5000000000 10300408609 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3170129781/5000000000 : ℝ), (5192043371/10000000000 : ℝ), (-6008977/5000000000 : ℝ)] ![(7032515530679/12500000000000 : ℝ), (21859637466789/50000000000000 : ℝ), (10300408609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3170129781/5000000000 : ℝ)|^77 ≤ (7032515530679/12500000000000 : ℝ)^61
        have hw : |(3170129781/5000000000 : ℝ)|=(3170129781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192043371/10000000000 : ℝ)|^77 ≤ (21859637466789/50000000000000 : ℝ)^61
        have hw : |(5192043371/10000000000 : ℝ)|=(5192043371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6008977/5000000000 : ℝ)|^77 ≤ (10300408609/50000000000000 : ℝ)^61
        have hw : |(-6008977/5000000000 : ℝ)|=(6008977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2599522901/5000000000 : ℝ)*x 0 + (4906187339/10000000000 : ℝ)*x 1 + (2283728003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599522901/5000000000 : ℝ)^77 ≤ (21896858734111/50000000000000 : ℝ)^61 := by
    have hnat : (2599522901 : ℕ)^77*50000000000000^61 ≤ 21896858734111^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599522901 5000000000 21896858734111 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906187339/10000000000 : ℝ)^77 ≤ (40703132430457/100000000000000 : ℝ)^61 := by
    have hnat : (4906187339 : ℕ)^77*100000000000000^61 ≤ 40703132430457^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906187339 10000000000 40703132430457 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283728003/10000000000 : ℝ)^77 ≤ (15503150090581/100000000000000 : ℝ)^61 := by
    have hnat : (2283728003 : ℕ)^77*100000000000000^61 ≤ 15503150090581^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283728003 10000000000 15503150090581 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599522901/5000000000 : ℝ), (4906187339/10000000000 : ℝ), (2283728003/10000000000 : ℝ)] ![(21896858734111/50000000000000 : ℝ), (40703132430457/100000000000000 : ℝ), (15503150090581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599522901/5000000000 : ℝ)|^77 ≤ (21896858734111/50000000000000 : ℝ)^61
        have hw : |(2599522901/5000000000 : ℝ)|=(2599522901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906187339/10000000000 : ℝ)|^77 ≤ (40703132430457/100000000000000 : ℝ)^61
        have hw : |(4906187339/10000000000 : ℝ)|=(4906187339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2283728003/10000000000 : ℝ)|^77 ≤ (15503150090581/100000000000000 : ℝ)^61
        have hw : |(2283728003/10000000000 : ℝ)|=(2283728003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-100175259/312500000 : ℝ)*x 0 + (1615172011/5000000000 : ℝ)*x 1 + (5974705591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100175259/312500000 : ℝ)^77 ≤ (1486596860201/6250000000000 : ℝ)^61 := by
    have hnat : (100175259 : ℕ)^77*6250000000000^61 ≤ 1486596860201^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100175259 312500000 1486596860201 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615172011/5000000000 : ℝ)^77 ≤ (6004365929397/25000000000000 : ℝ)^61 := by
    have hnat : (1615172011 : ℕ)^77*25000000000000^61 ≤ 6004365929397^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615172011 5000000000 6004365929397 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5974705591/10000000000 : ℝ)^77 ≤ (52196986501917/100000000000000 : ℝ)^61 := by
    have hnat : (5974705591 : ℕ)^77*100000000000000^61 ≤ 52196986501917^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974705591 10000000000 52196986501917 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100175259/312500000 : ℝ), (1615172011/5000000000 : ℝ), (5974705591/10000000000 : ℝ)] ![(1486596860201/6250000000000 : ℝ), (6004365929397/25000000000000 : ℝ), (52196986501917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100175259/312500000 : ℝ)|^77 ≤ (1486596860201/6250000000000 : ℝ)^61
        have hw : |(-100175259/312500000 : ℝ)|=(100175259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1615172011/5000000000 : ℝ)|^77 ≤ (6004365929397/25000000000000 : ℝ)^61
        have hw : |(1615172011/5000000000 : ℝ)|=(1615172011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5974705591/10000000000 : ℝ)|^77 ≤ (52196986501917/100000000000000 : ℝ)^61
        have hw : |(5974705591/10000000000 : ℝ)|=(5974705591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3153217531/10000000000 : ℝ)*x 0 + (-319050099/1000000000 : ℝ)*x 1 + (1513206507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3153217531/10000000000 : ℝ)^77 ≤ (2911987906967/12500000000000 : ℝ)^61 := by
    have hnat : (3153217531 : ℕ)^77*12500000000000^61 ≤ 2911987906967^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3153217531 10000000000 2911987906967 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319050099/1000000000 : ℝ)^77 ≤ (23644139279063/100000000000000 : ℝ)^61 := by
    have hnat : (319050099 : ℕ)^77*100000000000000^61 ≤ 23644139279063^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319050099 1000000000 23644139279063 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1513206507/2500000000 : ℝ)^77 ≤ (10611991491613/20000000000000 : ℝ)^61 := by
    have hnat : (1513206507 : ℕ)^77*20000000000000^61 ≤ 10611991491613^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513206507 2500000000 10611991491613 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3153217531/10000000000 : ℝ), (-319050099/1000000000 : ℝ), (1513206507/2500000000 : ℝ)] ![(2911987906967/12500000000000 : ℝ), (23644139279063/100000000000000 : ℝ), (10611991491613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3153217531/10000000000 : ℝ)|^77 ≤ (2911987906967/12500000000000 : ℝ)^61
        have hw : |(3153217531/10000000000 : ℝ)|=(3153217531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-319050099/1000000000 : ℝ)|^77 ≤ (23644139279063/100000000000000 : ℝ)^61
        have hw : |(-319050099/1000000000 : ℝ)|=(319050099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1513206507/2500000000 : ℝ)|^77 ≤ (10611991491613/20000000000000 : ℝ)^61
        have hw : |(1513206507/2500000000 : ℝ)|=(1513206507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3425382771/5000000000 : ℝ)*x 0 + (4560710407/10000000000 : ℝ)*x 1 + (-227486007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3425382771/5000000000 : ℝ)^77 ≤ (62037498775439/100000000000000 : ℝ)^61 := by
    have hnat : (3425382771 : ℕ)^77*100000000000000^61 ≤ 62037498775439^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3425382771 5000000000 62037498775439 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4560710407/10000000000 : ℝ)^77 ≤ (37119182022107/100000000000000 : ℝ)^61 := by
    have hnat : (4560710407 : ℕ)^77*100000000000000^61 ≤ 37119182022107^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560710407 10000000000 37119182022107 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227486007/10000000000 : ℝ)^77 ≤ (33732767593/4000000000000 : ℝ)^61 := by
    have hnat : (227486007 : ℕ)^77*4000000000000^61 ≤ 33732767593^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227486007 10000000000 33732767593 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3425382771/5000000000 : ℝ), (4560710407/10000000000 : ℝ), (-227486007/10000000000 : ℝ)] ![(62037498775439/100000000000000 : ℝ), (37119182022107/100000000000000 : ℝ), (33732767593/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3425382771/5000000000 : ℝ)|^77 ≤ (62037498775439/100000000000000 : ℝ)^61
        have hw : |(3425382771/5000000000 : ℝ)|=(3425382771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4560710407/10000000000 : ℝ)|^77 ≤ (37119182022107/100000000000000 : ℝ)^61
        have hw : |(4560710407/10000000000 : ℝ)|=(4560710407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-227486007/10000000000 : ℝ)|^77 ≤ (33732767593/4000000000000 : ℝ)^61
        have hw : |(-227486007/10000000000 : ℝ)|=(227486007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316059_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (228892529/1250000000 : ℝ)*x 0 + (7501803641/10000000000 : ℝ)*x 1 + (2649274987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228892529/1250000000 : ℝ)^77 ≤ (11731055986789/100000000000000 : ℝ)^61 := by
    have hnat : (228892529 : ℕ)^77*100000000000000^61 ≤ 11731055986789^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228892529 1250000000 11731055986789 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7501803641/10000000000 : ℝ)^77 ≤ (69570042295297/100000000000000 : ℝ)^61 := by
    have hnat : (7501803641 : ℕ)^77*100000000000000^61 ≤ 69570042295297^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7501803641 10000000000 69570042295297 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2649274987/10000000000 : ℝ)^77 ≤ (9349450850977/50000000000000 : ℝ)^61 := by
    have hnat : (2649274987 : ℕ)^77*50000000000000^61 ≤ 9349450850977^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2649274987 10000000000 9349450850977 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228892529/1250000000 : ℝ), (7501803641/10000000000 : ℝ), (2649274987/10000000000 : ℝ)] ![(11731055986789/100000000000000 : ℝ), (69570042295297/100000000000000 : ℝ), (9349450850977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228892529/1250000000 : ℝ)|^77 ≤ (11731055986789/100000000000000 : ℝ)^61
        have hw : |(228892529/1250000000 : ℝ)|=(228892529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7501803641/10000000000 : ℝ)|^77 ≤ (69570042295297/100000000000000 : ℝ)^61
        have hw : |(7501803641/10000000000 : ℝ)|=(7501803641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2649274987/10000000000 : ℝ)|^77 ≤ (9349450850977/50000000000000 : ℝ)^61
        have hw : |(2649274987/10000000000 : ℝ)|=(2649274987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316059_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39359/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39359/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16151/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16151/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46387/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46387/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43919/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43919/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17739/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17739/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (79159/100000 : ℝ) ^ (19/4 : ℝ) ≤ (32951593489073371909/100000000000000000000 : ℝ) := by
    have hpowers : (79159/100000 : ℝ)^19 ≤ (32951593489073371909/100000000000000000000 : ℝ)^4 := by
      have hnat : (79159 : ℕ)^19*100000000000000000000^4 ≤ 32951593489073371909^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79159 100000 32951593489073371909 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79159/100000 : ℝ)) (X := (32951593489073371909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (132951593489073371909/100000000000000000000 : ℝ) ≤ (10617951731152317/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (132951593489073371909/100000000000000000000 : ℝ)^4 ≤ (10617951731152317/10000000000000000 : ℝ)^19 := by
      have hnat : (132951593489073371909 : ℕ)^4*10000000000000000^19 ≤ 10617951731152317^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132951593489073371909 100000000000000000000 10617951731152317 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10617951731152317/10000000000000000 : ℝ)) (X := (132951593489073371909/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (82951593489073371909/50000000000000000000 : ℝ) ≤ (11124620537951671/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (82951593489073371909/50000000000000000000 : ℝ)^4 ≤ (11124620537951671/10000000000000000 : ℝ)^19 := by
      have hnat : (82951593489073371909 : ℕ)^4*10000000000000000^19 ≤ 11124620537951671^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82951593489073371909 50000000000000000000 11124620537951671 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11124620537951671/10000000000000000 : ℝ)) (X := (82951593489073371909/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(617951731152317/7915900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(253334403399677/3957950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (79159/100000 : ℝ)) (alpha := (617951731152317/7915900000000000 : ℝ)) (beta := (253334403399677/3957950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79159/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(617951731152317/7915900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(253334403399677/3957950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (39359/50000 : ℝ) ^ (19/4 : ℝ) ≤ (16044335999910689697/50000000000000000000 : ℝ) := by
    have hpowers : (39359/50000 : ℝ)^19 ≤ (16044335999910689697/50000000000000000000 : ℝ)^4 := by
      have hnat : (39359 : ℕ)^19*50000000000000000000^4 ≤ 16044335999910689697^4*50000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39359 50000 16044335999910689697 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39359/50000 : ℝ)) (X := (16044335999910689697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (66044335999910689697/50000000000000000000 : ℝ) ≤ (5301702918108159/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (66044335999910689697/50000000000000000000 : ℝ)^4 ≤ (5301702918108159/5000000000000000 : ℝ)^19 := by
      have hnat : (66044335999910689697 : ℕ)^4*5000000000000000^19 ≤ 5301702918108159^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66044335999910689697 50000000000000000000 5301702918108159 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5301702918108159/5000000000000000 : ℝ)) (X := (66044335999910689697/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (41044335999910689697/25000000000000000000 : ℝ) ≤ (11100156454183059/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (41044335999910689697/25000000000000000000 : ℝ)^4 ≤ (11100156454183059/10000000000000000 : ℝ)^19 := by
      have hnat : (41044335999910689697 : ℕ)^4*10000000000000000^19 ≤ 11100156454183059^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41044335999910689697 25000000000000000000 11100156454183059 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11100156454183059/10000000000000000 : ℝ)) (X := (41044335999910689697/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(301702918108159/3935900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(496750617966741/7871800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (39359/50000 : ℝ)) (alpha := (301702918108159/3935900000000000 : ℝ)) (beta := (496750617966741/7871800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39359/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(301702918108159/3935900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(496750617966741/7871800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16151/25000 : ℝ) ^ (19/4 : ℝ) ≤ (12552556654646636017/100000000000000000000 : ℝ) := by
    have hpowers : (16151/25000 : ℝ)^19 ≤ (12552556654646636017/100000000000000000000 : ℝ)^4 := by
      have hnat : (16151 : ℕ)^19*100000000000000000000^4 ≤ 12552556654646636017^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16151 25000 12552556654646636017 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16151/25000 : ℝ)) (X := (12552556654646636017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (112552556654646636017/100000000000000000000 : ℝ) ≤ (5126036095981549/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (112552556654646636017/100000000000000000000 : ℝ)^4 ≤ (5126036095981549/5000000000000000 : ℝ)^19 := by
      have hnat : (112552556654646636017 : ℕ)^4*5000000000000000^19 ≤ 5126036095981549^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112552556654646636017 100000000000000000000 5126036095981549 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5126036095981549/5000000000000000 : ℝ)) (X := (112552556654646636017/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (62552556654646636017/50000000000000000000 : ℝ) ≤ (10482840070722399/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (62552556654646636017/50000000000000000000 : ℝ)^4 ≤ (10482840070722399/10000000000000000 : ℝ)^19 := by
      have hnat : (62552556654646636017 : ℕ)^4*10000000000000000^19 ≤ 10482840070722399^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62552556654646636017 50000000000000000000 10482840070722399 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10482840070722399/10000000000000000 : ℝ)) (X := (62552556654646636017/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(126036095981549/3230200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(230767878759301/6460400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (16151/25000 : ℝ)) (alpha := (126036095981549/3230200000000000 : ℝ)) (beta := (230767878759301/6460400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16151/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(126036095981549/3230200000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(230767878759301/6460400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((99745427/312500000 : ℝ)*X 1 0+(-159338867/500000000 : ℝ)*X 1 1+(6023340483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2966956421/5000000000 : ℝ)*X 2 0+(5425475161/10000000000 : ℝ)*X 2 1+(-457575983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1939503493/5000000000 : ℝ)*X 0 0+(2603431497/5000000000 : ℝ)*X 0 1+(3425663637/10000000000 : ℝ)*X 0 2+(1939503493/5000000000 : ℝ)*X 1 0+(2603431497/5000000000 : ℝ)*X 1 1+(3425663637/10000000000 : ℝ)*X 1 2+(1939503493/5000000000 : ℝ)*X 2 0+(2603431497/5000000000 : ℝ)*X 2 1+(3425663637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-3004007407/10000000000 : ℝ)*X 0 0+(2787507747/10000000000 : ℝ)*X 0 1+(406764479/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1511046389/5000000000 : ℝ)*X 1 0+(-2761174479/10000000000 : ℝ)*X 1 1+(1302901873/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5710267103/10000000000 : ℝ)*X 2 0+(2918575319/5000000000 : ℝ)*X 2 1+(-2630491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3521335243/10000000000 : ℝ)*X 0 0+(3236430621/5000000000 : ℝ)*X 0 1+(1139960579/5000000000 : ℝ)*X 0 2+(3521335243/10000000000 : ℝ)*X 1 0+(3236430621/5000000000 : ℝ)*X 1 1+(1139960579/5000000000 : ℝ)*X 1 2+(3521335243/10000000000 : ℝ)*X 2 0+(3236430621/5000000000 : ℝ)*X 2 1+(1139960579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2777683913/10000000000 : ℝ)*X 0 0+(3015461333/10000000000 : ℝ)*X 0 1+(1626684147/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2768378799/10000000000 : ℝ)*X 1 0+(-15084421/50000000 : ℝ)*X 1 1+(407063291/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3170129781/5000000000 : ℝ)*X 2 0+(5192043371/10000000000 : ℝ)*X 2 1+(-6008977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2599522901/5000000000 : ℝ)*X 0 0+(4906187339/10000000000 : ℝ)*X 0 1+(2283728003/10000000000 : ℝ)*X 0 2+(2599522901/5000000000 : ℝ)*X 1 0+(4906187339/10000000000 : ℝ)*X 1 1+(2283728003/10000000000 : ℝ)*X 1 2+(2599522901/5000000000 : ℝ)*X 2 0+(4906187339/10000000000 : ℝ)*X 2 1+(2283728003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-100175259/312500000 : ℝ)*X 0 0+(1615172011/5000000000 : ℝ)*X 0 1+(5974705591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3153217531/10000000000 : ℝ)*X 1 0+(-319050099/1000000000 : ℝ)*X 1 1+(1513206507/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3425382771/5000000000 : ℝ)*X 2 0+(4560710407/10000000000 : ℝ)*X 2 1+(-227486007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((228892529/1250000000 : ℝ)*X 0 0+(7501803641/10000000000 : ℝ)*X 0 1+(2649274987/10000000000 : ℝ)*X 0 2+(228892529/1250000000 : ℝ)*X 1 0+(7501803641/10000000000 : ℝ)*X 1 1+(2649274987/10000000000 : ℝ)*X 1 2+(228892529/1250000000 : ℝ)*X 2 0+(7501803641/10000000000 : ℝ)*X 2 1+(2649274987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316059_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((46387/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46387/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (611845357575541813314801742557/201281455108924000000000000000000000 : ℝ) := by norm_num
    linear_combination (16289/500000000000 : ℝ)*(base19) + (323887/200000000000 : ℝ)*(base59) + (431702399559/200000000000 : ℝ)*(base60) + (798535627917/100000000000 : ℝ)*(major_s1_0) + (798535627917/100000000000 : ℝ)*(major_s1_1) + (798535627917/100000000000 : ℝ)*(major_s1_2) + (7015929/500000000000 : ℝ)*(sp_s1_2) + (1182819/500000000000 : ℝ)*(sp_s1_6) + (5732875960979/500000000000 : ℝ)*(sp_s1_7) + (11465709293677/1000000000000 : ℝ)*(sp_s1_8) + (114657378901/10000000000 : ℝ)*(sp_s1_9) + (2252473785009/500000000000 : ℝ)*(sp_s1_13) + (42595703/1000000000000 : ℝ)*(sp_s1_15) + (9687473/1000000000000 : ℝ)*(sp_s1_27) + (4504959623129/1000000000000 : ℝ)*(f.failure) + (5732875960979/500000000000 : ℝ)*(f.sum) + (1960618056972490637/12713744180000000000000000000000 : ℝ)*base62 + (78252250371571/646040000000000000000000000 : ℝ)*base64 + (218205764025563/787180000000000000000000000 : ℝ)*base67 + (1198522242179/64604000000000000000000000 : ℝ)*base68 + (13936300799776314309/51139880360000000000000000000000 : ℝ)*base70 + (36294494285769/98948750000000000000000000 : ℝ)*base73 + (76658706405677/393590000000000000000000000 : ℝ)*base75 + (63282897530477/197897500000000000000000000 : ℝ)*base77 + (2654444641004197253/62312381620000000000000000000000 : ℝ)*base79 + (22847/100000000000000000 : ℝ)*base86 + (22847/100000000000000000 : ℝ)*base88 + (22847/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43919/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43919/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19911490605225412456142938766187/1006407275544620000000000000000000000 : ℝ) := by norm_num
    linear_combination (1085807/200000000000 : ℝ)*(base19) + (1290557/125000000000 : ℝ)*(base59) + (531784895539/250000000000 : ℝ)*(base60) + (787303402969/100000000000 : ℝ)*(major_s1_0) + (787303402969/100000000000 : ℝ)*(major_s1_1) + (787303402969/100000000000 : ℝ)*(major_s1_2) + (591569/1000000000000 : ℝ)*(sp_s1_2) + (15245079/500000000000 : ℝ)*(sp_s1_6) + (129275189/500000000000 : ℝ)*(sp_s1_7) + (11304210181681/1000000000000 : ℝ)*(sp_s1_14) + (706528956439/62500000000 : ℝ)*(sp_s1_15) + (5652160554229/500000000000 : ℝ)*(sp_s1_16) + (4441562242253/1000000000000 : ℝ)*(sp_s1_20) + (4594751/31250000000 : ℝ)*(sp_s1_23) + (4441592732411/1000000000000 : ℝ)*(f.failure) + (11304468732059/1000000000000 : ℝ)*(f.sum) + (2033837859005074553/12713744180000000000000000000000 : ℝ)*base63 + (27420570010037/646040000000000000000000000 : ℝ)*base65 + (98318112632321/787180000000000000000000000 : ℝ)*base66 + (659805027721/323020000000000000000000000 : ℝ)*base68 + (10054228306901381179/51139880360000000000000000000000 : ℝ)*base71 + (13510364133133/158318000000000000000000000 : ℝ)*base72 + (5586802186083/393590000000000000000000000 : ℝ)*base75 + (50939612845657/791590000000000000000000000 : ℝ)*base76 + (1073321358498617/12462476324000000000000000000000 : ℝ)*base78 + (23373/100000000000000000 : ℝ)*base86 + (23373/100000000000000000 : ℝ)*base88 + (23373/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17739/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17739/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22518683541443628159090919470447/2012814551089240000000000000000000000 : ℝ) := by norm_num
    linear_combination (13349/10000000000 : ℝ)*(base16) + (1104769/500000000000 : ℝ)*(base40) + (40253036739/1000000000000 : ℝ)*(base50) + (9065869707/15625000000 : ℝ)*(base60) + (780504784457/200000000000 : ℝ)*(major_s1_0) + (780504784457/200000000000 : ℝ)*(major_s1_1) + (780504784457/200000000000 : ℝ)*(major_s1_2) + (1661470433/1000000000000 : ℝ)*(sp_s1_1) + (25243303/1000000000000 : ℝ)*(sp_s1_13) + (51402153/500000000000 : ℝ)*(sp_s1_16) + (5603425041183/1000000000000 : ℝ)*(sp_s1_21) + (5601762235849/1000000000000 : ℝ)*(sp_s1_22) + (5603322236877/1000000000000 : ℝ)*(sp_s1_23) + (1100796915429/500000000000 : ℝ)*(sp_s1_27) + (2201619074161/1000000000000 : ℝ)*(f.failure) + (5603425041183/1000000000000 : ℝ)*(f.sum) + (3868058148368384477/25427488360000000000000000000000 : ℝ)*base62 + (1117012927846083/1292080000000000000000000000 : ℝ)*base64 + (1247049715748991/1574360000000000000000000000 : ℝ)*base66 + (422972448985557/646040000000000000000000000 : ℝ)*base68 + (66152151819698896889/102279760720000000000000000000000 : ℝ)*base70 + (14436704637947/39579500000000000000000000 : ℝ)*base72 + (1887618940967/6297440000000000000000000 : ℝ)*base74 + (390234480709673/1583180000000000000000000000 : ℝ)*base76 + (78536039990574073981/124624763240000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (56377/100000000000000000 : ℝ)*base87 + (56377/100000000000000000 : ℝ)*base89 + (56377/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39359/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39359/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16151/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16151/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46387/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46387/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43919/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43919/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17739/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17739/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316059_s1 p hpa hpb X hX hprev0

#print axioms solution

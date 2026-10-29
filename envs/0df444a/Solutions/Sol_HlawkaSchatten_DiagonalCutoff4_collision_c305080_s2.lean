-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305080_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:33:28.533755+00:00
-- url     : https://prove2.me/submissions/06732cc3-e5ed-45ce-bf71-b5a0a4bd9c41

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
theorem collision_support_c305080_s2_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-680905999/2000000000 : ℝ)*x 0 + (563255001/1000000000 : ℝ)*x 1 + (3864347799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (680905999/2000000000 : ℝ)^67 ≤ (24280161405951/100000000000000 : ℝ)^51 := by
    have hnat : (680905999 : ℕ)^67*100000000000000^51 ≤ 24280161405951^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680905999 2000000000 24280161405951 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563255001/1000000000 : ℝ)^67 ≤ (4704298575423/10000000000000 : ℝ)^51 := by
    have hnat : (563255001 : ℕ)^67*10000000000000^51 ≤ 4704298575423^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563255001 1000000000 4704298575423 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3864347799/10000000000 : ℝ)^67 ≤ (28676852825443/100000000000000 : ℝ)^51 := by
    have hnat : (3864347799 : ℕ)^67*100000000000000^51 ≤ 28676852825443^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864347799 10000000000 28676852825443 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-680905999/2000000000 : ℝ), (563255001/1000000000 : ℝ), (3864347799/10000000000 : ℝ)] ![(24280161405951/100000000000000 : ℝ), (4704298575423/10000000000000 : ℝ), (28676852825443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-680905999/2000000000 : ℝ)|^67 ≤ (24280161405951/100000000000000 : ℝ)^51
        have hw : |(-680905999/2000000000 : ℝ)|=(680905999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563255001/1000000000 : ℝ)|^67 ≤ (4704298575423/10000000000000 : ℝ)^51
        have hw : |(563255001/1000000000 : ℝ)|=(563255001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3864347799/10000000000 : ℝ)|^67 ≤ (28676852825443/100000000000000 : ℝ)^51
        have hw : |(3864347799/10000000000 : ℝ)|=(3864347799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3065090087/5000000000 : ℝ)*x 0 + (-269569827/5000000000 : ℝ)*x 1 + (218793981/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3065090087/5000000000 : ℝ)^67 ≤ (2103091500911/4000000000000 : ℝ)^51 := by
    have hnat : (3065090087 : ℕ)^67*4000000000000^51 ≤ 2103091500911^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3065090087 5000000000 2103091500911 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269569827/5000000000 : ℝ)^67 ≤ (2156769019481/100000000000000 : ℝ)^51 := by
    have hnat : (269569827 : ℕ)^67*100000000000000^51 ≤ 2156769019481^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269569827 5000000000 2156769019481 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218793981/400000000 : ℝ)^67 ≤ (22632971721591/50000000000000 : ℝ)^51 := by
    have hnat : (218793981 : ℕ)^67*50000000000000^51 ≤ 22632971721591^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218793981 400000000 22632971721591 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3065090087/5000000000 : ℝ), (-269569827/5000000000 : ℝ), (218793981/400000000 : ℝ)] ![(2103091500911/4000000000000 : ℝ), (2156769019481/100000000000000 : ℝ), (22632971721591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3065090087/5000000000 : ℝ)|^67 ≤ (2103091500911/4000000000000 : ℝ)^51
        have hw : |(3065090087/5000000000 : ℝ)|=(3065090087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269569827/5000000000 : ℝ)|^67 ≤ (2156769019481/100000000000000 : ℝ)^51
        have hw : |(-269569827/5000000000 : ℝ)|=(269569827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218793981/400000000 : ℝ)|^67 ≤ (22632971721591/50000000000000 : ℝ)^51
        have hw : |(218793981/400000000 : ℝ)|=(218793981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-841550427/2500000000 : ℝ)*x 0 + (5722607603/10000000000 : ℝ)*x 1 + (1899667307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841550427/2500000000 : ℝ)^67 ≤ (23921694699047/100000000000000 : ℝ)^51 := by
    have hnat : (841550427 : ℕ)^67*100000000000000^51 ≤ 23921694699047^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841550427 2500000000 23921694699047 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5722607603/10000000000 : ℝ)^67 ≤ (48033586617057/100000000000000 : ℝ)^51 := by
    have hnat : (5722607603 : ℕ)^67*100000000000000^51 ≤ 48033586617057^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5722607603 10000000000 48033586617057 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1899667307/5000000000 : ℝ)^67 ≤ (5608943732317/20000000000000 : ℝ)^51 := by
    have hnat : (1899667307 : ℕ)^67*20000000000000^51 ≤ 5608943732317^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899667307 5000000000 5608943732317 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-841550427/2500000000 : ℝ), (5722607603/10000000000 : ℝ), (1899667307/5000000000 : ℝ)] ![(23921694699047/100000000000000 : ℝ), (48033586617057/100000000000000 : ℝ), (5608943732317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-841550427/2500000000 : ℝ)|^67 ≤ (23921694699047/100000000000000 : ℝ)^51
        have hw : |(-841550427/2500000000 : ℝ)|=(841550427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5722607603/10000000000 : ℝ)|^67 ≤ (48033586617057/100000000000000 : ℝ)^51
        have hw : |(5722607603/10000000000 : ℝ)|=(5722607603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1899667307/5000000000 : ℝ)|^67 ≤ (5608943732317/20000000000000 : ℝ)^51
        have hw : |(1899667307/5000000000 : ℝ)|=(1899667307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (233913903/400000000 : ℝ)*x 0 + (720803/5000000000 : ℝ)*x 1 + (5952083543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233913903/400000000 : ℝ)^67 ≤ (1235482995959/2500000000000 : ℝ)^51 := by
    have hnat : (233913903 : ℕ)^67*2500000000000^51 ≤ 1235482995959^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233913903 400000000 1235482995959 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720803/5000000000 : ℝ)^67 ≤ (899039643/100000000000000 : ℝ)^51 := by
    have hnat : (720803 : ℕ)^67*100000000000000^51 ≤ 899039643^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720803 5000000000 899039643 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5952083543/10000000000 : ℝ)^67 ≤ (6322472639703/12500000000000 : ℝ)^51 := by
    have hnat : (5952083543 : ℕ)^67*12500000000000^51 ≤ 6322472639703^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5952083543 10000000000 6322472639703 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(233913903/400000000 : ℝ), (720803/5000000000 : ℝ), (5952083543/10000000000 : ℝ)] ![(1235482995959/2500000000000 : ℝ), (899039643/100000000000000 : ℝ), (6322472639703/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(233913903/400000000 : ℝ)|^67 ≤ (1235482995959/2500000000000 : ℝ)^51
        have hw : |(233913903/400000000 : ℝ)|=(233913903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(720803/5000000000 : ℝ)|^67 ≤ (899039643/100000000000000 : ℝ)^51
        have hw : |(720803/5000000000 : ℝ)|=(720803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5952083543/10000000000 : ℝ)|^67 ≤ (6322472639703/12500000000000 : ℝ)^51
        have hw : |(5952083543/10000000000 : ℝ)|=(5952083543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (86319017/312500000 : ℝ)*x 0 + (6771822273/10000000000 : ℝ)*x 1 + (-155881249/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86319017/312500000 : ℝ)^67 ≤ (9224320390071/50000000000000 : ℝ)^51 := by
    have hnat : (86319017 : ℕ)^67*50000000000000^51 ≤ 9224320390071^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86319017 312500000 9224320390071 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6771822273/10000000000 : ℝ)^67 ≤ (59923002730079/100000000000000 : ℝ)^51 := by
    have hnat : (6771822273 : ℕ)^67*100000000000000^51 ≤ 59923002730079^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6771822273 10000000000 59923002730079 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155881249/500000000 : ℝ)^67 ≤ (21628356472841/100000000000000 : ℝ)^51 := by
    have hnat : (155881249 : ℕ)^67*100000000000000^51 ≤ 21628356472841^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155881249 500000000 21628356472841 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86319017/312500000 : ℝ), (6771822273/10000000000 : ℝ), (-155881249/500000000 : ℝ)] ![(9224320390071/50000000000000 : ℝ), (59923002730079/100000000000000 : ℝ), (21628356472841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86319017/312500000 : ℝ)|^67 ≤ (9224320390071/50000000000000 : ℝ)^51
        have hw : |(86319017/312500000 : ℝ)|=(86319017/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6771822273/10000000000 : ℝ)|^67 ≤ (59923002730079/100000000000000 : ℝ)^51
        have hw : |(6771822273/10000000000 : ℝ)|=(6771822273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-155881249/500000000 : ℝ)|^67 ≤ (21628356472841/100000000000000 : ℝ)^51
        have hw : |(-155881249/500000000 : ℝ)|=(155881249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_12 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (402220857/1000000000 : ℝ)*x 0 + (973606623/2000000000 : ℝ)*x 1 + (51173789/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402220857/1000000000 : ℝ)^67 ≤ (15112804001881/50000000000000 : ℝ)^51 := by
    have hnat : (402220857 : ℕ)^67*50000000000000^51 ≤ 15112804001881^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402220857 1000000000 15112804001881 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973606623/2000000000 : ℝ)^67 ≤ (4854878526133/12500000000000 : ℝ)^51 := by
    have hnat : (973606623 : ℕ)^67*12500000000000^51 ≤ 4854878526133^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973606623 2000000000 4854878526133 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51173789/125000000 : ℝ)^67 ≤ (1237414550981/4000000000000 : ℝ)^51 := by
    have hnat : (51173789 : ℕ)^67*4000000000000^51 ≤ 1237414550981^51*125000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51173789 125000000 1237414550981 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(402220857/1000000000 : ℝ), (973606623/2000000000 : ℝ), (51173789/125000000 : ℝ)] ![(15112804001881/50000000000000 : ℝ), (4854878526133/12500000000000 : ℝ), (1237414550981/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(402220857/1000000000 : ℝ)|^67 ≤ (15112804001881/50000000000000 : ℝ)^51
        have hw : |(402220857/1000000000 : ℝ)|=(402220857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973606623/2000000000 : ℝ)|^67 ≤ (4854878526133/12500000000000 : ℝ)^51
        have hw : |(973606623/2000000000 : ℝ)|=(973606623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51173789/125000000 : ℝ)|^67 ≤ (1237414550981/4000000000000 : ℝ)^51
        have hw : |(51173789/125000000 : ℝ)|=(51173789/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-820977899/2000000000 : ℝ)*x 0 + (1118668459/2000000000 : ℝ)*x 1 + (3195652427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820977899/2000000000 : ℝ)^67 ≤ (6208894494837/20000000000000 : ℝ)^51 := by
    have hnat : (820977899 : ℕ)^67*20000000000000^51 ≤ 6208894494837^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820977899 2000000000 6208894494837 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118668459/2000000000 : ℝ)^67 ≤ (23306630311083/50000000000000 : ℝ)^51 := by
    have hnat : (1118668459 : ℕ)^67*50000000000000^51 ≤ 23306630311083^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118668459 2000000000 23306630311083 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3195652427/10000000000 : ℝ)^67 ≤ (22342266895549/100000000000000 : ℝ)^51 := by
    have hnat : (3195652427 : ℕ)^67*100000000000000^51 ≤ 22342266895549^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195652427 10000000000 22342266895549 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-820977899/2000000000 : ℝ), (1118668459/2000000000 : ℝ), (3195652427/10000000000 : ℝ)] ![(6208894494837/20000000000000 : ℝ), (23306630311083/50000000000000 : ℝ), (22342266895549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-820977899/2000000000 : ℝ)|^67 ≤ (6208894494837/20000000000000 : ℝ)^51
        have hw : |(-820977899/2000000000 : ℝ)|=(820977899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118668459/2000000000 : ℝ)|^67 ≤ (23306630311083/50000000000000 : ℝ)^51
        have hw : |(1118668459/2000000000 : ℝ)|=(1118668459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3195652427/10000000000 : ℝ)|^67 ≤ (22342266895549/100000000000000 : ℝ)^51
        have hw : |(3195652427/10000000000 : ℝ)|=(3195652427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1438660683/2500000000 : ℝ)*x 0 + (-88132093/2000000000 : ℝ)*x 1 + (5896317091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1438660683/2500000000 : ℝ)^67 ≤ (6048393300099/12500000000000 : ℝ)^51 := by
    have hnat : (1438660683 : ℕ)^67*12500000000000^51 ≤ 6048393300099^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438660683 2500000000 6048393300099 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88132093/2000000000 : ℝ)^67 ≤ (206840220409/12500000000000 : ℝ)^51 := by
    have hnat : (88132093 : ℕ)^67*12500000000000^51 ≤ 206840220409^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88132093 2000000000 206840220409 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5896317091/10000000000 : ℝ)^67 ≤ (49958131818959/100000000000000 : ℝ)^51 := by
    have hnat : (5896317091 : ℕ)^67*100000000000000^51 ≤ 49958131818959^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5896317091 10000000000 49958131818959 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1438660683/2500000000 : ℝ), (-88132093/2000000000 : ℝ), (5896317091/10000000000 : ℝ)] ![(6048393300099/12500000000000 : ℝ), (206840220409/12500000000000 : ℝ), (49958131818959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1438660683/2500000000 : ℝ)|^67 ≤ (6048393300099/12500000000000 : ℝ)^51
        have hw : |(1438660683/2500000000 : ℝ)|=(1438660683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88132093/2000000000 : ℝ)|^67 ≤ (206840220409/12500000000000 : ℝ)^51
        have hw : |(-88132093/2000000000 : ℝ)|=(88132093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5896317091/10000000000 : ℝ)|^67 ≤ (49958131818959/100000000000000 : ℝ)^51
        have hw : |(5896317091/10000000000 : ℝ)|=(5896317091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2487326889/10000000000 : ℝ)*x 0 + (3027831543/5000000000 : ℝ)*x 1 + (-527403893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2487326889/10000000000 : ℝ)^67 ≤ (643011666917/4000000000000 : ℝ)^51 := by
    have hnat : (2487326889 : ℕ)^67*4000000000000^51 ≤ 643011666917^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487326889 10000000000 643011666917 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3027831543/5000000000 : ℝ)^67 ≤ (51739267833861/100000000000000 : ℝ)^51 := by
    have hnat : (3027831543 : ℕ)^67*100000000000000^51 ≤ 51739267833861^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3027831543 5000000000 51739267833861 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527403893/1250000000 : ℝ)^67 ≤ (32185440486717/100000000000000 : ℝ)^51 := by
    have hnat : (527403893 : ℕ)^67*100000000000000^51 ≤ 32185440486717^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527403893 1250000000 32185440486717 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2487326889/10000000000 : ℝ), (3027831543/5000000000 : ℝ), (-527403893/1250000000 : ℝ)] ![(643011666917/4000000000000 : ℝ), (51739267833861/100000000000000 : ℝ), (32185440486717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2487326889/10000000000 : ℝ)|^67 ≤ (643011666917/4000000000000 : ℝ)^51
        have hw : |(2487326889/10000000000 : ℝ)|=(2487326889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3027831543/5000000000 : ℝ)|^67 ≤ (51739267833861/100000000000000 : ℝ)^51
        have hw : |(3027831543/5000000000 : ℝ)|=(3027831543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527403893/1250000000 : ℝ)|^67 ≤ (32185440486717/100000000000000 : ℝ)^51
        have hw : |(-527403893/1250000000 : ℝ)|=(527403893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_19 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2584424963/5000000000 : ℝ)*x 0 + (4569970041/10000000000 : ℝ)*x 1 + (636738953/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584424963/5000000000 : ℝ)^67 ≤ (10505538037491/25000000000000 : ℝ)^51 := by
    have hnat : (2584424963 : ℕ)^67*25000000000000^51 ≤ 10505538037491^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584424963 5000000000 10505538037491 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4569970041/10000000000 : ℝ)^67 ≤ (1787267290783/5000000000000 : ℝ)^51 := by
    have hnat : (4569970041 : ℕ)^67*5000000000000^51 ≤ 1787267290783^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569970041 10000000000 1787267290783 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (636738953/2000000000 : ℝ)^67 ≤ (11116251009651/50000000000000 : ℝ)^51 := by
    have hnat : (636738953 : ℕ)^67*50000000000000^51 ≤ 11116251009651^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636738953 2000000000 11116251009651 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584424963/5000000000 : ℝ), (4569970041/10000000000 : ℝ), (636738953/2000000000 : ℝ)] ![(10505538037491/25000000000000 : ℝ), (1787267290783/5000000000000 : ℝ), (11116251009651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584424963/5000000000 : ℝ)|^67 ≤ (10505538037491/25000000000000 : ℝ)^51
        have hw : |(2584424963/5000000000 : ℝ)|=(2584424963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4569970041/10000000000 : ℝ)|^67 ≤ (1787267290783/5000000000000 : ℝ)^51
        have hw : |(4569970041/10000000000 : ℝ)|=(4569970041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(636738953/2000000000 : ℝ)|^67 ≤ (11116251009651/50000000000000 : ℝ)^51
        have hw : |(636738953/2000000000 : ℝ)|=(636738953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-741518887/2500000000 : ℝ)*x 0 + (5978657777/10000000000 : ℝ)*x 1 + (242730447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741518887/2500000000 : ℝ)^67 ≤ (10128900796151/50000000000000 : ℝ)^51 := by
    have hnat : (741518887 : ℕ)^67*50000000000000^51 ≤ 10128900796151^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741518887 2500000000 10128900796151 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5978657777/10000000000 : ℝ)^67 ≤ (50876658456261/100000000000000 : ℝ)^51 := by
    have hnat : (5978657777 : ℕ)^67*100000000000000^51 ≤ 50876658456261^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978657777 10000000000 50876658456261 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242730447/625000000 : ℝ)^67 ≤ (7216384986663/25000000000000 : ℝ)^51 := by
    have hnat : (242730447 : ℕ)^67*25000000000000^51 ≤ 7216384986663^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242730447 625000000 7216384986663 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-741518887/2500000000 : ℝ), (5978657777/10000000000 : ℝ), (242730447/625000000 : ℝ)] ![(10128900796151/50000000000000 : ℝ), (50876658456261/100000000000000 : ℝ), (7216384986663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-741518887/2500000000 : ℝ)|^67 ≤ (10128900796151/50000000000000 : ℝ)^51
        have hw : |(-741518887/2500000000 : ℝ)|=(741518887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5978657777/10000000000 : ℝ)|^67 ≤ (50876658456261/100000000000000 : ℝ)^51
        have hw : |(5978657777/10000000000 : ℝ)|=(5978657777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(242730447/625000000 : ℝ)|^67 ≤ (7216384986663/25000000000000 : ℝ)^51
        have hw : |(242730447/625000000 : ℝ)|=(242730447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6893302261/10000000000 : ℝ)*x 0 + (9/2000000000 : ℝ)*x 1 + (2425511481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6893302261/10000000000 : ℝ)^67 ≤ (61339164263343/100000000000000 : ℝ)^51 := by
    have hnat : (6893302261 : ℕ)^67*100000000000000^51 ≤ 61339164263343^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6893302261 10000000000 61339164263343 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9/2000000000 : ℝ)^67 ≤ (1083/100000000000000 : ℝ)^51 := by
    have hnat : (9 : ℕ)^67*100000000000000^51 ≤ 1083^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9 2000000000 1083 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2425511481/5000000000 : ℝ)^67 ≤ (38660835727179/100000000000000 : ℝ)^51 := by
    have hnat : (2425511481 : ℕ)^67*100000000000000^51 ≤ 38660835727179^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425511481 5000000000 38660835727179 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6893302261/10000000000 : ℝ), (9/2000000000 : ℝ), (2425511481/5000000000 : ℝ)] ![(61339164263343/100000000000000 : ℝ), (1083/100000000000000 : ℝ), (38660835727179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6893302261/10000000000 : ℝ)|^67 ≤ (61339164263343/100000000000000 : ℝ)^51
        have hw : |(6893302261/10000000000 : ℝ)|=(6893302261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9/2000000000 : ℝ)|^67 ≤ (1083/100000000000000 : ℝ)^51
        have hw : |(9/2000000000 : ℝ)|=(9/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2425511481/5000000000 : ℝ)|^67 ≤ (38660835727179/100000000000000 : ℝ)^51
        have hw : |(2425511481/5000000000 : ℝ)|=(2425511481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (635296387/2500000000 : ℝ)*x 0 + (677038087/1000000000 : ℝ)*x 1 + (-332734939/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (635296387/2500000000 : ℝ)^67 ≤ (4133530353673/25000000000000 : ℝ)^51 := by
    have hnat : (635296387 : ℕ)^67*25000000000000^51 ≤ 4133530353673^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635296387 2500000000 4133530353673 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677038087/1000000000 : ℝ)^67 ≤ (59906246992003/100000000000000 : ℝ)^51 := by
    have hnat : (677038087 : ℕ)^67*100000000000000^51 ≤ 59906246992003^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677038087 1000000000 59906246992003 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332734939/1000000000 : ℝ)^67 ≤ (5889907896879/25000000000000 : ℝ)^51 := by
    have hnat : (332734939 : ℕ)^67*25000000000000^51 ≤ 5889907896879^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332734939 1000000000 5889907896879 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(635296387/2500000000 : ℝ), (677038087/1000000000 : ℝ), (-332734939/1000000000 : ℝ)] ![(4133530353673/25000000000000 : ℝ), (59906246992003/100000000000000 : ℝ), (5889907896879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(635296387/2500000000 : ℝ)|^67 ≤ (4133530353673/25000000000000 : ℝ)^51
        have hw : |(635296387/2500000000 : ℝ)|=(635296387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677038087/1000000000 : ℝ)|^67 ≤ (59906246992003/100000000000000 : ℝ)^51
        have hw : |(677038087/1000000000 : ℝ)|=(677038087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332734939/1000000000 : ℝ)|^67 ≤ (5889907896879/25000000000000 : ℝ)^51
        have hw : |(-332734939/1000000000 : ℝ)|=(332734939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305080_s2_s2_25 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1264574113/2500000000 : ℝ)*x 0 + (4340938917/10000000000 : ℝ)*x 1 + (3559674493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1264574113/2500000000 : ℝ)^67 ≤ (10211343467911/25000000000000 : ℝ)^51 := by
    have hnat : (1264574113 : ℕ)^67*25000000000000^51 ≤ 10211343467911^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264574113 2500000000 10211343467911 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4340938917/10000000000 : ℝ)^67 ≤ (16705306175141/50000000000000 : ℝ)^51 := by
    have hnat : (4340938917 : ℕ)^67*50000000000000^51 ≤ 16705306175141^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340938917 10000000000 16705306175141 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3559674493/10000000000 : ℝ)^67 ≤ (12872006880957/50000000000000 : ℝ)^51 := by
    have hnat : (3559674493 : ℕ)^67*50000000000000^51 ≤ 12872006880957^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3559674493 10000000000 12872006880957 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1264574113/2500000000 : ℝ), (4340938917/10000000000 : ℝ), (3559674493/10000000000 : ℝ)] ![(10211343467911/25000000000000 : ℝ), (16705306175141/50000000000000 : ℝ), (12872006880957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1264574113/2500000000 : ℝ)|^67 ≤ (10211343467911/25000000000000 : ℝ)^51
        have hw : |(1264574113/2500000000 : ℝ)|=(1264574113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4340938917/10000000000 : ℝ)|^67 ≤ (16705306175141/50000000000000 : ℝ)^51
        have hw : |(4340938917/10000000000 : ℝ)|=(4340938917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3559674493/10000000000 : ℝ)|^67 ≤ (12872006880957/50000000000000 : ℝ)^51
        have hw : |(3559674493/10000000000 : ℝ)|=(3559674493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305080_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((36749/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36749/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((19471/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(19471/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41163/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41163/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8551/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8551/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10557/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(10557/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(983/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(983/2000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (36749/50000 : ℝ) ^ (133/32 : ℝ) ≤ (27810425636676254497/100000000000000000000 : ℝ) := by
    have hpowers : (36749/50000 : ℝ)^133 ≤ (27810425636676254497/100000000000000000000 : ℝ)^32 := by
      have hnat : (36749 : ℕ)^133*100000000000000000000^32 ≤ 27810425636676254497^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36749 50000 27810425636676254497 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36749/50000 : ℝ)) (X := (27810425636676254497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (127810425636676254497/100000000000000000000 : ℝ) ≤ (10608158681902067/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (127810425636676254497/100000000000000000000 : ℝ)^32 ≤ (10608158681902067/10000000000000000 : ℝ)^133 := by
      have hnat : (127810425636676254497 : ℕ)^32*10000000000000000^133 ≤ 10608158681902067^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127810425636676254497 100000000000000000000 10608158681902067 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10608158681902067/10000000000000000 : ℝ)) (X := (127810425636676254497/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (77810425636676254497/50000000000000000000 : ℝ) ≤ (2224548065656733/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (77810425636676254497/50000000000000000000 : ℝ)^32 ≤ (2224548065656733/2000000000000000 : ℝ)^133 := by
      have hnat : (77810425636676254497 : ℕ)^32*2000000000000000^133 ≤ 2224548065656733^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77810425636676254497 50000000000000000000 2224548065656733 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2224548065656733/2000000000000000 : ℝ)) (X := (77810425636676254497/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(608158681902067/7349800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(257290823190799/3674900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (36749/50000 : ℝ)) (alpha := (608158681902067/7349800000000000 : ℝ)) (beta := (257290823190799/3674900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36749/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(608158681902067/7349800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(257290823190799/3674900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (19471/50000 : ℝ) ^ (133/32 : ℝ) ≤ (496153284128387103/25000000000000000000 : ℝ) := by
    have hpowers : (19471/50000 : ℝ)^133 ≤ (496153284128387103/25000000000000000000 : ℝ)^32 := by
      have hnat : (19471 : ℕ)^133*25000000000000000000^32 ≤ 496153284128387103^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19471 50000 496153284128387103 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19471/50000 : ℝ)) (X := (496153284128387103/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (25496153284128387103/25000000000000000000 : ℝ) ≤ (5023697199149463/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25496153284128387103/25000000000000000000 : ℝ)^32 ≤ (5023697199149463/5000000000000000 : ℝ)^133 := by
      have hnat : (25496153284128387103 : ℕ)^32*5000000000000000^133 ≤ 5023697199149463^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25496153284128387103 25000000000000000000 5023697199149463 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023697199149463/5000000000000000 : ℝ)) (X := (25496153284128387103/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (12996153284128387103/12500000000000000000 : ℝ) ≤ (5047046749695019/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12996153284128387103/12500000000000000000 : ℝ)^32 ≤ (5047046749695019/5000000000000000 : ℝ)^133 := by
      have hnat : (12996153284128387103 : ℕ)^32*5000000000000000^133 ≤ 5047046749695019^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12996153284128387103 12500000000000000000 5047046749695019 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047046749695019/5000000000000000 : ℝ)) (X := (12996153284128387103/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(23697199149463/1947100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(5837387636389/486775000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (19471/50000 : ℝ)) (alpha := (23697199149463/1947100000000000 : ℝ)) (beta := (5837387636389/486775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (19471/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(23697199149463/1947100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(5837387636389/486775000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (41163/50000 : ℝ) ^ (133/32 : ℝ) ≤ (44560567938388806541/100000000000000000000 : ℝ) := by
    have hpowers : (41163/50000 : ℝ)^133 ≤ (44560567938388806541/100000000000000000000 : ℝ)^32 := by
      have hnat : (41163 : ℕ)^133*100000000000000000000^32 ≤ 44560567938388806541^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41163 50000 44560567938388806541 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41163/50000 : ℝ)) (X := (44560567938388806541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (144560567938388806541/100000000000000000000 : ℝ) ≤ (2731795858226267/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (144560567938388806541/100000000000000000000 : ℝ)^32 ≤ (2731795858226267/2500000000000000 : ℝ)^133 := by
      have hnat : (144560567938388806541 : ℕ)^32*2500000000000000^133 ≤ 2731795858226267^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144560567938388806541 100000000000000000000 2731795858226267 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2731795858226267/2500000000000000 : ℝ)) (X := (144560567938388806541/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (94560567938388806541/50000000000000000000 : ℝ) ≤ (11656926990684547/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (94560567938388806541/50000000000000000000 : ℝ)^32 ≤ (11656926990684547/10000000000000000 : ℝ)^133 := by
      have hnat : (94560567938388806541 : ℕ)^32*10000000000000000^133 ≤ 11656926990684547^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94560567938388806541 50000000000000000000 11656926990684547 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11656926990684547/10000000000000000 : ℝ)) (X := (94560567938388806541/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(231795858226267/2058150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(729743557779479/8232600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (41163/50000 : ℝ)) (alpha := (231795858226267/2058150000000000 : ℝ)) (beta := (729743557779479/8232600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (41163/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(231795858226267/2058150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(729743557779479/8232600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-680905999/2000000000 : ℝ)*X 0 0+(563255001/1000000000 : ℝ)*X 0 1+(3864347799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((3065090087/5000000000 : ℝ)*X 1 0+(-269569827/5000000000 : ℝ)*X 1 1+(218793981/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-841550427/2500000000 : ℝ)*X 0 0+(5722607603/10000000000 : ℝ)*X 0 1+(1899667307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((233913903/400000000 : ℝ)*X 1 0+(720803/5000000000 : ℝ)*X 1 1+(5952083543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((86319017/312500000 : ℝ)*X 2 0+(6771822273/10000000000 : ℝ)*X 2 1+(-155881249/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((402220857/1000000000 : ℝ)*X 0 0+(973606623/2000000000 : ℝ)*X 0 1+(51173789/125000000 : ℝ)*X 0 2+(402220857/1000000000 : ℝ)*X 1 0+(973606623/2000000000 : ℝ)*X 1 1+(51173789/125000000 : ℝ)*X 1 2+(402220857/1000000000 : ℝ)*X 2 0+(973606623/2000000000 : ℝ)*X 2 1+(51173789/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-820977899/2000000000 : ℝ)*X 0 0+(1118668459/2000000000 : ℝ)*X 0 1+(3195652427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1438660683/2500000000 : ℝ)*X 1 0+(-88132093/2000000000 : ℝ)*X 1 1+(5896317091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2487326889/10000000000 : ℝ)*X 2 0+(3027831543/5000000000 : ℝ)*X 2 1+(-527403893/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((2584424963/5000000000 : ℝ)*X 0 0+(4569970041/10000000000 : ℝ)*X 0 1+(636738953/2000000000 : ℝ)*X 0 2+(2584424963/5000000000 : ℝ)*X 1 0+(4569970041/10000000000 : ℝ)*X 1 1+(636738953/2000000000 : ℝ)*X 1 2+(2584424963/5000000000 : ℝ)*X 2 0+(4569970041/10000000000 : ℝ)*X 2 1+(636738953/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-741518887/2500000000 : ℝ)*X 0 0+(5978657777/10000000000 : ℝ)*X 0 1+(242730447/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6893302261/10000000000 : ℝ)*X 1 0+(9/2000000000 : ℝ)*X 1 1+(2425511481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((635296387/2500000000 : ℝ)*X 2 0+(677038087/1000000000 : ℝ)*X 2 1+(-332734939/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((1264574113/2500000000 : ℝ)*X 0 0+(4340938917/10000000000 : ℝ)*X 0 1+(3559674493/10000000000 : ℝ)*X 0 2+(1264574113/2500000000 : ℝ)*X 1 0+(4340938917/10000000000 : ℝ)*X 1 1+(3559674493/10000000000 : ℝ)*X 1 2+(1264574113/2500000000 : ℝ)*X 2 0+(4340938917/10000000000 : ℝ)*X 2 1+(3559674493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305080_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((8551/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8551/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (71711662072049819431877343/7155397790000000000000000000000 : ℝ) := by norm_num
    linear_combination (3778622577/500000000000 : ℝ)*(base40) + (3420222283329/1000000000000 : ℝ)*(base49) + (178649934913/125000000000 : ℝ)*(base50) + (966331/500000000000 : ℝ)*(base60) + (1712019360297/250000000000 : ℝ)*(major_s2_0) + (1712019360297/250000000000 : ℝ)*(major_s2_1) + (1712019360297/250000000000 : ℝ)*(major_s2_2) + (4609084204339/500000000000 : ℝ)*(sp_s2_7) + (2304519168949/250000000000 : ℝ)*(sp_s2_8) + (576122521951/62500000000 : ℝ)*(sp_s2_9) + (4477974890921/1000000000000 : ℝ)*(sp_s2_12) + (99974973/1000000000000 : ℝ)*(sp_s2_14) + (2060523/250000000000 : ℝ)*(sp_s2_20) + (108149777/500000000000 : ℝ)*(sp_s2_22) + (4477974890921/1000000000000 : ℝ)*(f.failure) + (921817665077/100000000000 : ℝ)*(f.sum) + (1251603069584977361/6679039775000000000000000000000 : ℝ)*base62 + (4250087552693/85756250000000000000000000 : ℝ)*base64 + (166622048169699/486775000000000000000000000 : ℝ)*base67 + (369636408070301/343025000000000000000000000 : ℝ)*base69 + (2031216081422254419/12605825725000000000000000000000 : ℝ)*base71 + (747599550454811/1837450000000000000000000000 : ℝ)*base73 + (154700519872847/486775000000000000000000000 : ℝ)*base74 + (266063444507991/459362500000000000000000000 : ℝ)*base77 + (3167257953252899/17469232885742187500000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1041/3125000000000000 : ℝ)*base86 + (1041/3125000000000000 : ℝ)*base88 + (1041/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((10557/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(10557/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (708757317402572977484336349491/49089606538295000000000000000000000 : ℝ) := by norm_num
    linear_combination (97470954613/500000000000 : ℝ)*(base40) + (901920777147/1000000000000 : ℝ)*(base49) + (657119/200000000000 : ℝ)*(base60) + (286142994337/100000000000 : ℝ)*(major_s2_0) + (286142994337/100000000000 : ℝ)*(major_s2_1) + (286142994337/100000000000 : ℝ)*(major_s2_2) + (2005263/1000000000000 : ℝ)*(sp_s2_0) + (258443461/1000000000000 : ℝ)*(sp_s2_1) + (129521333/1000000000000 : ℝ)*(sp_s2_8) + (3851756903689/1000000000000 : ℝ)*(sp_s2_13) + (3851370944159/1000000000000 : ℝ)*(sp_s2_14) + (481469863619/125000000000 : ℝ)*(sp_s2_15) + (935327702413/500000000000 : ℝ)*(sp_s2_19) + (440760277/1000000000000 : ℝ)*(sp_s2_25) + (116943510319/62500000000 : ℝ)*(f.failure) + (481469863619/125000000000 : ℝ)*(f.sum) + (1092647741715200881/4007423865000000000000000000000 : ℝ)*base63 + (620370040046663/823260000000000000000000000 : ℝ)*base65 + (16224808007301/24338750000000000000000000 : ℝ)*base67 + (138240454291367/411630000000000000000000000 : ℝ)*base69 + (810126630248273063/7563495435000000000000000000000 : ℝ)*base70 + (220340606129027/367490000000000000000000000 : ℝ)*base73 + (6752181502473/9735500000000000000000000 : ℝ)*base75 + (295975044517573/734980000000000000000000000 : ℝ)*base77 + (3864732303009666877/7155397790000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (383/1562500000000000 : ℝ)*base87 + (383/1562500000000000 : ℝ)*base89 + (383/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(983/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(983/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (825172898439983437931034317031/98179213076590000000000000000000000 : ℝ) := by norm_num
    linear_combination (1530801/1000000000000 : ℝ)*(base23) + (385050562697/500000000000 : ℝ)*(base40) + (325703371203/100000000000 : ℝ)*(base49) + (1098966100147/1000000000000 : ℝ)*(base50) + (181381/125000000000 : ℝ)*(base59) + (684717679197/100000000000 : ℝ)*(major_s2_0) + (684717679197/100000000000 : ℝ)*(major_s2_1) + (684717679197/100000000000 : ℝ)*(major_s2_2) + (18737499/500000000000 : ℝ)*(sp_s2_0) + (24310673/125000000000 : ℝ)*(sp_s2_19) + (9216927353191/1000000000000 : ℝ)*(sp_s2_20) + (2304241207047/250000000000 : ℝ)*(sp_s2_21) + (2304240824347/250000000000 : ℝ)*(sp_s2_22) + (447719146877/100000000000 : ℝ)*(sp_s2_25) + (895477190831/200000000000 : ℝ)*(f.failure) + (2304241207047/250000000000 : ℝ)*(f.sum) + (566035506048742857/667903977500000000000000000000 : ℝ)*base63 + (198429511703439/274420000000000000000000000 : ℝ)*base65 + (23861870453021/38942000000000000000000000 : ℝ)*base67 + (73707864786067/68605000000000000000000000 : ℝ)*base69 + (1257864984955109007/1260582572500000000000000000000 : ℝ)*base71 + (196668304304129/367490000000000000000000000 : ℝ)*base73 + (9256118157933/9735500000000000000000000 : ℝ)*base75 + (455364526581987/734980000000000000000000000 : ℝ)*base77 + (97451203347040489/447212361875000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (99/625000000000000 : ℝ)*base87 + (99/625000000000000 : ℝ)*base89 + (99/625000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((36749/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36749/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((19471/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(19471/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41163/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41163/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8551/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8551/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10557/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(10557/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(983/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(983/2000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305080_s2 p hpa hpb X hX hprev1

#print axioms solution

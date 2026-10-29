-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:39:32.833977+00:00
-- url     : https://prove2.me/submissions/aabac07c-8e54-4cdb-bde4-4fa51bec2143

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
theorem collision_support_c308063_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-116022129/2000000000 : ℝ)*x 0 + (5638497621/10000000000 : ℝ)*x 1 + (5882217703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116022129/2000000000 : ℝ)^69 ≤ (2456015406791/100000000000000 : ℝ)^53 := by
    have hnat : (116022129 : ℕ)^69*100000000000000^53 ≤ 2456015406791^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116022129 2000000000 2456015406791 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5638497621/10000000000 : ℝ)^69 ≤ (47428885434697/100000000000000 : ℝ)^53 := by
    have hnat : (5638497621 : ℕ)^69*100000000000000^53 ≤ 47428885434697^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638497621 10000000000 47428885434697 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5882217703/10000000000 : ℝ)^69 ≤ (31321936967/62500000000 : ℝ)^53 := by
    have hnat : (5882217703 : ℕ)^69*62500000000^53 ≤ 31321936967^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5882217703 10000000000 31321936967 62500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116022129/2000000000 : ℝ), (5638497621/10000000000 : ℝ), (5882217703/10000000000 : ℝ)] ![(2456015406791/100000000000000 : ℝ), (47428885434697/100000000000000 : ℝ), (31321936967/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116022129/2000000000 : ℝ)|^69 ≤ (2456015406791/100000000000000 : ℝ)^53
        have hw : |(-116022129/2000000000 : ℝ)|=(116022129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5638497621/10000000000 : ℝ)|^69 ≤ (47428885434697/100000000000000 : ℝ)^53
        have hw : |(5638497621/10000000000 : ℝ)|=(5638497621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5882217703/10000000000 : ℝ)|^69 ≤ (31321936967/62500000000 : ℝ)^53
        have hw : |(5882217703/10000000000 : ℝ)|=(5882217703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1127663503/2000000000 : ℝ)*x 0 + (-575786661/10000000000 : ℝ)*x 1 + (2942270833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127663503/2000000000 : ℝ)^69 ≤ (23713456554063/50000000000000 : ℝ)^53 := by
    have hnat : (1127663503 : ℕ)^69*50000000000000^53 ≤ 23713456554063^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127663503 2000000000 23713456554063 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575786661/10000000000 : ℝ)^69 ≤ (608052332849/25000000000000 : ℝ)^53 := by
    have hnat : (575786661 : ℕ)^69*25000000000000^53 ≤ 608052332849^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575786661 10000000000 608052332849 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2942270833/5000000000 : ℝ)^69 ≤ (50140877539381/100000000000000 : ℝ)^53 := by
    have hnat : (2942270833 : ℕ)^69*100000000000000^53 ≤ 50140877539381^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2942270833 5000000000 50140877539381 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1127663503/2000000000 : ℝ), (-575786661/10000000000 : ℝ), (2942270833/5000000000 : ℝ)] ![(23713456554063/50000000000000 : ℝ), (608052332849/25000000000000 : ℝ), (50140877539381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1127663503/2000000000 : ℝ)|^69 ≤ (23713456554063/50000000000000 : ℝ)^53
        have hw : |(1127663503/2000000000 : ℝ)|=(1127663503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-575786661/10000000000 : ℝ)|^69 ≤ (608052332849/25000000000000 : ℝ)^53
        have hw : |(-575786661/10000000000 : ℝ)|=(575786661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2942270833/5000000000 : ℝ)|^69 ≤ (50140877539381/100000000000000 : ℝ)^53
        have hw : |(2942270833/5000000000 : ℝ)|=(2942270833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5704288353/10000000000 : ℝ)*x 0 + (292655377/500000000 : ℝ)*x 1 + (-126559643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5704288353/10000000000 : ℝ)^69 ≤ (9630124700501/20000000000000 : ℝ)^53 := by
    have hnat : (5704288353 : ℕ)^69*20000000000000^53 ≤ 9630124700501^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704288353 10000000000 9630124700501 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292655377/500000000 : ℝ)^69 ≤ (49792457484769/100000000000000 : ℝ)^53 := by
    have hnat : (292655377 : ℕ)^69*100000000000000^53 ≤ 49792457484769^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292655377 500000000 49792457484769 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126559643/2500000000 : ℝ)^69 ≤ (2056918997899/100000000000000 : ℝ)^53 := by
    have hnat : (126559643 : ℕ)^69*100000000000000^53 ≤ 2056918997899^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126559643 2500000000 2056918997899 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5704288353/10000000000 : ℝ), (292655377/500000000 : ℝ), (-126559643/2500000000 : ℝ)] ![(9630124700501/20000000000000 : ℝ), (49792457484769/100000000000000 : ℝ), (2056918997899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5704288353/10000000000 : ℝ)|^69 ≤ (9630124700501/20000000000000 : ℝ)^53
        have hw : |(5704288353/10000000000 : ℝ)|=(5704288353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292655377/500000000 : ℝ)|^69 ≤ (49792457484769/100000000000000 : ℝ)^53
        have hw : |(292655377/500000000 : ℝ)|=(292655377/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126559643/2500000000 : ℝ)|^69 ≤ (2056918997899/100000000000000 : ℝ)^53
        have hw : |(-126559643/2500000000 : ℝ)|=(126559643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1166490431/2500000000 : ℝ)*x 0 + (434226043/1000000000 : ℝ)*x 1 + (485279/1250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1166490431/2500000000 : ℝ)^69 ≤ (7413595386861/20000000000000 : ℝ)^53 := by
    have hnat : (1166490431 : ℕ)^69*20000000000000^53 ≤ 7413595386861^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166490431 2500000000 7413595386861 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434226043/1000000000 : ℝ)^69 ≤ (6751139279503/20000000000000 : ℝ)^53 := by
    have hnat : (434226043 : ℕ)^69*20000000000000^53 ≤ 6751139279503^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434226043 1000000000 6751139279503 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485279/1250000 : ℝ)^69 ≤ (29176326650193/100000000000000 : ℝ)^53 := by
    have hnat : (485279 : ℕ)^69*100000000000000^53 ≤ 29176326650193^53*1250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485279 1250000 29176326650193 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1166490431/2500000000 : ℝ), (434226043/1000000000 : ℝ), (485279/1250000 : ℝ)] ![(7413595386861/20000000000000 : ℝ), (6751139279503/20000000000000 : ℝ), (29176326650193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1166490431/2500000000 : ℝ)|^69 ≤ (7413595386861/20000000000000 : ℝ)^53
        have hw : |(1166490431/2500000000 : ℝ)|=(1166490431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(434226043/1000000000 : ℝ)|^69 ≤ (6751139279503/20000000000000 : ℝ)^53
        have hw : |(434226043/1000000000 : ℝ)|=(434226043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485279/1250000 : ℝ)|^69 ≤ (29176326650193/100000000000000 : ℝ)^53
        have hw : |(485279/1250000 : ℝ)|=(485279/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-986444417/10000000000 : ℝ)*x 0 + (273841509/1000000000 : ℝ)*x 1 + (8146454311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986444417/10000000000 : ℝ)^69 ≤ (2451130494561/50000000000000 : ℝ)^53 := by
    have hnat : (986444417 : ℕ)^69*50000000000000^53 ≤ 2451130494561^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986444417 10000000000 2451130494561 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273841509/1000000000 : ℝ)^69 ≤ (18521994077119/100000000000000 : ℝ)^53 := by
    have hnat : (273841509 : ℕ)^69*100000000000000^53 ≤ 18521994077119^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273841509 1000000000 18521994077119 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8146454311/10000000000 : ℝ)^69 ≤ (76575744917511/100000000000000 : ℝ)^53 := by
    have hnat : (8146454311 : ℕ)^69*100000000000000^53 ≤ 76575744917511^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8146454311 10000000000 76575744917511 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986444417/10000000000 : ℝ), (273841509/1000000000 : ℝ), (8146454311/10000000000 : ℝ)] ![(2451130494561/50000000000000 : ℝ), (18521994077119/100000000000000 : ℝ), (76575744917511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986444417/10000000000 : ℝ)|^69 ≤ (2451130494561/50000000000000 : ℝ)^53
        have hw : |(-986444417/10000000000 : ℝ)|=(986444417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273841509/1000000000 : ℝ)|^69 ≤ (18521994077119/100000000000000 : ℝ)^53
        have hw : |(273841509/1000000000 : ℝ)|=(273841509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8146454311/10000000000 : ℝ)|^69 ≤ (76575744917511/100000000000000 : ℝ)^53
        have hw : |(8146454311/10000000000 : ℝ)|=(8146454311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1613651527/5000000000 : ℝ)*x 0 + (-157356071/10000000000 : ℝ)*x 1 + (1629886499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613651527/5000000000 : ℝ)^69 ≤ (22938496893051/100000000000000 : ℝ)^53 := by
    have hnat : (1613651527 : ℕ)^69*100000000000000^53 ≤ 22938496893051^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613651527 5000000000 22938496893051 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157356071/10000000000 : ℝ)^69 ≤ (449310375623/100000000000000 : ℝ)^53 := by
    have hnat : (157356071 : ℕ)^69*100000000000000^53 ≤ 449310375623^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157356071 10000000000 449310375623 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1629886499/2000000000 : ℝ)^69 ≤ (38306096358527/50000000000000 : ℝ)^53 := by
    have hnat : (1629886499 : ℕ)^69*50000000000000^53 ≤ 38306096358527^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629886499 2000000000 38306096358527 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1613651527/5000000000 : ℝ), (-157356071/10000000000 : ℝ), (1629886499/2000000000 : ℝ)] ![(22938496893051/100000000000000 : ℝ), (449310375623/100000000000000 : ℝ), (38306096358527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1613651527/5000000000 : ℝ)|^69 ≤ (22938496893051/100000000000000 : ℝ)^53
        have hw : |(1613651527/5000000000 : ℝ)|=(1613651527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-157356071/10000000000 : ℝ)|^69 ≤ (449310375623/100000000000000 : ℝ)^53
        have hw : |(-157356071/10000000000 : ℝ)|=(157356071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1629886499/2000000000 : ℝ)|^69 ≤ (38306096358527/50000000000000 : ℝ)^53
        have hw : |(1629886499/2000000000 : ℝ)|=(1629886499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1586052531/5000000000 : ℝ)*x 0 + (8221361111/10000000000 : ℝ)*x 1 + (-4069613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1586052531/5000000000 : ℝ)^69 ≤ (22429055119179/100000000000000 : ℝ)^53 := by
    have hnat : (1586052531 : ℕ)^69*100000000000000^53 ≤ 22429055119179^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586052531 5000000000 22429055119179 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8221361111/10000000000 : ℝ)^69 ≤ (77493693040379/100000000000000 : ℝ)^53 := by
    have hnat : (8221361111 : ℕ)^69*100000000000000^53 ≤ 77493693040379^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8221361111 10000000000 77493693040379 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4069613/1000000000 : ℝ)^69 ≤ (77251828623/100000000000000 : ℝ)^53 := by
    have hnat : (4069613 : ℕ)^69*100000000000000^53 ≤ 77251828623^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4069613 1000000000 77251828623 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1586052531/5000000000 : ℝ), (8221361111/10000000000 : ℝ), (-4069613/1000000000 : ℝ)] ![(22429055119179/100000000000000 : ℝ), (77493693040379/100000000000000 : ℝ), (77251828623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1586052531/5000000000 : ℝ)|^69 ≤ (22429055119179/100000000000000 : ℝ)^53
        have hw : |(1586052531/5000000000 : ℝ)|=(1586052531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8221361111/10000000000 : ℝ)|^69 ≤ (77493693040379/100000000000000 : ℝ)^53
        have hw : |(8221361111/10000000000 : ℝ)|=(8221361111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4069613/1000000000 : ℝ)|^69 ≤ (77251828623/100000000000000 : ℝ)^53
        have hw : |(-4069613/1000000000 : ℝ)|=(4069613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (653602749/2000000000 : ℝ)*x 0 + (7310873001/10000000000 : ℝ)*x 1 + (864029901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653602749/2000000000 : ℝ)^69 ≤ (4663184373283/20000000000000 : ℝ)^53 := by
    have hnat : (653602749 : ℕ)^69*20000000000000^53 ≤ 4663184373283^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653602749 2000000000 4663184373283 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7310873001/10000000000 : ℝ)^69 ≤ (66512511931521/100000000000000 : ℝ)^53 := by
    have hnat : (7310873001 : ℕ)^69*100000000000000^53 ≤ 66512511931521^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7310873001 10000000000 66512511931521 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864029901/5000000000 : ℝ)^69 ≤ (10171566194989/100000000000000 : ℝ)^53 := by
    have hnat : (864029901 : ℕ)^69*100000000000000^53 ≤ 10171566194989^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864029901 5000000000 10171566194989 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653602749/2000000000 : ℝ), (7310873001/10000000000 : ℝ), (864029901/5000000000 : ℝ)] ![(4663184373283/20000000000000 : ℝ), (66512511931521/100000000000000 : ℝ), (10171566194989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653602749/2000000000 : ℝ)|^69 ≤ (4663184373283/20000000000000 : ℝ)^53
        have hw : |(653602749/2000000000 : ℝ)|=(653602749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7310873001/10000000000 : ℝ)|^69 ≤ (66512511931521/100000000000000 : ℝ)^53
        have hw : |(7310873001/10000000000 : ℝ)|=(7310873001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864029901/5000000000 : ℝ)|^69 ≤ (10171566194989/100000000000000 : ℝ)^53
        have hw : |(864029901/5000000000 : ℝ)|=(864029901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-62022723/5000000000 : ℝ)*x 0 + (125833537/400000000 : ℝ)*x 1 + (411023589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62022723/5000000000 : ℝ)^69 ≤ (65930755259/20000000000000 : ℝ)^53 := by
    have hnat : (62022723 : ℕ)^69*20000000000000^53 ≤ 65930755259^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62022723 5000000000 65930755259 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125833537/400000000 : ℝ)^69 ≤ (22187566371811/100000000000000 : ℝ)^53 := by
    have hnat : (125833537 : ℕ)^69*100000000000000^53 ≤ 22187566371811^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125833537 400000000 22187566371811 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411023589/500000000 : ℝ)^69 ≤ (77482779838363/100000000000000 : ℝ)^53 := by
    have hnat : (411023589 : ℕ)^69*100000000000000^53 ≤ 77482779838363^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411023589 500000000 77482779838363 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62022723/5000000000 : ℝ), (125833537/400000000 : ℝ), (411023589/500000000 : ℝ)] ![(65930755259/20000000000000 : ℝ), (22187566371811/100000000000000 : ℝ), (77482779838363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62022723/5000000000 : ℝ)|^69 ≤ (65930755259/20000000000000 : ℝ)^53
        have hw : |(-62022723/5000000000 : ℝ)|=(62022723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125833537/400000000 : ℝ)|^69 ≤ (22187566371811/100000000000000 : ℝ)^53
        have hw : |(125833537/400000000 : ℝ)|=(125833537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(411023589/500000000 : ℝ)|^69 ≤ (77482779838363/100000000000000 : ℝ)^53
        have hw : |(411023589/500000000 : ℝ)|=(411023589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (329933337/1250000000 : ℝ)*x 0 + (-974440749/10000000000 : ℝ)*x 1 + (8223486607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329933337/1250000000 : ℝ)^69 ≤ (1765548139919/10000000000000 : ℝ)^53 := by
    have hnat : (329933337 : ℕ)^69*10000000000000^53 ≤ 1765548139919^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329933337 1250000000 1765548139919 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974440749/10000000000 : ℝ)^69 ≤ (4824741607941/100000000000000 : ℝ)^53 := by
    have hnat : (974440749 : ℕ)^69*100000000000000^53 ≤ 4824741607941^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974440749 10000000000 4824741607941 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8223486607/10000000000 : ℝ)^69 ≤ (3100791078977/4000000000000 : ℝ)^53 := by
    have hnat : (8223486607 : ℕ)^69*4000000000000^53 ≤ 3100791078977^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8223486607 10000000000 3100791078977 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329933337/1250000000 : ℝ), (-974440749/10000000000 : ℝ), (8223486607/10000000000 : ℝ)] ![(1765548139919/10000000000000 : ℝ), (4824741607941/100000000000000 : ℝ), (3100791078977/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329933337/1250000000 : ℝ)|^69 ≤ (1765548139919/10000000000000 : ℝ)^53
        have hw : |(329933337/1250000000 : ℝ)|=(329933337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974440749/10000000000 : ℝ)|^69 ≤ (4824741607941/100000000000000 : ℝ)^53
        have hw : |(-974440749/10000000000 : ℝ)|=(974440749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8223486607/10000000000 : ℝ)|^69 ≤ (3100791078977/4000000000000 : ℝ)^53
        have hw : |(8223486607/10000000000 : ℝ)|=(8223486607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1604908551/2000000000 : ℝ)*x 0 + (171205763/500000000 : ℝ)*x 1 + (-788043/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1604908551/2000000000 : ℝ)^69 ≤ (7508722335153/10000000000000 : ℝ)^53 := by
    have hnat : (1604908551 : ℕ)^69*10000000000000^53 ≤ 7508722335153^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604908551 2000000000 7508722335153 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171205763/500000000 : ℝ)^69 ≤ (24776198800549/100000000000000 : ℝ)^53 := by
    have hnat : (171205763 : ℕ)^69*100000000000000^53 ≤ 24776198800549^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171205763 500000000 24776198800549 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788043/125000000 : ℝ)^69 ≤ (68288921669/50000000000000 : ℝ)^53 := by
    have hnat : (788043 : ℕ)^69*50000000000000^53 ≤ 68288921669^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788043 125000000 68288921669 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1604908551/2000000000 : ℝ), (171205763/500000000 : ℝ), (-788043/125000000 : ℝ)] ![(7508722335153/10000000000000 : ℝ), (24776198800549/100000000000000 : ℝ), (68288921669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1604908551/2000000000 : ℝ)|^69 ≤ (7508722335153/10000000000000 : ℝ)^53
        have hw : |(1604908551/2000000000 : ℝ)|=(1604908551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171205763/500000000 : ℝ)|^69 ≤ (24776198800549/100000000000000 : ℝ)^53
        have hw : |(171205763/500000000 : ℝ)|=(171205763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-788043/125000000 : ℝ)|^69 ≤ (68288921669/50000000000000 : ℝ)^53
        have hw : |(-788043/125000000 : ℝ)|=(788043/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7642271423/10000000000 : ℝ)*x 0 + (142179011/500000000 : ℝ)*x 1 + (858204919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7642271423/10000000000 : ℝ)^69 ≤ (17616063581739/25000000000000 : ℝ)^53 := by
    have hnat : (7642271423 : ℕ)^69*25000000000000^53 ≤ 17616063581739^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7642271423 10000000000 17616063581739 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142179011/500000000 : ℝ)^69 ≤ (9726681426043/50000000000000 : ℝ)^53 := by
    have hnat : (142179011 : ℕ)^69*50000000000000^53 ≤ 9726681426043^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142179011 500000000 9726681426043 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (858204919/5000000000 : ℝ)^69 ≤ (2016476559851/20000000000000 : ℝ)^53 := by
    have hnat : (858204919 : ℕ)^69*20000000000000^53 ≤ 2016476559851^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858204919 5000000000 2016476559851 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7642271423/10000000000 : ℝ), (142179011/500000000 : ℝ), (858204919/5000000000 : ℝ)] ![(17616063581739/25000000000000 : ℝ), (9726681426043/50000000000000 : ℝ), (2016476559851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7642271423/10000000000 : ℝ)|^69 ≤ (17616063581739/25000000000000 : ℝ)^53
        have hw : |(7642271423/10000000000 : ℝ)|=(7642271423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142179011/500000000 : ℝ)|^69 ≤ (9726681426043/50000000000000 : ℝ)^53
        have hw : |(142179011/500000000 : ℝ)|=(142179011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(858204919/5000000000 : ℝ)|^69 ≤ (2016476559851/20000000000000 : ℝ)^53
        have hw : |(858204919/5000000000 : ℝ)|=(858204919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-15196353/1000000000 : ℝ)*x 0 + (7423572381/10000000000 : ℝ)*x 1 + (827938371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15196353/1000000000 : ℝ)^69 ≤ (85873764269/20000000000000 : ℝ)^53 := by
    have hnat : (15196353 : ℕ)^69*20000000000000^53 ≤ 85873764269^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15196353 1000000000 85873764269 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7423572381/10000000000 : ℝ)^69 ≤ (16962611432283/25000000000000 : ℝ)^53 := by
    have hnat : (7423572381 : ℕ)^69*25000000000000^53 ≤ 16962611432283^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7423572381 10000000000 16962611432283 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827938371/2000000000 : ℝ)^69 ≤ (15860092715969/50000000000000 : ℝ)^53 := by
    have hnat : (827938371 : ℕ)^69*50000000000000^53 ≤ 15860092715969^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827938371 2000000000 15860092715969 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15196353/1000000000 : ℝ), (7423572381/10000000000 : ℝ), (827938371/2000000000 : ℝ)] ![(85873764269/20000000000000 : ℝ), (16962611432283/25000000000000 : ℝ), (15860092715969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15196353/1000000000 : ℝ)|^69 ≤ (85873764269/20000000000000 : ℝ)^53
        have hw : |(-15196353/1000000000 : ℝ)|=(15196353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7423572381/10000000000 : ℝ)|^69 ≤ (16962611432283/25000000000000 : ℝ)^53
        have hw : |(7423572381/10000000000 : ℝ)|=(7423572381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827938371/2000000000 : ℝ)|^69 ≤ (15860092715969/50000000000000 : ℝ)^53
        have hw : |(827938371/2000000000 : ℝ)|=(827938371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7971510429/10000000000 : ℝ)*x 0 + (-9676477/2000000000 : ℝ)*x 1 + (349662271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7971510429/10000000000 : ℝ)^69 ≤ (37220914224401/50000000000000 : ℝ)^53 := by
    have hnat : (7971510429 : ℕ)^69*50000000000000^53 ≤ 37220914224401^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7971510429 10000000000 37220914224401 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9676477/2000000000 : ℝ)^69 ≤ (24191619833/25000000000000 : ℝ)^53 := by
    have hnat : (9676477 : ℕ)^69*25000000000000^53 ≤ 24191619833^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9676477 2000000000 24191619833 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349662271/1000000000 : ℝ)^69 ≤ (6365351264879/25000000000000 : ℝ)^53 := by
    have hnat : (349662271 : ℕ)^69*25000000000000^53 ≤ 6365351264879^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349662271 1000000000 6365351264879 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7971510429/10000000000 : ℝ), (-9676477/2000000000 : ℝ), (349662271/1000000000 : ℝ)] ![(37220914224401/50000000000000 : ℝ), (24191619833/25000000000000 : ℝ), (6365351264879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7971510429/10000000000 : ℝ)|^69 ≤ (37220914224401/50000000000000 : ℝ)^53
        have hw : |(7971510429/10000000000 : ℝ)|=(7971510429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9676477/2000000000 : ℝ)|^69 ≤ (24191619833/25000000000000 : ℝ)^53
        have hw : |(-9676477/2000000000 : ℝ)|=(9676477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(349662271/1000000000 : ℝ)|^69 ≤ (6365351264879/25000000000000 : ℝ)^53
        have hw : |(349662271/1000000000 : ℝ)|=(349662271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (252123217/1000000000 : ℝ)*x 0 + (8350035323/10000000000 : ℝ)*x 1 + (-445237533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252123217/1000000000 : ℝ)^69 ≤ (16632887861517/100000000000000 : ℝ)^53 := by
    have hnat : (252123217 : ℕ)^69*100000000000000^53 ≤ 16632887861517^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252123217 1000000000 16632887861517 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8350035323/10000000000 : ℝ)^69 ≤ (39538214475333/50000000000000 : ℝ)^53 := by
    have hnat : (8350035323 : ℕ)^69*50000000000000^53 ≤ 39538214475333^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8350035323 10000000000 39538214475333 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445237533/5000000000 : ℝ)^69 ≤ (858136633723/20000000000000 : ℝ)^53 := by
    have hnat : (445237533 : ℕ)^69*20000000000000^53 ≤ 858136633723^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445237533 5000000000 858136633723 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252123217/1000000000 : ℝ), (8350035323/10000000000 : ℝ), (-445237533/5000000000 : ℝ)] ![(16632887861517/100000000000000 : ℝ), (39538214475333/50000000000000 : ℝ), (858136633723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252123217/1000000000 : ℝ)|^69 ≤ (16632887861517/100000000000000 : ℝ)^53
        have hw : |(252123217/1000000000 : ℝ)|=(252123217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8350035323/10000000000 : ℝ)|^69 ≤ (39538214475333/50000000000000 : ℝ)^53
        have hw : |(8350035323/10000000000 : ℝ)|=(8350035323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445237533/5000000000 : ℝ)|^69 ≤ (858136633723/20000000000000 : ℝ)^53
        have hw : |(-445237533/5000000000 : ℝ)|=(445237533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7775296623/10000000000 : ℝ)*x 0 + (629143131/2500000000 : ℝ)*x 1 + (1878834107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7775296623/10000000000 : ℝ)^69 ≤ (36032622008711/50000000000000 : ℝ)^53 := by
    have hnat : (7775296623 : ℕ)^69*50000000000000^53 ≤ 36032622008711^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7775296623 10000000000 36032622008711 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629143131/2500000000 : ℝ)^69 ≤ (16592878673137/100000000000000 : ℝ)^53 := by
    have hnat : (629143131 : ℕ)^69*100000000000000^53 ≤ 16592878673137^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629143131 2500000000 16592878673137 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878834107/10000000000 : ℝ)^69 ≤ (2835469322561/25000000000000 : ℝ)^53 := by
    have hnat : (1878834107 : ℕ)^69*25000000000000^53 ≤ 2835469322561^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878834107 10000000000 2835469322561 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7775296623/10000000000 : ℝ), (629143131/2500000000 : ℝ), (1878834107/10000000000 : ℝ)] ![(36032622008711/50000000000000 : ℝ), (16592878673137/100000000000000 : ℝ), (2835469322561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7775296623/10000000000 : ℝ)|^69 ≤ (36032622008711/50000000000000 : ℝ)^53
        have hw : |(7775296623/10000000000 : ℝ)|=(7775296623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629143131/2500000000 : ℝ)|^69 ≤ (16592878673137/100000000000000 : ℝ)^53
        have hw : |(629143131/2500000000 : ℝ)|=(629143131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1878834107/10000000000 : ℝ)|^69 ≤ (2835469322561/25000000000000 : ℝ)^53
        have hw : |(1878834107/10000000000 : ℝ)|=(1878834107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308063_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((41783/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41783/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83403/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2019/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2019/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((74101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37149/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37149/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35777/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35777/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (41783/50000 : ℝ) ^ (17/4 : ℝ) ≤ (46625753348696091539/100000000000000000000 : ℝ) := by
    have hpowers : (41783/50000 : ℝ)^17 ≤ (46625753348696091539/100000000000000000000 : ℝ)^4 := by
      have hnat : (41783 : ℕ)^17*100000000000000000000^4 ≤ 46625753348696091539^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41783 50000 46625753348696091539 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41783/50000 : ℝ)) (X := (46625753348696091539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (146625753348696091539/100000000000000000000 : ℝ) ≤ (437691675671171/400000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (146625753348696091539/100000000000000000000 : ℝ)^4 ≤ (437691675671171/400000000000000 : ℝ)^17 := by
      have hnat : (146625753348696091539 : ℕ)^4*400000000000000^17 ≤ 437691675671171^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146625753348696091539 100000000000000000000 437691675671171 400000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (437691675671171/400000000000000 : ℝ)) (X := (146625753348696091539/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (96625753348696091539/50000000000000000000 : ℝ) ≤ (11676778246668731/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (96625753348696091539/50000000000000000000 : ℝ)^4 ≤ (11676778246668731/10000000000000000 : ℝ)^17 := by
      have hnat : (96625753348696091539 : ℕ)^4*10000000000000000^17 ≤ 11676778246668731^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96625753348696091539 50000000000000000000 11676778246668731 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11676778246668731/10000000000000000 : ℝ)) (X := (96625753348696091539/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(37691675671171/334264000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(45905397180591/522287500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (41783/50000 : ℝ)) (alpha := (37691675671171/334264000000000 : ℝ)) (beta := (45905397180591/522287500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (41783/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(37691675671171/334264000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(45905397180591/522287500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (83403/100000 : ℝ) ^ (17/4 : ℝ) ≤ (23120227985660812463/50000000000000000000 : ℝ) := by
    have hpowers : (83403/100000 : ℝ)^17 ≤ (23120227985660812463/50000000000000000000 : ℝ)^4 := by
      have hnat : (83403 : ℕ)^17*50000000000000000000^4 ≤ 23120227985660812463^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83403 100000 23120227985660812463 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83403/100000 : ℝ)) (X := (23120227985660812463/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (73120227985660812463/50000000000000000000 : ℝ) ≤ (10935519501658383/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (73120227985660812463/50000000000000000000 : ℝ)^4 ≤ (10935519501658383/10000000000000000 : ℝ)^17 := by
      have hnat : (73120227985660812463 : ℕ)^4*10000000000000000^17 ≤ 10935519501658383^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73120227985660812463 50000000000000000000 10935519501658383 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10935519501658383/10000000000000000 : ℝ)) (X := (73120227985660812463/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (48120227985660812463/25000000000000000000 : ℝ) ≤ (5832902938177479/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (48120227985660812463/25000000000000000000 : ℝ)^4 ≤ (5832902938177479/5000000000000000 : ℝ)^17 := by
      have hnat : (48120227985660812463 : ℕ)^4*5000000000000000^17 ≤ 5832902938177479^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48120227985660812463 25000000000000000000 5832902938177479 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832902938177479/5000000000000000 : ℝ)) (X := (48120227985660812463/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(935519501658383/8340300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(9737151662621/111204000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (83403/100000 : ℝ)) (alpha := (935519501658383/8340300000000000 : ℝ)) (beta := (9737151662621/111204000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (83403/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(935519501658383/8340300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(9737151662621/111204000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (2019/2500 : ℝ) ^ (17/4 : ℝ) ≤ (40325923197694936221/100000000000000000000 : ℝ) := by
    have hpowers : (2019/2500 : ℝ)^17 ≤ (40325923197694936221/100000000000000000000 : ℝ)^4 := by
      have hnat : (2019 : ℕ)^17*100000000000000000000^4 ≤ 40325923197694936221^4*2500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2019 2500 40325923197694936221 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2019/2500 : ℝ)) (X := (40325923197694936221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (140325923197694936221/100000000000000000000 : ℝ) ≤ (5414903091141269/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (140325923197694936221/100000000000000000000 : ℝ)^4 ≤ (5414903091141269/5000000000000000 : ℝ)^17 := by
      have hnat : (140325923197694936221 : ℕ)^4*5000000000000000^17 ≤ 5414903091141269^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140325923197694936221 100000000000000000000 5414903091141269 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5414903091141269/5000000000000000 : ℝ)) (X := (140325923197694936221/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (90325923197694936221/50000000000000000000 : ℝ) ≤ (229860053082979/200000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (90325923197694936221/50000000000000000000 : ℝ)^4 ≤ (229860053082979/200000000000000 : ℝ)^17 := by
      have hnat : (90325923197694936221 : ℕ)^4*200000000000000^17 ≤ 229860053082979^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90325923197694936221 50000000000000000000 229860053082979 200000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (229860053082979/200000000000000 : ℝ)) (X := (90325923197694936221/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(138301030380423/1346000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(165799117966603/2019000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (2019/2500 : ℝ)) (alpha := (138301030380423/1346000000000000 : ℝ)) (beta := (165799117966603/2019000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2019/2500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(138301030380423/1346000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(165799117966603/2019000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-116022129/2000000000 : ℝ)*X 0 0+(5638497621/10000000000 : ℝ)*X 0 1+(5882217703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1127663503/2000000000 : ℝ)*X 1 0+(-575786661/10000000000 : ℝ)*X 1 1+(2942270833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5704288353/10000000000 : ℝ)*X 2 0+(292655377/500000000 : ℝ)*X 2 1+(-126559643/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1166490431/2500000000 : ℝ)*X 0 0+(434226043/1000000000 : ℝ)*X 0 1+(485279/1250000 : ℝ)*X 0 2+(1166490431/2500000000 : ℝ)*X 1 0+(434226043/1000000000 : ℝ)*X 1 1+(485279/1250000 : ℝ)*X 1 2+(1166490431/2500000000 : ℝ)*X 2 0+(434226043/1000000000 : ℝ)*X 2 1+(485279/1250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-986444417/10000000000 : ℝ)*X 0 0+(273841509/1000000000 : ℝ)*X 0 1+(8146454311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1613651527/5000000000 : ℝ)*X 1 0+(-157356071/10000000000 : ℝ)*X 1 1+(1629886499/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1586052531/5000000000 : ℝ)*X 2 0+(8221361111/10000000000 : ℝ)*X 2 1+(-4069613/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((653602749/2000000000 : ℝ)*X 0 0+(7310873001/10000000000 : ℝ)*X 0 1+(864029901/5000000000 : ℝ)*X 0 2+(653602749/2000000000 : ℝ)*X 1 0+(7310873001/10000000000 : ℝ)*X 1 1+(864029901/5000000000 : ℝ)*X 1 2+(653602749/2000000000 : ℝ)*X 2 0+(7310873001/10000000000 : ℝ)*X 2 1+(864029901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-62022723/5000000000 : ℝ)*X 0 0+(125833537/400000000 : ℝ)*X 0 1+(411023589/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((329933337/1250000000 : ℝ)*X 1 0+(-974440749/10000000000 : ℝ)*X 1 1+(8223486607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1604908551/2000000000 : ℝ)*X 2 0+(171205763/500000000 : ℝ)*X 2 1+(-788043/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7642271423/10000000000 : ℝ)*X 0 0+(142179011/500000000 : ℝ)*X 0 1+(858204919/5000000000 : ℝ)*X 0 2+(7642271423/10000000000 : ℝ)*X 1 0+(142179011/500000000 : ℝ)*X 1 1+(858204919/5000000000 : ℝ)*X 1 2+(7642271423/10000000000 : ℝ)*X 2 0+(142179011/500000000 : ℝ)*X 2 1+(858204919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-15196353/1000000000 : ℝ)*X 0 0+(7423572381/10000000000 : ℝ)*X 0 1+(827938371/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7971510429/10000000000 : ℝ)*X 1 0+(-9676477/2000000000 : ℝ)*X 1 1+(349662271/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((252123217/1000000000 : ℝ)*X 2 0+(8350035323/10000000000 : ℝ)*X 2 1+(-445237533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7775296623/10000000000 : ℝ)*X 0 0+(629143131/2500000000 : ℝ)*X 0 1+(1878834107/10000000000 : ℝ)*X 0 2+(7775296623/10000000000 : ℝ)*X 1 0+(629143131/2500000000 : ℝ)*X 1 1+(1878834107/10000000000 : ℝ)*X 1 2+(7775296623/10000000000 : ℝ)*X 2 0+(629143131/2500000000 : ℝ)*X 2 1+(1878834107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((74101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4186260498802950082078043/233875912500000000000000000000 : ℝ) := by norm_num
    linear_combination (357259706221/500000000000 : ℝ)*(base7) + (2171631/1000000000000 : ℝ)*(base50) + (13787559849/500000000000 : ℝ)*(base60) + (22138571231/12500000000 : ℝ)*(major_s2_0) + (22138571231/12500000000 : ℝ)*(major_s2_1) + (22138571231/12500000000 : ℝ)*(major_s2_2) + (12873131/1000000000000 : ℝ)*(sp_s2_0) + (645657/500000000000 : ℝ)*(sp_s2_6) + (49325194163/25000000000 : ℝ)*(sp_s2_7) + (49327965121/25000000000 : ℝ)*(sp_s2_8) + (3156989231/1600000000 : ℝ)*(sp_s2_9) + (1844678542847/1000000000000 : ℝ)*(sp_s2_13) + (97965189/1000000000000 : ℝ)*(sp_s2_14) + (67093/200000000000 : ℝ)*(sp_s2_23) + (1130160421719/1000000000000 : ℝ)*(f.failure) + (49327965121/25000000000 : ℝ)*(f.sum) + (300073478382511219/350813868750000000000000000000 : ℝ)*base62 + (2593730400587/100950000000000000000000000 : ℝ)*base65 + (97069461916927/278010000000000000000000000 : ℝ)*base66 + (29434551041089/33650000000000000000000000 : ℝ)*base68 + (192847187769875683/602570550000000000000000000000 : ℝ)*base71 + (18873392910447/29845000000000000000000000 : ℝ)*base72 + (656607899105569/834030000000000000000000000 : ℝ)*base74 + (31743067632403/59690000000000000000000000 : ℝ)*base76 + (148078714602760133/829720845000000000000000000000 : ℝ)*base79 + (6209/100000000000000000 : ℝ)*base87 + (6209/100000000000000000 : ℝ)*base89 + (6209/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37149/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37149/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1031256003837515443357161191803/78176298015900000000000000000000000 : ℝ) := by norm_num
    linear_combination (22735314293/31250000000 : ℝ)*(base7) + (672057/1000000000000 : ℝ)*(base39) + (3993/8000000000 : ℝ)*(base49) + (856847078609/500000000000 : ℝ)*(major_s2_0) + (856847078609/500000000000 : ℝ)*(major_s2_1) + (856847078609/500000000000 : ℝ)*(major_s2_2) + (4125931/1000000000000 : ℝ)*(sp_s2_0) + (1965859/1000000000000 : ℝ)*(sp_s2_1) + (10359867/125000000000 : ℝ)*(sp_s2_8) + (75478553699/40000000000 : ℝ)*(sp_s2_14) + (1886883123611/1000000000000 : ℝ)*(sp_s2_15) + (1886967968407/1000000000000 : ℝ)*(sp_s2_16) + (455234830997/250000000000 : ℝ)*(sp_s2_20) + (128619827/1000000000000 : ℝ)*(sp_s2_27) + (1093537886439/1000000000000 : ℝ)*(f.failure) + (1886967968407/1000000000000 : ℝ)*(f.sum) + (14441749341513583241/56130219000000000000000000000000 : ℝ)*base63 + (744717949697927/1009500000000000000000000000 : ℝ)*base65 + (143999357982719/278010000000000000000000000 : ℝ)*base67 + (483863883762607/673000000000000000000000000 : ℝ)*base69 + (2312090398666415483/21089969250000000000000000000000 : ℝ)*base71 + (416643622703473/522287500000000000000000000 : ℝ)*base73 + (1086932693312797/4170150000000000000000000000 : ℝ)*base75 + (273661609876847/835660000000000000000000000 : ℝ)*base77 + (2567910268823639921/7260057393750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (57871/100000000000000000 : ℝ)*base86 + (57871/100000000000000000 : ℝ)*base88 + (57871/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35777/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35777/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11574594000325287052950793331/1663325489700000000000000000000000 : ℝ) := by norm_num
    linear_combination (144730415591/200000000000 : ℝ)*(base7) + (4667953481/40000000000 : ℝ)*(base40) + (26353/125000000000 : ℝ)*(base49) + (3997/62500000000 : ℝ)*(base59) + (826326493297/500000000000 : ℝ)*(major_s2_0) + (826326493297/500000000000 : ℝ)*(major_s2_1) + (826326493297/500000000000 : ℝ)*(major_s2_2) + (7594811/1000000000000 : ℝ)*(sp_s2_1) + (7079137/1000000000000 : ℝ)*(sp_s2_2) + (22712371/500000000000 : ℝ)*(sp_s2_9) + (1806221141723/1000000000000 : ℝ)*(sp_s2_21) + (56444173341/31250000000 : ℝ)*(sp_s2_22) + (451542159461/250000000000 : ℝ)*(sp_s2_23) + (355647707497/200000000000 : ℝ)*(sp_s2_27) + (105458645953/100000000000 : ℝ)*(f.failure) + (1806221141723/1000000000000 : ℝ)*(f.sum) + (15230762089689545747/56130219000000000000000000000000 : ℝ)*base62 + (233327694812759/1009500000000000000000000000 : ℝ)*base64 + (1068454674223/2224080000000000000000000 : ℝ)*base66 + (313688697951769/673000000000000000000000000 : ℝ)*base68 + (1510397829735659/14022585937500000000000000000 : ℝ)*base70 + (12741031837017/44450000000000000000000000 : ℝ)*base72 + (2756982420991249/4170150000000000000000000000 : ℝ)*base74 + (7273689956027/17780000000000000000000000 : ℝ)*base76 + (58615015484884931/617877225000000000000000000000 : ℝ)*base78 + (583/10000000000000000 : ℝ)*base87 + (583/10000000000000000 : ℝ)*base89 + (583/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((41783/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41783/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83403/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2019/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2019/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((74101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37149/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37149/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35777/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35777/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308063_s2 p hpa hpb X hX hprev1

#print axioms solution

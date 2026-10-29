-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312036_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:17:19.760258+00:00
-- url     : https://prove2.me/submissions/95fcfa3e-9b6c-4a26-bc9e-d56d534315a5

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
theorem collision_support_c312036_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-505896077/10000000000 : ℝ)*x 0 + (-2865189993/5000000000 : ℝ)*x 1 + (-355231389/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505896077/10000000000 : ℝ)^37 ≤ (1110531772189/50000000000000 : ℝ)^29 := by
    have hnat : (505896077 : ℕ)^37*50000000000000^29 ≤ 1110531772189^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505896077 10000000000 1110531772189 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2865189993/5000000000 : ℝ)^37 ≤ (49144554174933/100000000000000 : ℝ)^29 := by
    have hnat : (2865189993 : ℕ)^37*100000000000000^29 ≤ 49144554174933^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2865189993 5000000000 49144554174933 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355231389/625000000 : ℝ)^37 ≤ (24317191131551/50000000000000 : ℝ)^29 := by
    have hnat : (355231389 : ℕ)^37*50000000000000^29 ≤ 24317191131551^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355231389 625000000 24317191131551 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505896077/10000000000 : ℝ), (-2865189993/5000000000 : ℝ), (-355231389/625000000 : ℝ)] ![(1110531772189/50000000000000 : ℝ), (49144554174933/100000000000000 : ℝ), (24317191131551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505896077/10000000000 : ℝ)|^37 ≤ (1110531772189/50000000000000 : ℝ)^29
        have hw : |(-505896077/10000000000 : ℝ)|=(505896077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2865189993/5000000000 : ℝ)|^37 ≤ (49144554174933/100000000000000 : ℝ)^29
        have hw : |(-2865189993/5000000000 : ℝ)|=(2865189993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355231389/625000000 : ℝ)|^37 ≤ (24317191131551/50000000000000 : ℝ)^29
        have hw : |(-355231389/625000000 : ℝ)|=(355231389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (329983129/625000000 : ℝ)*x 0 + (-922081599/2500000000 : ℝ)*x 1 + (-3658282521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329983129/625000000 : ℝ)^37 ≤ (44268093023117/100000000000000 : ℝ)^29 := by
    have hnat : (329983129 : ℕ)^37*100000000000000^29 ≤ 44268093023117^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329983129 625000000 44268093023117 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922081599/2500000000 : ℝ)^37 ≤ (28011347033331/100000000000000 : ℝ)^29 := by
    have hnat : (922081599 : ℕ)^37*100000000000000^29 ≤ 28011347033331^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922081599 2500000000 28011347033331 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3658282521/10000000000 : ℝ)^37 ≤ (173253499591/625000000000 : ℝ)^29 := by
    have hnat : (3658282521 : ℕ)^37*625000000000^29 ≤ 173253499591^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3658282521 10000000000 173253499591 625000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329983129/625000000 : ℝ), (-922081599/2500000000 : ℝ), (-3658282521/10000000000 : ℝ)] ![(44268093023117/100000000000000 : ℝ), (28011347033331/100000000000000 : ℝ), (173253499591/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329983129/625000000 : ℝ)|^37 ≤ (44268093023117/100000000000000 : ℝ)^29
        have hw : |(329983129/625000000 : ℝ)|=(329983129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922081599/2500000000 : ℝ)|^37 ≤ (28011347033331/100000000000000 : ℝ)^29
        have hw : |(-922081599/2500000000 : ℝ)|=(922081599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3658282521/10000000000 : ℝ)|^37 ≤ (173253499591/625000000000 : ℝ)^29
        have hw : |(-3658282521/10000000000 : ℝ)|=(3658282521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-207045243/5000000000 : ℝ)*x 0 + (-1567998713/2500000000 : ℝ)*x 1 + (-646668449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207045243/5000000000 : ℝ)^37 ≤ (172030038909/10000000000000 : ℝ)^29 := by
    have hnat : (207045243 : ℕ)^37*10000000000000^29 ≤ 172030038909^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207045243 5000000000 172030038909 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1567998713/2500000000 : ℝ)^37 ≤ (27573228059951/50000000000000 : ℝ)^29 := by
    have hnat : (1567998713 : ℕ)^37*50000000000000^29 ≤ 27573228059951^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567998713 2500000000 27573228059951 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646668449/1250000000 : ℝ)^37 ≤ (21566621739819/50000000000000 : ℝ)^29 := by
    have hnat : (646668449 : ℕ)^37*50000000000000^29 ≤ 21566621739819^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646668449 1250000000 21566621739819 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207045243/5000000000 : ℝ), (-1567998713/2500000000 : ℝ), (-646668449/1250000000 : ℝ)] ![(172030038909/10000000000000 : ℝ), (27573228059951/50000000000000 : ℝ), (21566621739819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207045243/5000000000 : ℝ)|^37 ≤ (172030038909/10000000000000 : ℝ)^29
        have hw : |(-207045243/5000000000 : ℝ)|=(207045243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1567998713/2500000000 : ℝ)|^37 ≤ (27573228059951/50000000000000 : ℝ)^29
        have hw : |(-1567998713/2500000000 : ℝ)|=(1567998713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-646668449/1250000000 : ℝ)|^37 ≤ (21566621739819/50000000000000 : ℝ)^29
        have hw : |(-646668449/1250000000 : ℝ)|=(646668449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5219914911/10000000000 : ℝ)*x 0 + (810002741/2000000000 : ℝ)*x 1 + (-838373247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5219914911/10000000000 : ℝ)^37 ≤ (21814611147227/50000000000000 : ℝ)^29 := by
    have hnat : (5219914911 : ℕ)^37*50000000000000^29 ≤ 21814611147227^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219914911 10000000000 21814611147227 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (810002741/2000000000 : ℝ)^37 ≤ (15781149466241/50000000000000 : ℝ)^29 := by
    have hnat : (810002741 : ℕ)^37*50000000000000^29 ≤ 15781149466241^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810002741 2000000000 15781149466241 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838373247/2500000000 : ℝ)^37 ≤ (24808478754657/100000000000000 : ℝ)^29 := by
    have hnat : (838373247 : ℕ)^37*100000000000000^29 ≤ 24808478754657^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838373247 2500000000 24808478754657 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5219914911/10000000000 : ℝ), (810002741/2000000000 : ℝ), (-838373247/2500000000 : ℝ)] ![(21814611147227/50000000000000 : ℝ), (15781149466241/50000000000000 : ℝ), (24808478754657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5219914911/10000000000 : ℝ)|^37 ≤ (21814611147227/50000000000000 : ℝ)^29
        have hw : |(5219914911/10000000000 : ℝ)|=(5219914911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(810002741/2000000000 : ℝ)|^37 ≤ (15781149466241/50000000000000 : ℝ)^29
        have hw : |(810002741/2000000000 : ℝ)|=(810002741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-838373247/2500000000 : ℝ)|^37 ≤ (24808478754657/100000000000000 : ℝ)^29
        have hw : |(-838373247/2500000000 : ℝ)|=(838373247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5843194977/10000000000 : ℝ)*x 0 + (-1308187131/5000000000 : ℝ)*x 1 + (4048095753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5843194977/10000000000 : ℝ)^37 ≤ (10076461836359/20000000000000 : ℝ)^29 := by
    have hnat : (5843194977 : ℕ)^37*20000000000000^29 ≤ 10076461836359^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5843194977 10000000000 10076461836359 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308187131/5000000000 : ℝ)^37 ≤ (18074460752869/100000000000000 : ℝ)^29 := by
    have hnat : (1308187131 : ℕ)^37*100000000000000^29 ≤ 18074460752869^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308187131 5000000000 18074460752869 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4048095753/10000000000 : ℝ)^37 ≤ (31543230050801/100000000000000 : ℝ)^29 := by
    have hnat : (4048095753 : ℕ)^37*100000000000000^29 ≤ 31543230050801^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048095753 10000000000 31543230050801 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5843194977/10000000000 : ℝ), (-1308187131/5000000000 : ℝ), (4048095753/10000000000 : ℝ)] ![(10076461836359/20000000000000 : ℝ), (18074460752869/100000000000000 : ℝ), (31543230050801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5843194977/10000000000 : ℝ)|^37 ≤ (10076461836359/20000000000000 : ℝ)^29
        have hw : |(5843194977/10000000000 : ℝ)|=(5843194977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1308187131/5000000000 : ℝ)|^37 ≤ (18074460752869/100000000000000 : ℝ)^29
        have hw : |(-1308187131/5000000000 : ℝ)|=(1308187131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4048095753/10000000000 : ℝ)|^37 ≤ (31543230050801/100000000000000 : ℝ)^29
        have hw : |(4048095753/10000000000 : ℝ)|=(4048095753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1370161377/2500000000 : ℝ)*x 0 + (-3129296971/10000000000 : ℝ)*x 1 + (-795825867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370161377/2500000000 : ℝ)^37 ≤ (46428567944341/100000000000000 : ℝ)^29 := by
    have hnat : (1370161377 : ℕ)^37*100000000000000^29 ≤ 46428567944341^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370161377 2500000000 46428567944341 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3129296971/10000000000 : ℝ)^37 ≤ (22712225136119/100000000000000 : ℝ)^29 := by
    have hnat : (3129296971 : ℕ)^37*100000000000000^29 ≤ 22712225136119^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3129296971 10000000000 22712225136119 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795825867/2000000000 : ℝ)^37 ≤ (3085920690649/10000000000000 : ℝ)^29 := by
    have hnat : (795825867 : ℕ)^37*10000000000000^29 ≤ 3085920690649^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795825867 2000000000 3085920690649 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370161377/2500000000 : ℝ), (-3129296971/10000000000 : ℝ), (-795825867/2000000000 : ℝ)] ![(46428567944341/100000000000000 : ℝ), (22712225136119/100000000000000 : ℝ), (3085920690649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370161377/2500000000 : ℝ)|^37 ≤ (46428567944341/100000000000000 : ℝ)^29
        have hw : |(1370161377/2500000000 : ℝ)|=(1370161377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3129296971/10000000000 : ℝ)|^37 ≤ (22712225136119/100000000000000 : ℝ)^29
        have hw : |(-3129296971/10000000000 : ℝ)|=(3129296971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-795825867/2000000000 : ℝ)|^37 ≤ (3085920690649/10000000000000 : ℝ)^29
        have hw : |(-795825867/2000000000 : ℝ)|=(795825867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (91/10000000000 : ℝ)*x 0 + (-2818112933/5000000000 : ℝ)*x 1 + (-1195841067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91/10000000000 : ℝ)^37 ≤ (5507/100000000000000 : ℝ)^29 := by
    have hnat : (91 : ℕ)^37*100000000000000^29 ≤ 5507^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91 10000000000 5507 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2818112933/5000000000 : ℝ)^37 ≤ (6014583290483/12500000000000 : ℝ)^29 := by
    have hnat : (2818112933 : ℕ)^37*12500000000000^29 ≤ 6014583290483^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818112933 5000000000 6014583290483 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195841067/2000000000 : ℝ)^37 ≤ (10376666730653/20000000000000 : ℝ)^29 := by
    have hnat : (1195841067 : ℕ)^37*20000000000000^29 ≤ 10376666730653^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195841067 2000000000 10376666730653 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(91/10000000000 : ℝ), (-2818112933/5000000000 : ℝ), (-1195841067/2000000000 : ℝ)] ![(5507/100000000000000 : ℝ), (6014583290483/12500000000000 : ℝ), (10376666730653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(91/10000000000 : ℝ)|^37 ≤ (5507/100000000000000 : ℝ)^29
        have hw : |(91/10000000000 : ℝ)|=(91/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2818112933/5000000000 : ℝ)|^37 ≤ (6014583290483/12500000000000 : ℝ)^29
        have hw : |(-2818112933/5000000000 : ℝ)|=(2818112933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1195841067/2000000000 : ℝ)|^37 ≤ (10376666730653/20000000000000 : ℝ)^29
        have hw : |(-1195841067/2000000000 : ℝ)|=(1195841067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5588651057/10000000000 : ℝ)*x 0 + (1701509221/5000000000 : ℝ)*x 1 + (-719287231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5588651057/10000000000 : ℝ)^37 ≤ (4759908218509/10000000000000 : ℝ)^29 := by
    have hnat : (5588651057 : ℕ)^37*10000000000000^29 ≤ 4759908218509^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588651057 10000000000 4759908218509 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1701509221/5000000000 : ℝ)^37 ≤ (12638438661057/50000000000000 : ℝ)^29 := by
    have hnat : (1701509221 : ℕ)^37*50000000000000^29 ≤ 12638438661057^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701509221 5000000000 12638438661057 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719287231/2000000000 : ℝ)^37 ≤ (27124040485831/100000000000000 : ℝ)^29 := by
    have hnat : (719287231 : ℕ)^37*100000000000000^29 ≤ 27124040485831^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719287231 2000000000 27124040485831 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5588651057/10000000000 : ℝ), (1701509221/5000000000 : ℝ), (-719287231/2000000000 : ℝ)] ![(4759908218509/10000000000000 : ℝ), (12638438661057/50000000000000 : ℝ), (27124040485831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5588651057/10000000000 : ℝ)|^37 ≤ (4759908218509/10000000000000 : ℝ)^29
        have hw : |(5588651057/10000000000 : ℝ)|=(5588651057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1701509221/5000000000 : ℝ)|^37 ≤ (12638438661057/50000000000000 : ℝ)^29
        have hw : |(1701509221/5000000000 : ℝ)|=(1701509221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-719287231/2000000000 : ℝ)|^37 ≤ (27124040485831/100000000000000 : ℝ)^29
        have hw : |(-719287231/2000000000 : ℝ)|=(719287231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3218099149/5000000000 : ℝ)*x 0 + (-2914735973/10000000000 : ℝ)*x 1 + (24643209/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3218099149/5000000000 : ℝ)^37 ≤ (14248775360331/25000000000000 : ℝ)^29 := by
    have hnat : (3218099149 : ℕ)^37*25000000000000^29 ≤ 14248775360331^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3218099149 5000000000 14248775360331 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2914735973/10000000000 : ℝ)^37 ≤ (20744475292563/100000000000000 : ℝ)^29 := by
    have hnat : (2914735973 : ℕ)^37*100000000000000^29 ≤ 20744475292563^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914735973 10000000000 20744475292563 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24643209/80000000 : ℝ)^37 ≤ (22260423256757/100000000000000 : ℝ)^29 := by
    have hnat : (24643209 : ℕ)^37*100000000000000^29 ≤ 22260423256757^29*80000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24643209 80000000 22260423256757 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3218099149/5000000000 : ℝ), (-2914735973/10000000000 : ℝ), (24643209/80000000 : ℝ)] ![(14248775360331/25000000000000 : ℝ), (20744475292563/100000000000000 : ℝ), (22260423256757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3218099149/5000000000 : ℝ)|^37 ≤ (14248775360331/25000000000000 : ℝ)^29
        have hw : |(3218099149/5000000000 : ℝ)|=(3218099149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2914735973/10000000000 : ℝ)|^37 ≤ (20744475292563/100000000000000 : ℝ)^29
        have hw : |(-2914735973/10000000000 : ℝ)|=(2914735973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24643209/80000000 : ℝ)|^37 ≤ (22260423256757/100000000000000 : ℝ)^29
        have hw : |(24643209/80000000 : ℝ)|=(24643209/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5265374791/10000000000 : ℝ)*x 0 + (-3572111741/10000000000 : ℝ)*x 1 + (-3789484327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265374791/10000000000 : ℝ)^37 ≤ (8822916986653/20000000000000 : ℝ)^29 := by
    have hnat : (5265374791 : ℕ)^37*20000000000000^29 ≤ 8822916986653^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265374791 10000000000 8822916986653 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3572111741/10000000000 : ℝ)^37 ≤ (26890198689761/100000000000000 : ℝ)^29 := by
    have hnat : (3572111741 : ℕ)^37*100000000000000^29 ≤ 26890198689761^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3572111741 10000000000 26890198689761 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3789484327/10000000000 : ℝ)^37 ≤ (1812201022947/6250000000000 : ℝ)^29 := by
    have hnat : (3789484327 : ℕ)^37*6250000000000^29 ≤ 1812201022947^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789484327 10000000000 1812201022947 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265374791/10000000000 : ℝ), (-3572111741/10000000000 : ℝ), (-3789484327/10000000000 : ℝ)] ![(8822916986653/20000000000000 : ℝ), (26890198689761/100000000000000 : ℝ), (1812201022947/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265374791/10000000000 : ℝ)|^37 ≤ (8822916986653/20000000000000 : ℝ)^29
        have hw : |(5265374791/10000000000 : ℝ)|=(5265374791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3572111741/10000000000 : ℝ)|^37 ≤ (26890198689761/100000000000000 : ℝ)^29
        have hw : |(-3572111741/10000000000 : ℝ)|=(3572111741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3789484327/10000000000 : ℝ)|^37 ≤ (1812201022947/6250000000000 : ℝ)^29
        have hw : |(-3789484327/10000000000 : ℝ)|=(3789484327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (13/2500000000 : ℝ)*x 0 + (-6015992893/10000000000 : ℝ)*x 1 + (-559876783/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13/2500000000 : ℝ)^37 ≤ (2697/100000000000000 : ℝ)^29 := by
    have hnat : (13 : ℕ)^37*100000000000000^29 ≤ 2697^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13 2500000000 2697 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6015992893/10000000000 : ℝ)^37 ≤ (52290955024387/100000000000000 : ℝ)^29 := by
    have hnat : (6015992893 : ℕ)^37*100000000000000^29 ≤ 52290955024387^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015992893 10000000000 52290955024387 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559876783/1000000000 : ℝ)^37 ≤ (9541808992127/20000000000000 : ℝ)^29 := by
    have hnat : (559876783 : ℕ)^37*20000000000000^29 ≤ 9541808992127^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559876783 1000000000 9541808992127 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13/2500000000 : ℝ), (-6015992893/10000000000 : ℝ), (-559876783/1000000000 : ℝ)] ![(2697/100000000000000 : ℝ), (52290955024387/100000000000000 : ℝ), (9541808992127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13/2500000000 : ℝ)|^37 ≤ (2697/100000000000000 : ℝ)^29
        have hw : |(13/2500000000 : ℝ)|=(13/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6015992893/10000000000 : ℝ)|^37 ≤ (52290955024387/100000000000000 : ℝ)^29
        have hw : |(-6015992893/10000000000 : ℝ)|=(6015992893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559876783/1000000000 : ℝ)|^37 ≤ (9541808992127/20000000000000 : ℝ)^29
        have hw : |(-559876783/1000000000 : ℝ)|=(559876783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6501265321/10000000000 : ℝ)*x 0 + (3019276923/10000000000 : ℝ)*x 1 + (-579107911/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6501265321/10000000000 : ℝ)^37 ≤ (57731268661801/100000000000000 : ℝ)^29 := by
    have hnat : (6501265321 : ℕ)^37*100000000000000^29 ≤ 57731268661801^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6501265321 10000000000 57731268661801 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3019276923/10000000000 : ℝ)^37 ≤ (4339681875777/20000000000000 : ℝ)^29 := by
    have hnat : (3019276923 : ℕ)^37*20000000000000^29 ≤ 4339681875777^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019276923 10000000000 4339681875777 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579107911/2000000000 : ℝ)^37 ≤ (20570321943591/100000000000000 : ℝ)^29 := by
    have hnat : (579107911 : ℕ)^37*100000000000000^29 ≤ 20570321943591^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579107911 2000000000 20570321943591 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6501265321/10000000000 : ℝ), (3019276923/10000000000 : ℝ), (-579107911/2000000000 : ℝ)] ![(57731268661801/100000000000000 : ℝ), (4339681875777/20000000000000 : ℝ), (20570321943591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6501265321/10000000000 : ℝ)|^37 ≤ (57731268661801/100000000000000 : ℝ)^29
        have hw : |(6501265321/10000000000 : ℝ)|=(6501265321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3019276923/10000000000 : ℝ)|^37 ≤ (4339681875777/20000000000000 : ℝ)^29
        have hw : |(3019276923/10000000000 : ℝ)|=(3019276923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579107911/2000000000 : ℝ)|^37 ≤ (20570321943591/100000000000000 : ℝ)^29
        have hw : |(-579107911/2000000000 : ℝ)|=(579107911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (551850297/1000000000 : ℝ)*x 0 + (-3613707/10000000 : ℝ)*x 1 + (3465608431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551850297/1000000000 : ℝ)^37 ≤ (46838131863061/100000000000000 : ℝ)^29 := by
    have hnat : (551850297 : ℕ)^37*100000000000000^29 ≤ 46838131863061^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551850297 1000000000 46838131863061 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3613707/10000000 : ℝ)^37 ≤ (13645169157349/50000000000000 : ℝ)^29 := by
    have hnat : (3613707 : ℕ)^37*50000000000000^29 ≤ 13645169157349^29*10000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613707 10000000 13645169157349 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3465608431/10000000000 : ℝ)^37 ≤ (3233941226763/12500000000000 : ℝ)^29 := by
    have hnat : (3465608431 : ℕ)^37*12500000000000^29 ≤ 3233941226763^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465608431 10000000000 3233941226763 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551850297/1000000000 : ℝ), (-3613707/10000000 : ℝ), (3465608431/10000000000 : ℝ)] ![(46838131863061/100000000000000 : ℝ), (13645169157349/50000000000000 : ℝ), (3233941226763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551850297/1000000000 : ℝ)|^37 ≤ (46838131863061/100000000000000 : ℝ)^29
        have hw : |(551850297/1000000000 : ℝ)|=(551850297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3613707/10000000 : ℝ)|^37 ≤ (13645169157349/50000000000000 : ℝ)^29
        have hw : |(-3613707/10000000 : ℝ)|=(3613707/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3465608431/10000000000 : ℝ)|^37 ≤ (3233941226763/12500000000000 : ℝ)^29
        have hw : |(3465608431/10000000000 : ℝ)|=(3465608431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312036_s1_s1_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5277257413/10000000000 : ℝ)*x 0 + (-761200691/2000000000 : ℝ)*x 1 + (-1771023511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277257413/10000000000 : ℝ)^37 ≤ (22120821757939/50000000000000 : ℝ)^29 := by
    have hnat : (5277257413 : ℕ)^37*50000000000000^29 ≤ 22120821757939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277257413 10000000000 22120821757939 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (761200691/2000000000 : ℝ)^37 ≤ (14578288550173/50000000000000 : ℝ)^29 := by
    have hnat : (761200691 : ℕ)^37*50000000000000^29 ≤ 14578288550173^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761200691 2000000000 14578288550173 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1771023511/5000000000 : ℝ)^37 ≤ (26601779364227/100000000000000 : ℝ)^29 := by
    have hnat : (1771023511 : ℕ)^37*100000000000000^29 ≤ 26601779364227^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771023511 5000000000 26601779364227 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277257413/10000000000 : ℝ), (-761200691/2000000000 : ℝ), (-1771023511/5000000000 : ℝ)] ![(22120821757939/50000000000000 : ℝ), (14578288550173/50000000000000 : ℝ), (26601779364227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277257413/10000000000 : ℝ)|^37 ≤ (22120821757939/50000000000000 : ℝ)^29
        have hw : |(5277257413/10000000000 : ℝ)|=(5277257413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-761200691/2000000000 : ℝ)|^37 ≤ (14578288550173/50000000000000 : ℝ)^29
        have hw : |(-761200691/2000000000 : ℝ)|=(761200691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1771023511/5000000000 : ℝ)|^37 ≤ (26601779364227/100000000000000 : ℝ)^29
        have hw : |(-1771023511/5000000000 : ℝ)|=(1771023511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312036_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((197/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(197/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38079/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-38079/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-79117/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-79117/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7463/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7463/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9959/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-9959/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40099/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40099/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (197/400 : ℝ) ^ (9/2 : ℝ) ≤ (516105003856706437/12500000000000000000 : ℝ) := by
    have hpowers : (197/400 : ℝ)^9 ≤ (516105003856706437/12500000000000000000 : ℝ)^2 := by
      have hnat : (197 : ℕ)^9*12500000000000000000^2 ≤ 516105003856706437^2*400^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        197 400 516105003856706437 12500000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (197/400 : ℝ)) (X := (516105003856706437/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13016105003856706437/12500000000000000000 : ℝ) ≤ (10090313818891973/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (13016105003856706437/12500000000000000000 : ℝ)^2 ≤ (10090313818891973/10000000000000000 : ℝ)^9 := by
      have hnat : (13016105003856706437 : ℕ)^2*10000000000000000^9 ≤ 10090313818891973^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13016105003856706437 12500000000000000000 10090313818891973 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10090313818891973/10000000000000000 : ℝ)) (X := (13016105003856706437/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6766105003856706437/6250000000000000000 : ℝ) ≤ (10177883898075291/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (6766105003856706437/6250000000000000000 : ℝ)^2 ≤ (10177883898075291/10000000000000000 : ℝ)^9 := by
      have hnat : (6766105003856706437 : ℕ)^2*10000000000000000^9 ≤ 10177883898075291^9*6250000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6766105003856706437 6250000000000000000 10177883898075291 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10177883898075291/10000000000000000 : ℝ)) (X := (6766105003856706437/6250000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(90313818891973/4925000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(43785039591659/2462500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (197/400 : ℝ)) (alpha := (90313818891973/4925000000000000 : ℝ)) (beta := (43785039591659/2462500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (197/400 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(90313818891973/4925000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(43785039591659/2462500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (38079/50000 : ℝ) ^ (9/2 : ℝ) ≤ (29357555254918600109/100000000000000000000 : ℝ) := by
    have hpowers : (38079/50000 : ℝ)^9 ≤ (29357555254918600109/100000000000000000000 : ℝ)^2 := by
      have hnat : (38079 : ℕ)^9*100000000000000000000^2 ≤ 29357555254918600109^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38079 50000 29357555254918600109 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38079/50000 : ℝ)) (X := (29357555254918600109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (129357555254918600109/100000000000000000000 : ℝ) ≤ (10588699464411349/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (129357555254918600109/100000000000000000000 : ℝ)^2 ≤ (10588699464411349/10000000000000000 : ℝ)^9 := by
      have hnat : (129357555254918600109 : ℕ)^2*10000000000000000^9 ≤ 10588699464411349^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129357555254918600109 100000000000000000000 10588699464411349 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10588699464411349/10000000000000000 : ℝ)) (X := (129357555254918600109/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (79357555254918600109/50000000000000000000 : ℝ) ≤ (5540536795190569/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (79357555254918600109/50000000000000000000 : ℝ)^2 ≤ (5540536795190569/5000000000000000 : ℝ)^9 := by
      have hnat : (79357555254918600109 : ℕ)^2*5000000000000000^9 ≤ 5540536795190569^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79357555254918600109 50000000000000000000 5540536795190569 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5540536795190569/5000000000000000 : ℝ)) (X := (79357555254918600109/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(65411051601261/846200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(492374125969789/7615800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (38079/50000 : ℝ)) (alpha := (65411051601261/846200000000000 : ℝ)) (beta := (492374125969789/7615800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (38079/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(65411051601261/846200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(492374125969789/7615800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (79117/100000 : ℝ) ^ (9/2 : ℝ) ≤ (8712728049356311871/25000000000000000000 : ℝ) := by
    have hpowers : (79117/100000 : ℝ)^9 ≤ (8712728049356311871/25000000000000000000 : ℝ)^2 := by
      have hnat : (79117 : ℕ)^9*25000000000000000000^2 ≤ 8712728049356311871^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79117 100000 8712728049356311871 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79117/100000 : ℝ)) (X := (8712728049356311871/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (33712728049356311871/25000000000000000000 : ℝ) ≤ (534350750897607/500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (33712728049356311871/25000000000000000000 : ℝ)^2 ≤ (534350750897607/500000000000000 : ℝ)^9 := by
      have hnat : (33712728049356311871 : ℕ)^2*500000000000000^9 ≤ 534350750897607^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33712728049356311871 25000000000000000000 534350750897607 500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (534350750897607/500000000000000 : ℝ)) (X := (33712728049356311871/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (21212728049356311871/12500000000000000000 : ℝ) ≤ (11247123059037091/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (21212728049356311871/12500000000000000000 : ℝ)^2 ≤ (11247123059037091/10000000000000000 : ℝ)^9 := by
      have hnat : (21212728049356311871 : ℕ)^2*10000000000000000^9 ≤ 11247123059037091^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21212728049356311871 12500000000000000000 11247123059037091 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11247123059037091/10000000000000000 : ℝ)) (X := (21212728049356311871/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(34350750897607/395585000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(560108041084951/7911700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (79117/100000 : ℝ)) (alpha := (34350750897607/395585000000000 : ℝ)) (beta := (560108041084951/7911700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (79117/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(34350750897607/395585000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(560108041084951/7911700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-505896077/10000000000 : ℝ)*X 0 0+(-2865189993/5000000000 : ℝ)*X 0 1+(-355231389/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((329983129/625000000 : ℝ)*X 0 0+(-922081599/2500000000 : ℝ)*X 0 1+(-3658282521/10000000000 : ℝ)*X 0 2+(329983129/625000000 : ℝ)*X 1 0+(-922081599/2500000000 : ℝ)*X 1 1+(-3658282521/10000000000 : ℝ)*X 1 2+(329983129/625000000 : ℝ)*X 2 0+(-922081599/2500000000 : ℝ)*X 2 1+(-3658282521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-207045243/5000000000 : ℝ)*X 0 0+(-1567998713/2500000000 : ℝ)*X 0 1+(-646668449/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5219914911/10000000000 : ℝ)*X 1 0+(810002741/2000000000 : ℝ)*X 1 1+(-838373247/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5843194977/10000000000 : ℝ)*X 2 0+(-1308187131/5000000000 : ℝ)*X 2 1+(4048095753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1370161377/2500000000 : ℝ)*X 0 0+(-3129296971/10000000000 : ℝ)*X 0 1+(-795825867/2000000000 : ℝ)*X 0 2+(1370161377/2500000000 : ℝ)*X 1 0+(-3129296971/10000000000 : ℝ)*X 1 1+(-795825867/2000000000 : ℝ)*X 1 2+(1370161377/2500000000 : ℝ)*X 2 0+(-3129296971/10000000000 : ℝ)*X 2 1+(-795825867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((91/10000000000 : ℝ)*X 0 0+(-2818112933/5000000000 : ℝ)*X 0 1+(-1195841067/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((5588651057/10000000000 : ℝ)*X 1 0+(1701509221/5000000000 : ℝ)*X 1 1+(-719287231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3218099149/5000000000 : ℝ)*X 2 0+(-2914735973/10000000000 : ℝ)*X 2 1+(24643209/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((5265374791/10000000000 : ℝ)*X 0 0+(-3572111741/10000000000 : ℝ)*X 0 1+(-3789484327/10000000000 : ℝ)*X 0 2+(5265374791/10000000000 : ℝ)*X 1 0+(-3572111741/10000000000 : ℝ)*X 1 1+(-3789484327/10000000000 : ℝ)*X 1 2+(5265374791/10000000000 : ℝ)*X 2 0+(-3572111741/10000000000 : ℝ)*X 2 1+(-3789484327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((13/2500000000 : ℝ)*X 0 0+(-6015992893/10000000000 : ℝ)*X 0 1+(-559876783/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6501265321/10000000000 : ℝ)*X 1 0+(3019276923/10000000000 : ℝ)*X 1 1+(-579107911/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((551850297/1000000000 : ℝ)*X 2 0+(-3613707/10000000 : ℝ)*X 2 1+(3465608431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((5277257413/10000000000 : ℝ)*X 0 0+(-761200691/2000000000 : ℝ)*X 0 1+(-1771023511/5000000000 : ℝ)*X 0 2+(5277257413/10000000000 : ℝ)*X 1 0+(-761200691/2000000000 : ℝ)*X 1 1+(-1771023511/5000000000 : ℝ)*X 1 2+(5277257413/10000000000 : ℝ)*X 2 0+(-761200691/2000000000 : ℝ)*X 2 1+(-1771023511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312036_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((7463/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7463/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40931669846825218734451541983081/2472921499462500000000000000000000000 : ℝ) := by norm_num
    linear_combination (128162651359/200000000000 : ℝ)*(base39) + (118704692219/500000000000 : ℝ)*(base50) + (341835643/31250000000 : ℝ)*(base60) + (2338369437437/1000000000000 : ℝ)*(major_s1_0) + (2338369437437/1000000000000 : ℝ)*(major_s1_1) + (2338369437437/1000000000000 : ℝ)*(major_s1_2) + (14026891/62500000000 : ℝ)*(sp_s1_0) + (131017558473/40000000000 : ℝ)*(sp_s1_7) + (3275781793991/1000000000000 : ℝ)*(sp_s1_8) + (204736393797/62500000000 : ℝ)*(sp_s1_9) + (140044580077/100000000000 : ℝ)*(sp_s1_13) + (506761/1000000000000 : ℝ)*(sp_s1_15) + (50525603/100000000000 : ℝ)*(sp_s1_19) + (118908671/1000000000000 : ℝ)*(sp_s1_20) + (1751188821/1250000000 : ℝ)*(f.failure) + (204736393797/62500000000 : ℝ)*(f.sum) + (41748637820081325971/66948805400000000000000000000000 : ℝ)*base62 + (2542150629970357/7911700000000000000000000000 : ℝ)*base64 + (2315790589225073/7615800000000000000000000000 : ℝ)*base66 + (171867535931219/395585000000000000000000000 : ℝ)*base68 + (226214273105391158733/389651225000000000000000000000000 : ℝ)*base70 + (493049299798267/2462500000000000000000000000 : ℝ)*base72 + (346393152316223/846200000000000000000000000 : ℝ)*base74 + (66317059936799/4925000000000000000000000000 : ℝ)*base76 + (148732283522093688311/187539075000000000000000000000000 : ℝ)*base78 + (13/31250000000000 : ℝ)*base86 + (13/31250000000000 : ℝ)*base88 + (13/31250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9959/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-9959/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1887135342537545466033945453/97412806250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1985091284509/500000000000 : ℝ)*(base39) + (2172074541421/1000000000000 : ℝ)*(base40) + (10307878753/125000000000 : ℝ)*(base60) + (3576671902089/500000000000 : ℝ)*(major_s1_0) + (3576671902089/500000000000 : ℝ)*(major_s1_1) + (3576671902089/500000000000 : ℝ)*(major_s1_2) + (402200077/1000000000000 : ℝ)*(sp_s1_6) + (3368523/1000000000000 : ℝ)*(sp_s1_8) + (37336123/1000000000000 : ℝ)*(sp_s1_9) + (232891413/500000000000 : ℝ)*(sp_s1_13) + (5010504545813/500000000000 : ℝ)*(sp_s1_14) + (313156428847/31250000000 : ℝ)*(sp_s1_15) + (10020971755503/1000000000000 : ℝ)*(sp_s1_16) + (4284804076301/1000000000000 : ℝ)*(sp_s1_19) + (4285672059203/1000000000000 : ℝ)*(f.failure) + (5010504545813/500000000000 : ℝ)*(f.sum) + (21574927693855571797/33474402700000000000000000000000 : ℝ)*base62 + (199153268116383/494481250000000000000000000 : ℝ)*base64 + (55418331848629/423100000000000000000000000 : ℝ)*base66 + (156467308645211/197792500000000000000000000 : ℝ)*base68 + (52587240838285269099/194825612500000000000000000000000 : ℝ)*base71 + (90677906983099/1231250000000000000000000000 : ℝ)*base72 + (6633013095709/423100000000000000000000000 : ℝ)*base75 + (1088371461691597/2462500000000000000000000000 : ℝ)*base77 + (613180873095134637/10418837500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (49661/100000000000000000 : ℝ)*base86 + (49661/100000000000000000 : ℝ)*base88 + (49661/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40099/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40099/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6947038411993443585602463610723/618230374865625000000000000000000000 : ℝ) := by norm_num
    linear_combination (3966225754427/1000000000000 : ℝ)*(base39) + (22076061909/12500000000 : ℝ)*(base40) + (85290460513/1000000000000 : ℝ)*(base50) + (3569277366661/500000000000 : ℝ)*(major_s1_0) + (3569277366661/500000000000 : ℝ)*(major_s1_1) + (3569277366661/500000000000 : ℝ)*(major_s1_2) + (78975053/500000000000 : ℝ)*(sp_s1_7) + (28104879/500000000000 : ℝ)*(sp_s1_8) + (26566141/1000000000000 : ℝ)*(sp_s1_13) + (1473219/31250000000 : ℝ)*(sp_s1_16) + (1000013605859/100000000000 : ℝ)*(sp_s1_20) + (5000118899469/500000000000 : ℝ)*(sp_s1_21) + (10000246865689/1000000000000 : ℝ)*(sp_s1_22) + (2138392573071/500000000000 : ℝ)*(sp_s1_25) + (4276811712283/1000000000000 : ℝ)*(f.failure) + (10000294008697/1000000000000 : ℝ)*(f.sum) + (24488251759309297823/33474402700000000000000000000000 : ℝ)*base62 + (6365367441911/988962500000000000000000000 : ℝ)*base65 + (1343428473173839/3807900000000000000000000000 : ℝ)*base66 + (47305981550281/395585000000000000000000000 : ℝ)*base68 + (6884737876643683401/194825612500000000000000000000000 : ℝ)*base71 + (21128588769139/76953125000000000000000000 : ℝ)*base73 + (482504696052759/423100000000000000000000000 : ℝ)*base74 + (473795112068403/2462500000000000000000000000 : ℝ)*base77 + (32873506862703917983/93769537500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (92379/100000000000000000 : ℝ)*base87 + (92379/100000000000000000 : ℝ)*base89 + (92379/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((197/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(197/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38079/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-38079/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-79117/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-79117/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7463/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7463/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9959/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-9959/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40099/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40099/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312036_s1 p hpa hpb X hX hprev0

#print axioms solution

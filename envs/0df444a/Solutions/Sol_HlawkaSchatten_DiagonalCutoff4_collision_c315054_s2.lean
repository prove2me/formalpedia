-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:18.289301+00:00
-- url     : https://prove2.me/submissions/faf9f04c-c365-4f56-a33b-1d3ef48671c4

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
theorem collision_support_c315054_s2_s2_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1306224899/10000000000 : ℝ)*x 0 + (4525035987/10000000000 : ℝ)*x 1 + (-3153855167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306224899/10000000000 : ℝ)^19 ≤ (7590832588081/100000000000000 : ℝ)^15 := by
    have hnat : (1306224899 : ℕ)^19*100000000000000^15 ≤ 7590832588081^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306224899 10000000000 7590832588081 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525035987/10000000000 : ℝ)^19 ≤ (9156466751633/25000000000000 : ℝ)^15 := by
    have hnat : (4525035987 : ℕ)^19*25000000000000^15 ≤ 9156466751633^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525035987 10000000000 9156466751633 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3153855167/5000000000 : ℝ)^19 ≤ (27891650197621/50000000000000 : ℝ)^15 := by
    have hnat : (3153855167 : ℕ)^19*50000000000000^15 ≤ 27891650197621^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3153855167 5000000000 27891650197621 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1306224899/10000000000 : ℝ), (4525035987/10000000000 : ℝ), (-3153855167/5000000000 : ℝ)] ![(7590832588081/100000000000000 : ℝ), (9156466751633/25000000000000 : ℝ), (27891650197621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1306224899/10000000000 : ℝ)|^19 ≤ (7590832588081/100000000000000 : ℝ)^15
        have hw : |(-1306224899/10000000000 : ℝ)|=(1306224899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525035987/10000000000 : ℝ)|^19 ≤ (9156466751633/25000000000000 : ℝ)^15
        have hw : |(4525035987/10000000000 : ℝ)|=(4525035987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3153855167/5000000000 : ℝ)|^19 ≤ (27891650197621/50000000000000 : ℝ)^15
        have hw : |(-3153855167/5000000000 : ℝ)|=(3153855167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1099984301/2000000000 : ℝ)*x 0 + (-1156133173/5000000000 : ℝ)*x 1 + (-2303018009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099984301/2000000000 : ℝ)^19 ≤ (11723525460739/25000000000000 : ℝ)^15 := by
    have hnat : (1099984301 : ℕ)^19*25000000000000^15 ≤ 11723525460739^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099984301 2000000000 11723525460739 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156133173/5000000000 : ℝ)^19 ≤ (3129521571633/20000000000000 : ℝ)^15 := by
    have hnat : (1156133173 : ℕ)^19*20000000000000^15 ≤ 3129521571633^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156133173 5000000000 3129521571633 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303018009/5000000000 : ℝ)^19 ≤ (1498331611577/4000000000000 : ℝ)^15 := by
    have hnat : (2303018009 : ℕ)^19*4000000000000^15 ≤ 1498331611577^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303018009 5000000000 1498331611577 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099984301/2000000000 : ℝ), (-1156133173/5000000000 : ℝ), (-2303018009/5000000000 : ℝ)] ![(11723525460739/25000000000000 : ℝ), (3129521571633/20000000000000 : ℝ), (1498331611577/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099984301/2000000000 : ℝ)|^19 ≤ (11723525460739/25000000000000 : ℝ)^15
        have hw : |(1099984301/2000000000 : ℝ)|=(1099984301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1156133173/5000000000 : ℝ)|^19 ≤ (3129521571633/20000000000000 : ℝ)^15
        have hw : |(-1156133173/5000000000 : ℝ)|=(1156133173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2303018009/5000000000 : ℝ)|^19 ≤ (1498331611577/4000000000000 : ℝ)^15
        have hw : |(-2303018009/5000000000 : ℝ)|=(2303018009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5111417391/10000000000 : ℝ)*x 0 + (5088039489/10000000000 : ℝ)*x 1 + (2209322899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5111417391/10000000000 : ℝ)^19 ≤ (42738476678259/100000000000000 : ℝ)^15 := by
    have hnat : (5111417391 : ℕ)^19*100000000000000^15 ≤ 42738476678259^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111417391 10000000000 42738476678259 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088039489/10000000000 : ℝ)^19 ≤ (42491030729353/100000000000000 : ℝ)^15 := by
    have hnat : (5088039489 : ℕ)^19*100000000000000^15 ≤ 42491030729353^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088039489 10000000000 42491030729353 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209322899/10000000000 : ℝ)^19 ≤ (2954098517069/20000000000000 : ℝ)^15 := by
    have hnat : (2209322899 : ℕ)^19*20000000000000^15 ≤ 2954098517069^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209322899 10000000000 2954098517069 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5111417391/10000000000 : ℝ), (5088039489/10000000000 : ℝ), (2209322899/10000000000 : ℝ)] ![(42738476678259/100000000000000 : ℝ), (42491030729353/100000000000000 : ℝ), (2954098517069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5111417391/10000000000 : ℝ)|^19 ≤ (42738476678259/100000000000000 : ℝ)^15
        have hw : |(5111417391/10000000000 : ℝ)|=(5111417391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088039489/10000000000 : ℝ)|^19 ≤ (42491030729353/100000000000000 : ℝ)^15
        have hw : |(5088039489/10000000000 : ℝ)|=(5088039489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209322899/10000000000 : ℝ)|^19 ≤ (2954098517069/20000000000000 : ℝ)^15
        have hw : |(2209322899/10000000000 : ℝ)|=(2209322899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5141676833/10000000000 : ℝ)*x 0 + (1280558651/2500000000 : ℝ)*x 1 + (-425659209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5141676833/10000000000 : ℝ)^19 ≤ (43059209290301/100000000000000 : ℝ)^15 := by
    have hnat : (5141676833 : ℕ)^19*100000000000000^15 ≤ 43059209290301^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141676833 10000000000 43059209290301 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280558651/2500000000 : ℝ)^19 ≤ (21426537450247/50000000000000 : ℝ)^15 := by
    have hnat : (1280558651 : ℕ)^19*50000000000000^15 ≤ 21426537450247^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280558651 2500000000 21426537450247 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425659209/2000000000 : ℝ)^19 ≤ (352192894747/2500000000000 : ℝ)^15 := by
    have hnat : (425659209 : ℕ)^19*2500000000000^15 ≤ 352192894747^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425659209 2000000000 352192894747 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5141676833/10000000000 : ℝ), (1280558651/2500000000 : ℝ), (-425659209/2000000000 : ℝ)] ![(43059209290301/100000000000000 : ℝ), (21426537450247/50000000000000 : ℝ), (352192894747/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5141676833/10000000000 : ℝ)|^19 ≤ (43059209290301/100000000000000 : ℝ)^15
        have hw : |(5141676833/10000000000 : ℝ)|=(5141676833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1280558651/2500000000 : ℝ)|^19 ≤ (21426537450247/50000000000000 : ℝ)^15
        have hw : |(1280558651/2500000000 : ℝ)|=(1280558651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425659209/2000000000 : ℝ)|^19 ≤ (352192894747/2500000000000 : ℝ)^15
        have hw : |(-425659209/2000000000 : ℝ)|=(425659209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-122589289/1000000000 : ℝ)*x 0 + (105826729/250000000 : ℝ)*x 1 + (-3311433011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122589289/1000000000 : ℝ)^19 ≤ (350221822901/5000000000000 : ℝ)^15 := by
    have hnat : (122589289 : ℕ)^19*5000000000000^15 ≤ 350221822901^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122589289 1000000000 350221822901 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105826729/250000000 : ℝ)^19 ≤ (8414664464617/25000000000000 : ℝ)^15 := by
    have hnat : (105826729 : ℕ)^19*25000000000000^15 ≤ 8414664464617^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105826729 250000000 8414664464617 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3311433011/5000000000 : ℝ)^19 ≤ (59336905665187/100000000000000 : ℝ)^15 := by
    have hnat : (3311433011 : ℕ)^19*100000000000000^15 ≤ 59336905665187^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311433011 5000000000 59336905665187 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122589289/1000000000 : ℝ), (105826729/250000000 : ℝ), (-3311433011/5000000000 : ℝ)] ![(350221822901/5000000000000 : ℝ), (8414664464617/25000000000000 : ℝ), (59336905665187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122589289/1000000000 : ℝ)|^19 ≤ (350221822901/5000000000000 : ℝ)^15
        have hw : |(-122589289/1000000000 : ℝ)|=(122589289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105826729/250000000 : ℝ)|^19 ≤ (8414664464617/25000000000000 : ℝ)^15
        have hw : |(105826729/250000000 : ℝ)|=(105826729/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3311433011/5000000000 : ℝ)|^19 ≤ (59336905665187/100000000000000 : ℝ)^15
        have hw : |(-3311433011/5000000000 : ℝ)|=(3311433011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5346537811/10000000000 : ℝ)*x 0 + (-86287253/500000000 : ℝ)*x 1 + (-104517399/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346537811/10000000000 : ℝ)^19 ≤ (45243759017407/100000000000000 : ℝ)^15 := by
    have hnat : (5346537811 : ℕ)^19*100000000000000^15 ≤ 45243759017407^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346537811 10000000000 45243759017407 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86287253/500000000 : ℝ)^19 ≤ (10801989295783/100000000000000 : ℝ)^15 := by
    have hnat : (86287253 : ℕ)^19*100000000000000^15 ≤ 10801989295783^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86287253 500000000 10801989295783 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104517399/200000000 : ℝ)^19 ≤ (21977125834453/50000000000000 : ℝ)^15 := by
    have hnat : (104517399 : ℕ)^19*50000000000000^15 ≤ 21977125834453^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104517399 200000000 21977125834453 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346537811/10000000000 : ℝ), (-86287253/500000000 : ℝ), (-104517399/200000000 : ℝ)] ![(45243759017407/100000000000000 : ℝ), (10801989295783/100000000000000 : ℝ), (21977125834453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346537811/10000000000 : ℝ)|^19 ≤ (45243759017407/100000000000000 : ℝ)^15
        have hw : |(5346537811/10000000000 : ℝ)|=(5346537811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86287253/500000000 : ℝ)|^19 ≤ (10801989295783/100000000000000 : ℝ)^15
        have hw : |(-86287253/500000000 : ℝ)|=(86287253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104517399/200000000 : ℝ)|^19 ≤ (21977125834453/50000000000000 : ℝ)^15
        have hw : |(-104517399/200000000 : ℝ)|=(104517399/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (490872059/1000000000 : ℝ)*x 0 + (574216023/1000000000 : ℝ)*x 1 + (1607262801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490872059/1000000000 : ℝ)^19 ≤ (20301581295267/50000000000000 : ℝ)^15 := by
    have hnat : (490872059 : ℕ)^19*50000000000000^15 ≤ 20301581295267^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490872059 1000000000 20301581295267 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574216023/1000000000 : ℝ)^19 ≤ (49525483275097/100000000000000 : ℝ)^15 := by
    have hnat : (574216023 : ℕ)^19*100000000000000^15 ≤ 49525483275097^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574216023 1000000000 49525483275097 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1607262801/10000000000 : ℝ)^19 ≤ (4935677057239/50000000000000 : ℝ)^15 := by
    have hnat : (1607262801 : ℕ)^19*50000000000000^15 ≤ 4935677057239^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607262801 10000000000 4935677057239 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490872059/1000000000 : ℝ), (574216023/1000000000 : ℝ), (1607262801/10000000000 : ℝ)] ![(20301581295267/50000000000000 : ℝ), (49525483275097/100000000000000 : ℝ), (4935677057239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490872059/1000000000 : ℝ)|^19 ≤ (20301581295267/50000000000000 : ℝ)^15
        have hw : |(490872059/1000000000 : ℝ)|=(490872059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574216023/1000000000 : ℝ)|^19 ≤ (49525483275097/100000000000000 : ℝ)^15
        have hw : |(574216023/1000000000 : ℝ)|=(574216023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1607262801/10000000000 : ℝ)|^19 ≤ (4935677057239/50000000000000 : ℝ)^15
        have hw : |(1607262801/10000000000 : ℝ)|=(1607262801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1010663833/2000000000 : ℝ)*x 0 + (2879581039/5000000000 : ℝ)*x 1 + (-1383571893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010663833/2000000000 : ℝ)^19 ≤ (42124089157009/100000000000000 : ℝ)^15 := by
    have hnat : (1010663833 : ℕ)^19*100000000000000^15 ≤ 42124089157009^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010663833 2000000000 42124089157009 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2879581039/5000000000 : ℝ)^19 ≤ (9942259861363/20000000000000 : ℝ)^15 := by
    have hnat : (2879581039 : ℕ)^19*20000000000000^15 ≤ 9942259861363^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2879581039 5000000000 9942259861363 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383571893/10000000000 : ℝ)^19 ≤ (8164611525437/100000000000000 : ℝ)^15 := by
    have hnat : (1383571893 : ℕ)^19*100000000000000^15 ≤ 8164611525437^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383571893 10000000000 8164611525437 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1010663833/2000000000 : ℝ), (2879581039/5000000000 : ℝ), (-1383571893/10000000000 : ℝ)] ![(42124089157009/100000000000000 : ℝ), (9942259861363/20000000000000 : ℝ), (8164611525437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1010663833/2000000000 : ℝ)|^19 ≤ (42124089157009/100000000000000 : ℝ)^15
        have hw : |(1010663833/2000000000 : ℝ)|=(1010663833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2879581039/5000000000 : ℝ)|^19 ≤ (9942259861363/20000000000000 : ℝ)^15
        have hw : |(2879581039/5000000000 : ℝ)|=(2879581039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1383571893/10000000000 : ℝ)|^19 ≤ (8164611525437/100000000000000 : ℝ)^15
        have hw : |(-1383571893/10000000000 : ℝ)|=(1383571893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-430461421/5000000000 : ℝ)*x 0 + (905185477/2000000000 : ℝ)*x 1 + (-6583307217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430461421/5000000000 : ℝ)^19 ≤ (223833299437/5000000000000 : ℝ)^15 := by
    have hnat : (430461421 : ℕ)^19*5000000000000^15 ≤ 223833299437^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430461421 5000000000 223833299437 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905185477/2000000000 : ℝ)^19 ≤ (36635006271743/100000000000000 : ℝ)^15 := by
    have hnat : (905185477 : ℕ)^19*100000000000000^15 ≤ 36635006271743^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905185477 2000000000 36635006271743 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6583307217/10000000000 : ℝ)^19 ≤ (58888327726839/100000000000000 : ℝ)^15 := by
    have hnat : (6583307217 : ℕ)^19*100000000000000^15 ≤ 58888327726839^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6583307217 10000000000 58888327726839 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430461421/5000000000 : ℝ), (905185477/2000000000 : ℝ), (-6583307217/10000000000 : ℝ)] ![(223833299437/5000000000000 : ℝ), (36635006271743/100000000000000 : ℝ), (58888327726839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430461421/5000000000 : ℝ)|^19 ≤ (223833299437/5000000000000 : ℝ)^15
        have hw : |(-430461421/5000000000 : ℝ)|=(430461421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905185477/2000000000 : ℝ)|^19 ≤ (36635006271743/100000000000000 : ℝ)^15
        have hw : |(905185477/2000000000 : ℝ)|=(905185477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6583307217/10000000000 : ℝ)|^19 ≤ (58888327726839/100000000000000 : ℝ)^15
        have hw : |(-6583307217/10000000000 : ℝ)|=(6583307217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2534157001/5000000000 : ℝ)*x 0 + (-2064325021/10000000000 : ℝ)*x 1 + (-655693421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2534157001/5000000000 : ℝ)^19 ≤ (42282479811259/100000000000000 : ℝ)^15 := by
    have hnat : (2534157001 : ℕ)^19*100000000000000^15 ≤ 42282479811259^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534157001 5000000000 42282479811259 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064325021/10000000000 : ℝ)^19 ≤ (13553524035543/100000000000000 : ℝ)^15 := by
    have hnat : (2064325021 : ℕ)^19*100000000000000^15 ≤ 13553524035543^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064325021 10000000000 13553524035543 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655693421/1250000000 : ℝ)^19 ≤ (1380124879489/3125000000000 : ℝ)^15 := by
    have hnat : (655693421 : ℕ)^19*3125000000000^15 ≤ 1380124879489^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655693421 1250000000 1380124879489 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2534157001/5000000000 : ℝ), (-2064325021/10000000000 : ℝ), (-655693421/1250000000 : ℝ)] ![(42282479811259/100000000000000 : ℝ), (13553524035543/100000000000000 : ℝ), (1380124879489/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2534157001/5000000000 : ℝ)|^19 ≤ (42282479811259/100000000000000 : ℝ)^15
        have hw : |(2534157001/5000000000 : ℝ)|=(2534157001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064325021/10000000000 : ℝ)|^19 ≤ (13553524035543/100000000000000 : ℝ)^15
        have hw : |(-2064325021/10000000000 : ℝ)|=(2064325021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-655693421/1250000000 : ℝ)|^19 ≤ (1380124879489/3125000000000 : ℝ)^15
        have hw : |(-655693421/1250000000 : ℝ)|=(655693421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2889376381/5000000000 : ℝ)*x 0 + (4885103639/10000000000 : ℝ)*x 1 + (396896611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2889376381/5000000000 : ℝ)^19 ≤ (49925590598579/100000000000000 : ℝ)^15 := by
    have hnat : (2889376381 : ℕ)^19*100000000000000^15 ≤ 49925590598579^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2889376381 5000000000 49925590598579 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4885103639/10000000000 : ℝ)^19 ≤ (2522242316289/6250000000000 : ℝ)^15 := by
    have hnat : (4885103639 : ℕ)^19*6250000000000^15 ≤ 2522242316289^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885103639 10000000000 2522242316289 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396896611/2500000000 : ℝ)^19 ≤ (4859266165259/50000000000000 : ℝ)^15 := by
    have hnat : (396896611 : ℕ)^19*50000000000000^15 ≤ 4859266165259^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396896611 2500000000 4859266165259 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2889376381/5000000000 : ℝ), (4885103639/10000000000 : ℝ), (396896611/2500000000 : ℝ)] ![(49925590598579/100000000000000 : ℝ), (2522242316289/6250000000000 : ℝ), (4859266165259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2889376381/5000000000 : ℝ)|^19 ≤ (49925590598579/100000000000000 : ℝ)^15
        have hw : |(2889376381/5000000000 : ℝ)|=(2889376381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4885103639/10000000000 : ℝ)|^19 ≤ (2522242316289/6250000000000 : ℝ)^15
        have hw : |(4885103639/10000000000 : ℝ)|=(4885103639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396896611/2500000000 : ℝ)|^19 ≤ (4859266165259/50000000000000 : ℝ)^15
        have hw : |(396896611/2500000000 : ℝ)|=(396896611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1435418331/2500000000 : ℝ)*x 0 + (1000175199/2000000000 : ℝ)*x 1 + (-1482199739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1435418331/2500000000 : ℝ)^19 ≤ (9904032791373/20000000000000 : ℝ)^15 := by
    have hnat : (1435418331 : ℕ)^19*20000000000000^15 ≤ 9904032791373^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435418331 2500000000 9904032791373 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000175199/2000000000 : ℝ)^19 ≤ (20785559192819/50000000000000 : ℝ)^15 := by
    have hnat : (1000175199 : ℕ)^19*50000000000000^15 ≤ 20785559192819^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000175199 2000000000 20785559192819 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482199739/10000000000 : ℝ)^19 ≤ (4454358821707/50000000000000 : ℝ)^15 := by
    have hnat : (1482199739 : ℕ)^19*50000000000000^15 ≤ 4454358821707^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482199739 10000000000 4454358821707 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1435418331/2500000000 : ℝ), (1000175199/2000000000 : ℝ), (-1482199739/10000000000 : ℝ)] ![(9904032791373/20000000000000 : ℝ), (20785559192819/50000000000000 : ℝ), (4454358821707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1435418331/2500000000 : ℝ)|^19 ≤ (9904032791373/20000000000000 : ℝ)^15
        have hw : |(1435418331/2500000000 : ℝ)|=(1435418331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000175199/2000000000 : ℝ)|^19 ≤ (20785559192819/50000000000000 : ℝ)^15
        have hw : |(1000175199/2000000000 : ℝ)|=(1000175199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1482199739/10000000000 : ℝ)|^19 ≤ (4454358821707/50000000000000 : ℝ)^15
        have hw : |(-1482199739/10000000000 : ℝ)|=(1482199739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-10370989/156250000 : ℝ)*x 0 + (1011013211/2000000000 : ℝ)*x 1 + (-6205191353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10370989/156250000 : ℝ)^19 ≤ (322008142473/10000000000000 : ℝ)^15 := by
    have hnat : (10370989 : ℕ)^19*10000000000000^15 ≤ 322008142473^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10370989 156250000 322008142473 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011013211/2000000000 : ℝ)^19 ≤ (42142535136033/100000000000000 : ℝ)^15 := by
    have hnat : (1011013211 : ℕ)^19*100000000000000^15 ≤ 42142535136033^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011013211 2000000000 42142535136033 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6205191353/10000000000 : ℝ)^19 ≤ (27318691715259/50000000000000 : ℝ)^15 := by
    have hnat : (6205191353 : ℕ)^19*50000000000000^15 ≤ 27318691715259^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6205191353 10000000000 27318691715259 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10370989/156250000 : ℝ), (1011013211/2000000000 : ℝ), (-6205191353/10000000000 : ℝ)] ![(322008142473/10000000000000 : ℝ), (42142535136033/100000000000000 : ℝ), (27318691715259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10370989/156250000 : ℝ)|^19 ≤ (322008142473/10000000000000 : ℝ)^15
        have hw : |(-10370989/156250000 : ℝ)|=(10370989/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011013211/2000000000 : ℝ)|^19 ≤ (42142535136033/100000000000000 : ℝ)^15
        have hw : |(1011013211/2000000000 : ℝ)|=(1011013211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6205191353/10000000000 : ℝ)|^19 ≤ (27318691715259/50000000000000 : ℝ)^15
        have hw : |(-6205191353/10000000000 : ℝ)|=(6205191353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (770019431/1250000000 : ℝ)*x 0 + (-360013709/2000000000 : ℝ)*x 1 + (-4313404543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770019431/1250000000 : ℝ)^19 ≤ (54135578724429/100000000000000 : ℝ)^15 := by
    have hnat : (770019431 : ℕ)^19*100000000000000^15 ≤ 54135578724429^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770019431 1250000000 54135578724429 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360013709/2000000000 : ℝ)^19 ≤ (2848652428639/25000000000000 : ℝ)^15 := by
    have hnat : (360013709 : ℕ)^19*25000000000000^15 ≤ 2848652428639^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360013709 2000000000 2848652428639 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4313404543/10000000000 : ℝ)^19 ≤ (17234905776319/50000000000000 : ℝ)^15 := by
    have hnat : (4313404543 : ℕ)^19*50000000000000^15 ≤ 17234905776319^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313404543 10000000000 17234905776319 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(770019431/1250000000 : ℝ), (-360013709/2000000000 : ℝ), (-4313404543/10000000000 : ℝ)] ![(54135578724429/100000000000000 : ℝ), (2848652428639/25000000000000 : ℝ), (17234905776319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(770019431/1250000000 : ℝ)|^19 ≤ (54135578724429/100000000000000 : ℝ)^15
        have hw : |(770019431/1250000000 : ℝ)|=(770019431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360013709/2000000000 : ℝ)|^19 ≤ (2848652428639/25000000000000 : ℝ)^15
        have hw : |(-360013709/2000000000 : ℝ)|=(360013709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4313404543/10000000000 : ℝ)|^19 ≤ (17234905776319/50000000000000 : ℝ)^15
        have hw : |(-4313404543/10000000000 : ℝ)|=(4313404543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (501012491/1000000000 : ℝ)*x 0 + (640956771/1250000000 : ℝ)*x 1 + (571446083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501012491/1000000000 : ℝ)^19 ≤ (10417132222163/25000000000000 : ℝ)^15 := by
    have hnat : (501012491 : ℕ)^19*25000000000000^15 ≤ 10417132222163^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501012491 1000000000 10417132222163 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640956771/1250000000 : ℝ)^19 ≤ (5363814296947/12500000000000 : ℝ)^15 := by
    have hnat : (640956771 : ℕ)^19*12500000000000^15 ≤ 5363814296947^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640956771 1250000000 5363814296947 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571446083/2500000000 : ℝ)^19 ≤ (7710478364951/50000000000000 : ℝ)^15 := by
    have hnat : (571446083 : ℕ)^19*50000000000000^15 ≤ 7710478364951^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571446083 2500000000 7710478364951 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(501012491/1000000000 : ℝ), (640956771/1250000000 : ℝ), (571446083/2500000000 : ℝ)] ![(10417132222163/25000000000000 : ℝ), (5363814296947/12500000000000 : ℝ), (7710478364951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(501012491/1000000000 : ℝ)|^19 ≤ (10417132222163/25000000000000 : ℝ)^15
        have hw : |(501012491/1000000000 : ℝ)|=(501012491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640956771/1250000000 : ℝ)|^19 ≤ (5363814296947/12500000000000 : ℝ)^15
        have hw : |(640956771/1250000000 : ℝ)|=(640956771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571446083/2500000000 : ℝ)|^19 ≤ (7710478364951/50000000000000 : ℝ)^15
        have hw : |(571446083/2500000000 : ℝ)|=(571446083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s2_s2_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5427450089/10000000000 : ℝ)*x 0 + (1011311163/2000000000 : ℝ)*x 1 + (-184163847/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5427450089/10000000000 : ℝ)^19 ≤ (180128084181/390625000000 : ℝ)^15 := by
    have hnat : (5427450089 : ℕ)^19*390625000000^15 ≤ 180128084181^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427450089 10000000000 180128084181 390625000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011311163/2000000000 : ℝ)^19 ≤ (42158267338883/100000000000000 : ℝ)^15 := by
    have hnat : (1011311163 : ℕ)^19*100000000000000^15 ≤ 42158267338883^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011311163 2000000000 42158267338883 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184163847/1000000000 : ℝ)^19 ≤ (11728943095611/100000000000000 : ℝ)^15 := by
    have hnat : (184163847 : ℕ)^19*100000000000000^15 ≤ 11728943095611^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184163847 1000000000 11728943095611 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5427450089/10000000000 : ℝ), (1011311163/2000000000 : ℝ), (-184163847/1000000000 : ℝ)] ![(180128084181/390625000000 : ℝ), (42158267338883/100000000000000 : ℝ), (11728943095611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5427450089/10000000000 : ℝ)|^19 ≤ (180128084181/390625000000 : ℝ)^15
        have hw : |(5427450089/10000000000 : ℝ)|=(5427450089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011311163/2000000000 : ℝ)|^19 ≤ (42158267338883/100000000000000 : ℝ)^15
        have hw : |(1011311163/2000000000 : ℝ)|=(1011311163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-184163847/1000000000 : ℝ)|^19 ≤ (11728943095611/100000000000000 : ℝ)^15
        have hw : |(-184163847/1000000000 : ℝ)|=(184163847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315054_s2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((26977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28439/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28439/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-45201/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3507/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3507/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3701/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3701/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-467/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-467/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s2_pow0 : (26977/50000 : ℝ) ^ (75/16 : ℝ) ≤ (173265010732847551/3125000000000000000 : ℝ) := by
    have hpowers : (26977/50000 : ℝ)^75 ≤ (173265010732847551/3125000000000000000 : ℝ)^16 := by
      have hnat : (26977 : ℕ)^75*3125000000000000000^16 ≤ 173265010732847551^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26977 50000 173265010732847551 3125000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26977/50000 : ℝ)) (X := (173265010732847551/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (3298265010732847551/3125000000000000000 : ℝ) ≤ (5057892366718369/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3298265010732847551/3125000000000000000 : ℝ)^16 ≤ (5057892366718369/5000000000000000 : ℝ)^75 := by
      have hnat : (3298265010732847551 : ℕ)^16*5000000000000000^75 ≤ 5057892366718369^75*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3298265010732847551 3125000000000000000 5057892366718369 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057892366718369/5000000000000000 : ℝ)) (X := (3298265010732847551/3125000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (1735765010732847551/1562500000000000000 : ℝ) ≤ (1022687920064723/1000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (1735765010732847551/1562500000000000000 : ℝ)^16 ≤ (1022687920064723/1000000000000000 : ℝ)^75 := by
      have hnat : (1735765010732847551 : ℕ)^16*1000000000000000^75 ≤ 1022687920064723^75*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1735765010732847551 1562500000000000000 1022687920064723 1000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1022687920064723/1000000000000000 : ℝ)) (X := (1735765010732847551/1562500000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(57892366718369/2697700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(27773616802623/1348850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (26977/50000 : ℝ)) (alpha := (57892366718369/2697700000000000 : ℝ)) (beta := (27773616802623/1348850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (26977/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(57892366718369/2697700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(27773616802623/1348850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (28439/50000 : ℝ) ^ (75/16 : ℝ) ≤ (7100705250025585253/100000000000000000000 : ℝ) := by
    have hpowers : (28439/50000 : ℝ)^75 ≤ (7100705250025585253/100000000000000000000 : ℝ)^16 := by
      have hnat : (28439 : ℕ)^75*100000000000000000000^16 ≤ 7100705250025585253^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28439 50000 7100705250025585253 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28439/50000 : ℝ)) (X := (7100705250025585253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (107100705250025585253/100000000000000000000 : ℝ) ≤ (2536855356793101/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (107100705250025585253/100000000000000000000 : ℝ)^16 ≤ (2536855356793101/2500000000000000 : ℝ)^75 := by
      have hnat : (107100705250025585253 : ℕ)^16*2500000000000000^75 ≤ 2536855356793101^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107100705250025585253 100000000000000000000 2536855356793101 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2536855356793101/2500000000000000 : ℝ)) (X := (107100705250025585253/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (57100705250025585253/50000000000000000000 : ℝ) ≤ (80369872034063/78125000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (57100705250025585253/50000000000000000000 : ℝ)^16 ≤ (80369872034063/78125000000000 : ℝ)^75 := by
      have hnat : (57100705250025585253 : ℕ)^16*78125000000000^75 ≤ 80369872034063^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57100705250025585253 50000000000000000000 80369872034063 78125000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80369872034063/78125000000000 : ℝ)) (X := (57100705250025585253/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(36855356793101/1421950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6996109659383/284390000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (28439/50000 : ℝ)) (alpha := (36855356793101/1421950000000000 : ℝ)) (beta := (6996109659383/284390000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (28439/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(36855356793101/1421950000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6996109659383/284390000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (45201/100000 : ℝ) ^ (75/16 : ℝ) ≤ (1209139630800191871/50000000000000000000 : ℝ) := by
    have hpowers : (45201/100000 : ℝ)^75 ≤ (1209139630800191871/50000000000000000000 : ℝ)^16 := by
      have hnat : (45201 : ℕ)^75*50000000000000000000^16 ≤ 1209139630800191871^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45201 100000 1209139630800191871 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45201/100000 : ℝ)) (X := (1209139630800191871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (51209139630800191871/50000000000000000000 : ℝ) ≤ (10051106189639771/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (51209139630800191871/50000000000000000000 : ℝ)^16 ≤ (10051106189639771/10000000000000000 : ℝ)^75 := by
      have hnat : (51209139630800191871 : ℕ)^16*10000000000000000^75 ≤ 10051106189639771^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51209139630800191871 50000000000000000000 10051106189639771 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051106189639771/10000000000000000 : ℝ)) (X := (51209139630800191871/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (26209139630800191871/25000000000000000000 : ℝ) ≤ (1010127174291709/1000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (26209139630800191871/25000000000000000000 : ℝ)^16 ≤ (1010127174291709/1000000000000000 : ℝ)^75 := by
      have hnat : (26209139630800191871 : ℕ)^16*1000000000000000^75 ≤ 1010127174291709^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26209139630800191871 25000000000000000000 1010127174291709 1000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1010127174291709/1000000000000000 : ℝ)) (X := (26209139630800191871/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(51106189639771/4520100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(50165553277319/4520100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (45201/100000 : ℝ)) (alpha := (51106189639771/4520100000000000 : ℝ)) (beta := (50165553277319/4520100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (45201/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(51106189639771/4520100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(50165553277319/4520100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1306224899/10000000000 : ℝ)*X 0 0+(4525035987/10000000000 : ℝ)*X 0 1+(-3153855167/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1099984301/2000000000 : ℝ)*X 1 0+(-1156133173/5000000000 : ℝ)*X 1 1+(-2303018009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5111417391/10000000000 : ℝ)*X 2 0+(5088039489/10000000000 : ℝ)*X 2 1+(2209322899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5141676833/10000000000 : ℝ)*X 0 0+(1280558651/2500000000 : ℝ)*X 0 1+(-425659209/2000000000 : ℝ)*X 0 2+(5141676833/10000000000 : ℝ)*X 1 0+(1280558651/2500000000 : ℝ)*X 1 1+(-425659209/2000000000 : ℝ)*X 1 2+(5141676833/10000000000 : ℝ)*X 2 0+(1280558651/2500000000 : ℝ)*X 2 1+(-425659209/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-122589289/1000000000 : ℝ)*X 0 0+(105826729/250000000 : ℝ)*X 0 1+(-3311433011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5346537811/10000000000 : ℝ)*X 1 0+(-86287253/500000000 : ℝ)*X 1 1+(-104517399/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((490872059/1000000000 : ℝ)*X 2 0+(574216023/1000000000 : ℝ)*X 2 1+(1607262801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1010663833/2000000000 : ℝ)*X 0 0+(2879581039/5000000000 : ℝ)*X 0 1+(-1383571893/10000000000 : ℝ)*X 0 2+(1010663833/2000000000 : ℝ)*X 1 0+(2879581039/5000000000 : ℝ)*X 1 1+(-1383571893/10000000000 : ℝ)*X 1 2+(1010663833/2000000000 : ℝ)*X 2 0+(2879581039/5000000000 : ℝ)*X 2 1+(-1383571893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-430461421/5000000000 : ℝ)*X 0 0+(905185477/2000000000 : ℝ)*X 0 1+(-6583307217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2534157001/5000000000 : ℝ)*X 1 0+(-2064325021/10000000000 : ℝ)*X 1 1+(-655693421/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2889376381/5000000000 : ℝ)*X 2 0+(4885103639/10000000000 : ℝ)*X 2 1+(396896611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1435418331/2500000000 : ℝ)*X 0 0+(1000175199/2000000000 : ℝ)*X 0 1+(-1482199739/10000000000 : ℝ)*X 0 2+(1435418331/2500000000 : ℝ)*X 1 0+(1000175199/2000000000 : ℝ)*X 1 1+(-1482199739/10000000000 : ℝ)*X 1 2+(1435418331/2500000000 : ℝ)*X 2 0+(1000175199/2000000000 : ℝ)*X 2 1+(-1482199739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-10370989/156250000 : ℝ)*X 0 0+(1011013211/2000000000 : ℝ)*X 0 1+(-6205191353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((770019431/1250000000 : ℝ)*X 1 0+(-360013709/2000000000 : ℝ)*X 1 1+(-4313404543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((501012491/1000000000 : ℝ)*X 2 0+(640956771/1250000000 : ℝ)*X 2 1+(571446083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((5427450089/10000000000 : ℝ)*X 0 0+(1011311163/2000000000 : ℝ)*X 0 1+(-184163847/1000000000 : ℝ)*X 0 2+(5427450089/10000000000 : ℝ)*X 1 0+(1011311163/2000000000 : ℝ)*X 1 1+(-184163847/1000000000 : ℝ)*X 1 2+(5427450089/10000000000 : ℝ)*X 2 0+(1011311163/2000000000 : ℝ)*X 2 1+(-184163847/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((3507/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3507/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (362607849572732408572157231/60838873007900000000000000000000 : ℝ) := by norm_num
    linear_combination (1205394306869/1000000000000 : ℝ)*(base39) + (2563237/1000000000000 : ℝ)*(base50) + (301335433049/500000000000 : ℝ)*(base60) + (390793180793/50000000000 : ℝ)*(major_s2_0) + (390793180793/50000000000 : ℝ)*(major_s2_1) + (390793180793/50000000000 : ℝ)*(major_s2_2) + (43601553/1000000000000 : ℝ)*(sp_s2_0) + (11156700367313/1000000000000 : ℝ)*(sp_s2_7) + (11156661155193/1000000000000 : ℝ)*(sp_s2_8) + (1115673176029/100000000000 : ℝ)*(sp_s2_9) + (1118731874089/250000000000 : ℝ)*(sp_s2_13) + (6722473/125000000000 : ℝ)*(sp_s2_14) + (136593457/1000000000000 : ℝ)*(sp_s2_15) + (1649709/25000000000 : ℝ)*(sp_s2_23) + (1118731874089/250000000000 : ℝ)*(f.failure) + (223135954973/20000000000 : ℝ)*(f.sum) + (96960002822823121/676563810000000000000000000000 : ℝ)*base62 + (2159376906467/4758000000000000000000000 : ℝ)*base64 + (8543087894611/71097500000000000000000000 : ℝ)*base66 + (904644925591/23790000000000000000000000 : ℝ)*base69 + (41563886748157529/128356566000000000000000000000 : ℝ)*base70 + (301878599587/134885000000000000000000000 : ℝ)*base73 + (33982149958947/71097500000000000000000000 : ℝ)*base74 + (28290888613481/134885000000000000000000000 : ℝ)*base76 + (1513760633739679141/3835994515000000000000000000000 : ℝ)*base78 + (10651/25000000000000000 : ℝ)*base87 + (10651/25000000000000000 : ℝ)*base89 + (10651/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3701/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3701/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15918009641107533201380857/1071226032500000000000000000000 : ℝ) := by norm_num
    linear_combination (570714439717/500000000000 : ℝ)*(base39) + (6769211/1000000000000 : ℝ)*(base40) + (16016743857/50000000000 : ℝ)*(base60) + (7830383117057/1000000000000 : ℝ)*(major_s2_0) + (7830383117057/1000000000000 : ℝ)*(major_s2_1) + (7830383117057/1000000000000 : ℝ)*(major_s2_2) + (2692613/50000000000 : ℝ)*(sp_s2_2) + (47907191/250000000000 : ℝ)*(sp_s2_7) + (163919173/1000000000000 : ℝ)*(sp_s2_8) + (2794332274843/250000000000 : ℝ)*(sp_s2_14) + (2794339202241/250000000000 : ℝ)*(sp_s2_15) + (11177466875877/1000000000000 : ℝ)*(sp_s2_16) + (1120797043137/250000000000 : ℝ)*(sp_s2_20) + (52380219/1000000000000 : ℝ)*(sp_s2_27) + (4483240552767/1000000000000 : ℝ)*(f.failure) + (11177520728137/1000000000000 : ℝ)*(f.sum) + (19165152182471333963/128547123900000000000000000000000 : ℝ)*base62 + (84056309178133/4520100000000000000000000000 : ℝ)*base65 + (3290118021461/56878000000000000000000000 : ℝ)*base66 + (2781295111806793/4520100000000000000000000000 : ℝ)*base68 + (26982945686526691127/60969368850000000000000000000000 : ℝ)*base71 + (504130171160051/1348850000000000000000000000 : ℝ)*base73 + (385904115165379/710975000000000000000000000 : ℝ)*base74 + (652187718973727/2697700000000000000000000000 : ℝ)*base76 + (1159168541135409687/4794993143750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (31453/100000000000000000 : ℝ)*base87 + (31453/100000000000000000 : ℝ)*base89 + (31453/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-467/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-467/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36318954633730057339870698759/9474906452050000000000000000000000 : ℝ) := by norm_num
    linear_combination (1257752894937/1000000000000 : ℝ)*(base39) + (52163/250000000000 : ℝ)*(base50) + (2796832240887/500000000000 : ℝ)*(major_s2_0) + (2796832240887/500000000000 : ℝ)*(major_s2_1) + (2796832240887/500000000000 : ℝ)*(major_s2_2) + (6622801/1000000000000 : ℝ)*(sp_s2_0) + (18240819/1000000000000 : ℝ)*(sp_s2_1) + (47488117/250000000000 : ℝ)*(sp_s2_2) + (62787/1000000000000 : ℝ)*(sp_s2_6) + (500913/500000000000 : ℝ)*(sp_s2_9) + (159694016497/20000000000 : ℝ)*(sp_s2_21) + (7984689206833/1000000000000 : ℝ)*(sp_s2_22) + (7984516493357/1000000000000 : ℝ)*(sp_s2_23) + (3202620175377/1000000000000 : ℝ)*(sp_s2_27) + (3202620238163/1000000000000 : ℝ)*(f.failure) + (7984707447651/1000000000000 : ℝ)*(f.sum) + (121767036635353803/175610825000000000000000000000 : ℝ)*base62 + (1917479578291/12350000000000000000000000 : ℝ)*base65 + (208226660868471/284390000000000000000000000 : ℝ)*base66 + (2520558682693/6175000000000000000000000 : ℝ)*base68 + (16544457771045683/83291487500000000000000000000 : ℝ)*base70 + (83034585309597/337212500000000000000000000 : ℝ)*base72 + (30090549391327/177743750000000000000000000 : ℝ)*base74 + (31295031025071/168606250000000000000000000 : ℝ)*base77 + (18502584750275418147/38359945150000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (88583/100000000000000000 : ℝ)*base86 + (88583/100000000000000000 : ℝ)*base88 + (88583/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((26977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28439/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28439/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-45201/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3507/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3507/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3701/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3701/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-467/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-467/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315054_s2 p hpa hpb X hX hprev1

#print axioms solution

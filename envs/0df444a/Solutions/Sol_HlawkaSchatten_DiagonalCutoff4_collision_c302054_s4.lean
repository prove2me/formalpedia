-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302054_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:38.497482+00:00
-- url     : https://prove2.me/submissions/6f03575b-f23a-4e97-9b69-24f2c3af5484

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
theorem collision_support_c302054_s4_s4_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-134921077/1000000000 : ℝ)*x 0 + (1123703417/2500000000 : ℝ)*x 1 + (-6626803047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134921077/1000000000 : ℝ)^33 ≤ (7107311252273/100000000000000 : ℝ)^25 := by
    have hnat : (134921077 : ℕ)^33*100000000000000^25 ≤ 7107311252273^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134921077 1000000000 7107311252273 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123703417/2500000000 : ℝ)^33 ≤ (34800015270099/100000000000000 : ℝ)^25 := by
    have hnat : (1123703417 : ℕ)^33*100000000000000^25 ≤ 34800015270099^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123703417 2500000000 34800015270099 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6626803047/10000000000 : ℝ)^33 ≤ (29046336734969/50000000000000 : ℝ)^25 := by
    have hnat : (6626803047 : ℕ)^33*50000000000000^25 ≤ 29046336734969^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6626803047 10000000000 29046336734969 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134921077/1000000000 : ℝ), (1123703417/2500000000 : ℝ), (-6626803047/10000000000 : ℝ)] ![(7107311252273/100000000000000 : ℝ), (34800015270099/100000000000000 : ℝ), (29046336734969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134921077/1000000000 : ℝ)|^33 ≤ (7107311252273/100000000000000 : ℝ)^25
        have hw : |(-134921077/1000000000 : ℝ)|=(134921077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123703417/2500000000 : ℝ)|^33 ≤ (34800015270099/100000000000000 : ℝ)^25
        have hw : |(1123703417/2500000000 : ℝ)|=(1123703417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6626803047/10000000000 : ℝ)|^33 ≤ (29046336734969/50000000000000 : ℝ)^25
        have hw : |(-6626803047/10000000000 : ℝ)|=(6626803047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5294273871/10000000000 : ℝ)*x 0 + (5249767987/10000000000 : ℝ)*x 1 + (283241027/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294273871/10000000000 : ℝ)^33 ≤ (21597051151773/50000000000000 : ℝ)^25 := by
    have hnat : (5294273871 : ℕ)^33*50000000000000^25 ≤ 21597051151773^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294273871 10000000000 21597051151773 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5249767987/10000000000 : ℝ)^33 ≤ (4271544602223/10000000000000 : ℝ)^25 := by
    have hnat : (5249767987 : ℕ)^33*10000000000000^25 ≤ 4271544602223^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249767987 10000000000 4271544602223 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283241027/1250000000 : ℝ)^33 ≤ (14090451667549/100000000000000 : ℝ)^25 := by
    have hnat : (283241027 : ℕ)^33*100000000000000^25 ≤ 14090451667549^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283241027 1250000000 14090451667549 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294273871/10000000000 : ℝ), (5249767987/10000000000 : ℝ), (283241027/1250000000 : ℝ)] ![(21597051151773/50000000000000 : ℝ), (4271544602223/10000000000000 : ℝ), (14090451667549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294273871/10000000000 : ℝ)|^33 ≤ (21597051151773/50000000000000 : ℝ)^25
        have hw : |(5294273871/10000000000 : ℝ)|=(5294273871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5249767987/10000000000 : ℝ)|^33 ≤ (4271544602223/10000000000000 : ℝ)^25
        have hw : |(5249767987/10000000000 : ℝ)|=(5249767987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283241027/1250000000 : ℝ)|^33 ≤ (14090451667549/100000000000000 : ℝ)^25
        have hw : |(283241027/1250000000 : ℝ)|=(283241027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-262712397/2500000000 : ℝ)*x 0 + (236522609/625000000 : ℝ)*x 1 + (-7396434033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262712397/2500000000 : ℝ)^33 ≤ (1277537172399/25000000000000 : ℝ)^25 := by
    have hnat : (262712397 : ℕ)^33*25000000000000^25 ≤ 1277537172399^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262712397 2500000000 1277537172399 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236522609/625000000 : ℝ)^33 ≤ (6932506703139/25000000000000 : ℝ)^25 := by
    have hnat : (236522609 : ℕ)^33*25000000000000^25 ≤ 6932506703139^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236522609 625000000 6932506703139 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7396434033/10000000000 : ℝ)^33 ≤ (4197489030191/6250000000000 : ℝ)^25 := by
    have hnat : (7396434033 : ℕ)^33*6250000000000^25 ≤ 4197489030191^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7396434033 10000000000 4197489030191 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262712397/2500000000 : ℝ), (236522609/625000000 : ℝ), (-7396434033/10000000000 : ℝ)] ![(1277537172399/25000000000000 : ℝ), (6932506703139/25000000000000 : ℝ), (4197489030191/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262712397/2500000000 : ℝ)|^33 ≤ (1277537172399/25000000000000 : ℝ)^25
        have hw : |(-262712397/2500000000 : ℝ)|=(262712397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(236522609/625000000 : ℝ)|^33 ≤ (6932506703139/25000000000000 : ℝ)^25
        have hw : |(236522609/625000000 : ℝ)|=(236522609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7396434033/10000000000 : ℝ)|^33 ≤ (4197489030191/6250000000000 : ℝ)^25
        have hw : |(-7396434033/10000000000 : ℝ)|=(7396434033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5147025343/10000000000 : ℝ)*x 0 + (-1427227317/10000000000 : ℝ)*x 1 + (-299009293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5147025343/10000000000 : ℝ)^33 ≤ (41615424091253/100000000000000 : ℝ)^25 := by
    have hnat : (5147025343 : ℕ)^33*100000000000000^25 ≤ 41615424091253^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147025343 10000000000 41615424091253 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1427227317/10000000000 : ℝ)^33 ≤ (7654749045661/100000000000000 : ℝ)^25 := by
    have hnat : (1427227317 : ℕ)^33*100000000000000^25 ≤ 7654749045661^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427227317 10000000000 7654749045661 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299009293/500000000 : ℝ)^33 ≤ (396326772209/781250000000 : ℝ)^25 := by
    have hnat : (299009293 : ℕ)^33*781250000000^25 ≤ 396326772209^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299009293 500000000 396326772209 781250000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5147025343/10000000000 : ℝ), (-1427227317/10000000000 : ℝ), (-299009293/500000000 : ℝ)] ![(41615424091253/100000000000000 : ℝ), (7654749045661/100000000000000 : ℝ), (396326772209/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5147025343/10000000000 : ℝ)|^33 ≤ (41615424091253/100000000000000 : ℝ)^25
        have hw : |(5147025343/10000000000 : ℝ)|=(5147025343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1427227317/10000000000 : ℝ)|^33 ≤ (7654749045661/100000000000000 : ℝ)^25
        have hw : |(-1427227317/10000000000 : ℝ)|=(1427227317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299009293/500000000 : ℝ)|^33 ≤ (396326772209/781250000000 : ℝ)^25
        have hw : |(-299009293/500000000 : ℝ)|=(299009293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1175288417/2500000000 : ℝ)*x 0 + (6579610841/10000000000 : ℝ)*x 1 + (278856861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1175288417/2500000000 : ℝ)^33 ≤ (36924095919039/100000000000000 : ℝ)^25 := by
    have hnat : (1175288417 : ℕ)^33*100000000000000^25 ≤ 36924095919039^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175288417 2500000000 36924095919039 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6579610841/10000000000 : ℝ)^33 ≤ (460377680917/800000000000 : ℝ)^25 := by
    have hnat : (6579610841 : ℕ)^33*800000000000^25 ≤ 460377680917^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6579610841 10000000000 460377680917 800000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278856861/2500000000 : ℝ)^33 ≤ (5528693954833/100000000000000 : ℝ)^25 := by
    have hnat : (278856861 : ℕ)^33*100000000000000^25 ≤ 5528693954833^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278856861 2500000000 5528693954833 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1175288417/2500000000 : ℝ), (6579610841/10000000000 : ℝ), (278856861/2500000000 : ℝ)] ![(36924095919039/100000000000000 : ℝ), (460377680917/800000000000 : ℝ), (5528693954833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1175288417/2500000000 : ℝ)|^33 ≤ (36924095919039/100000000000000 : ℝ)^25
        have hw : |(1175288417/2500000000 : ℝ)|=(1175288417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6579610841/10000000000 : ℝ)|^33 ≤ (460377680917/800000000000 : ℝ)^25
        have hw : |(6579610841/10000000000 : ℝ)|=(6579610841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(278856861/2500000000 : ℝ)|^33 ≤ (5528693954833/100000000000000 : ℝ)^25
        have hw : |(278856861/2500000000 : ℝ)|=(278856861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4862786053/10000000000 : ℝ)*x 0 + (3223667983/5000000000 : ℝ)*x 1 + (-218094063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4862786053/10000000000 : ℝ)^33 ≤ (19304493828471/50000000000000 : ℝ)^25 := by
    have hnat : (4862786053 : ℕ)^33*50000000000000^25 ≤ 19304493828471^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862786053 10000000000 19304493828471 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3223667983/5000000000 : ℝ)^33 ≤ (28012508570067/50000000000000 : ℝ)^25 := by
    have hnat : (3223667983 : ℕ)^33*50000000000000^25 ≤ 28012508570067^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3223667983 5000000000 28012508570067 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218094063/2000000000 : ℝ)^33 ≤ (335374699239/6250000000000 : ℝ)^25 := by
    have hnat : (218094063 : ℕ)^33*6250000000000^25 ≤ 335374699239^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218094063 2000000000 335374699239 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4862786053/10000000000 : ℝ), (3223667983/5000000000 : ℝ), (-218094063/2000000000 : ℝ)] ![(19304493828471/50000000000000 : ℝ), (28012508570067/50000000000000 : ℝ), (335374699239/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4862786053/10000000000 : ℝ)|^33 ≤ (19304493828471/50000000000000 : ℝ)^25
        have hw : |(4862786053/10000000000 : ℝ)|=(4862786053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3223667983/5000000000 : ℝ)|^33 ≤ (28012508570067/50000000000000 : ℝ)^25
        have hw : |(3223667983/5000000000 : ℝ)|=(3223667983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218094063/2000000000 : ℝ)|^33 ≤ (335374699239/6250000000000 : ℝ)^25
        have hw : |(-218094063/2000000000 : ℝ)|=(218094063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-227754611/5000000000 : ℝ)*x 0 + (132748133/312500000 : ℝ)*x 1 + (-7299909669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227754611/5000000000 : ℝ)^33 ≤ (6780727021/400000000000 : ℝ)^25 := by
    have hnat : (227754611 : ℕ)^33*400000000000^25 ≤ 6780727021^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227754611 5000000000 6780727021 400000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132748133/312500000 : ℝ)^33 ≤ (32299476846219/100000000000000 : ℝ)^25 := by
    have hnat : (132748133 : ℕ)^33*100000000000000^25 ≤ 32299476846219^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132748133 312500000 32299476846219 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7299909669/10000000000 : ℝ)^33 ≤ (33002670694033/50000000000000 : ℝ)^25 := by
    have hnat : (7299909669 : ℕ)^33*50000000000000^25 ≤ 33002670694033^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7299909669 10000000000 33002670694033 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227754611/5000000000 : ℝ), (132748133/312500000 : ℝ), (-7299909669/10000000000 : ℝ)] ![(6780727021/400000000000 : ℝ), (32299476846219/100000000000000 : ℝ), (33002670694033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227754611/5000000000 : ℝ)|^33 ≤ (6780727021/400000000000 : ℝ)^25
        have hw : |(-227754611/5000000000 : ℝ)|=(227754611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132748133/312500000 : ℝ)|^33 ≤ (32299476846219/100000000000000 : ℝ)^25
        have hw : |(132748133/312500000 : ℝ)|=(132748133/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7299909669/10000000000 : ℝ)|^33 ≤ (33002670694033/50000000000000 : ℝ)^25
        have hw : |(-7299909669/10000000000 : ℝ)|=(7299909669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4718971847/10000000000 : ℝ)*x 0 + (-1989315609/10000000000 : ℝ)*x 1 + (-1501642723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4718971847/10000000000 : ℝ)^33 ≤ (18554470039609/50000000000000 : ℝ)^25 := by
    have hnat : (4718971847 : ℕ)^33*50000000000000^25 ≤ 18554470039609^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718971847 10000000000 18554470039609 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989315609/10000000000 : ℝ)^33 ≤ (11865577252221/100000000000000 : ℝ)^25 := by
    have hnat : (1989315609 : ℕ)^33*100000000000000^25 ≤ 11865577252221^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989315609 10000000000 11865577252221 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1501642723/2500000000 : ℝ)^33 ≤ (25512741328143/50000000000000 : ℝ)^25 := by
    have hnat : (1501642723 : ℕ)^33*50000000000000^25 ≤ 25512741328143^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501642723 2500000000 25512741328143 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4718971847/10000000000 : ℝ), (-1989315609/10000000000 : ℝ), (-1501642723/2500000000 : ℝ)] ![(18554470039609/50000000000000 : ℝ), (11865577252221/100000000000000 : ℝ), (25512741328143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4718971847/10000000000 : ℝ)|^33 ≤ (18554470039609/50000000000000 : ℝ)^25
        have hw : |(4718971847/10000000000 : ℝ)|=(4718971847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989315609/10000000000 : ℝ)|^33 ≤ (11865577252221/100000000000000 : ℝ)^25
        have hw : |(-1989315609/10000000000 : ℝ)|=(1989315609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1501642723/2500000000 : ℝ)|^33 ≤ (25512741328143/50000000000000 : ℝ)^25
        have hw : |(-1501642723/2500000000 : ℝ)|=(1501642723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6640552323/10000000000 : ℝ)*x 0 + (4649686279/10000000000 : ℝ)*x 1 + (1089044403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6640552323/10000000000 : ℝ)^33 ≤ (11650365316863/20000000000000 : ℝ)^25 := by
    have hnat : (6640552323 : ℕ)^33*20000000000000^25 ≤ 11650365316863^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6640552323 10000000000 11650365316863 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4649686279/10000000000 : ℝ)^33 ≤ (568616222517/1562500000000 : ℝ)^25 := by
    have hnat : (4649686279 : ℕ)^33*1562500000000^25 ≤ 568616222517^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4649686279 10000000000 568616222517 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089044403/10000000000 : ℝ)^33 ≤ (669591895277/12500000000000 : ℝ)^25 := by
    have hnat : (1089044403 : ℕ)^33*12500000000000^25 ≤ 669591895277^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089044403 10000000000 669591895277 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6640552323/10000000000 : ℝ), (4649686279/10000000000 : ℝ), (1089044403/10000000000 : ℝ)] ![(11650365316863/20000000000000 : ℝ), (568616222517/1562500000000 : ℝ), (669591895277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6640552323/10000000000 : ℝ)|^33 ≤ (11650365316863/20000000000000 : ℝ)^25
        have hw : |(6640552323/10000000000 : ℝ)|=(6640552323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4649686279/10000000000 : ℝ)|^33 ≤ (568616222517/1562500000000 : ℝ)^25
        have hw : |(4649686279/10000000000 : ℝ)|=(4649686279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089044403/10000000000 : ℝ)|^33 ≤ (669591895277/12500000000000 : ℝ)^25
        have hw : |(1089044403/10000000000 : ℝ)|=(1089044403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6400063767/10000000000 : ℝ)*x 0 + (2396218383/5000000000 : ℝ)*x 1 + (-640958143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6400063767/10000000000 : ℝ)^33 ≤ (55483426936231/100000000000000 : ℝ)^25 := by
    have hnat : (6400063767 : ℕ)^33*100000000000000^25 ≤ 55483426936231^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6400063767 10000000000 55483426936231 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396218383/5000000000 : ℝ)^33 ≤ (2367088272813/6250000000000 : ℝ)^25 := by
    have hnat : (2396218383 : ℕ)^33*6250000000000^25 ≤ 2367088272813^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396218383 5000000000 2367088272813 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640958143/5000000000 : ℝ)^33 ≤ (3321580346643/50000000000000 : ℝ)^25 := by
    have hnat : (640958143 : ℕ)^33*50000000000000^25 ≤ 3321580346643^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640958143 5000000000 3321580346643 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6400063767/10000000000 : ℝ), (2396218383/5000000000 : ℝ), (-640958143/5000000000 : ℝ)] ![(55483426936231/100000000000000 : ℝ), (2367088272813/6250000000000 : ℝ), (3321580346643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6400063767/10000000000 : ℝ)|^33 ≤ (55483426936231/100000000000000 : ℝ)^25
        have hw : |(6400063767/10000000000 : ℝ)|=(6400063767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2396218383/5000000000 : ℝ)|^33 ≤ (2367088272813/6250000000000 : ℝ)^25
        have hw : |(2396218383/5000000000 : ℝ)|=(2396218383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-640958143/5000000000 : ℝ)|^33 ≤ (3321580346643/50000000000000 : ℝ)^25
        have hw : |(-640958143/5000000000 : ℝ)|=(640958143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-220594859/10000000000 : ℝ)*x 0 + (5397423923/10000000000 : ℝ)*x 1 + (-1272266423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220594859/10000000000 : ℝ)^33 ≤ (130189484209/20000000000000 : ℝ)^25 := by
    have hnat : (220594859 : ℕ)^33*20000000000000^25 ≤ 130189484209^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220594859 10000000000 130189484209 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397423923/10000000000 : ℝ)^33 ≤ (44308415448539/100000000000000 : ℝ)^25 := by
    have hnat : (5397423923 : ℕ)^33*100000000000000^25 ≤ 44308415448539^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397423923 10000000000 44308415448539 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272266423/2000000000 : ℝ)^33 ≤ (55040637117193/100000000000000 : ℝ)^25 := by
    have hnat : (1272266423 : ℕ)^33*100000000000000^25 ≤ 55040637117193^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272266423 2000000000 55040637117193 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220594859/10000000000 : ℝ), (5397423923/10000000000 : ℝ), (-1272266423/2000000000 : ℝ)] ![(130189484209/20000000000000 : ℝ), (44308415448539/100000000000000 : ℝ), (55040637117193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220594859/10000000000 : ℝ)|^33 ≤ (130189484209/20000000000000 : ℝ)^25
        have hw : |(-220594859/10000000000 : ℝ)|=(220594859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397423923/10000000000 : ℝ)|^33 ≤ (44308415448539/100000000000000 : ℝ)^25
        have hw : |(5397423923/10000000000 : ℝ)|=(5397423923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1272266423/2000000000 : ℝ)|^33 ≤ (55040637117193/100000000000000 : ℝ)^25
        have hw : |(-1272266423/2000000000 : ℝ)|=(1272266423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6822818069/10000000000 : ℝ)*x 0 + (-170914753/1000000000 : ℝ)*x 1 + (-4008409713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6822818069/10000000000 : ℝ)^33 ≤ (241486132059/400000000000 : ℝ)^25 := by
    have hnat : (6822818069 : ℕ)^33*400000000000^25 ≤ 241486132059^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6822818069 10000000000 241486132059 400000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170914753/1000000000 : ℝ)^33 ≤ (9711113013449/100000000000000 : ℝ)^25 := by
    have hnat : (170914753 : ℕ)^33*100000000000000^25 ≤ 9711113013449^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170914753 1000000000 9711113013449 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008409713/10000000000 : ℝ)^33 ≤ (29917353957669/100000000000000 : ℝ)^25 := by
    have hnat : (4008409713 : ℕ)^33*100000000000000^25 ≤ 29917353957669^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008409713 10000000000 29917353957669 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6822818069/10000000000 : ℝ), (-170914753/1000000000 : ℝ), (-4008409713/10000000000 : ℝ)] ![(241486132059/400000000000 : ℝ), (9711113013449/100000000000000 : ℝ), (29917353957669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6822818069/10000000000 : ℝ)|^33 ≤ (241486132059/400000000000 : ℝ)^25
        have hw : |(6822818069/10000000000 : ℝ)|=(6822818069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170914753/1000000000 : ℝ)|^33 ≤ (9711113013449/100000000000000 : ℝ)^25
        have hw : |(-170914753/1000000000 : ℝ)|=(170914753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4008409713/10000000000 : ℝ)|^33 ≤ (29917353957669/100000000000000 : ℝ)^25
        have hw : |(-4008409713/10000000000 : ℝ)|=(4008409713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4847715477/10000000000 : ℝ)*x 0 + (5597890283/10000000000 : ℝ)*x 1 + (297816883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4847715477/10000000000 : ℝ)^33 ≤ (9612780153183/25000000000000 : ℝ)^25 := by
    have hnat : (4847715477 : ℕ)^33*25000000000000^25 ≤ 9612780153183^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847715477 10000000000 9612780153183 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597890283/10000000000 : ℝ)^33 ≤ (46493493967251/100000000000000 : ℝ)^25 := by
    have hnat : (5597890283 : ℕ)^33*100000000000000^25 ≤ 46493493967251^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597890283 10000000000 46493493967251 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297816883/1250000000 : ℝ)^33 ≤ (3763846348169/25000000000000 : ℝ)^25 := by
    have hnat : (297816883 : ℕ)^33*25000000000000^25 ≤ 3763846348169^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297816883 1250000000 3763846348169 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4847715477/10000000000 : ℝ), (5597890283/10000000000 : ℝ), (297816883/1250000000 : ℝ)] ![(9612780153183/25000000000000 : ℝ), (46493493967251/100000000000000 : ℝ), (3763846348169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4847715477/10000000000 : ℝ)|^33 ≤ (9612780153183/25000000000000 : ℝ)^25
        have hw : |(4847715477/10000000000 : ℝ)|=(4847715477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5597890283/10000000000 : ℝ)|^33 ≤ (46493493967251/100000000000000 : ℝ)^25
        have hw : |(5597890283/10000000000 : ℝ)|=(5597890283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297816883/1250000000 : ℝ)|^33 ≤ (3763846348169/25000000000000 : ℝ)^25
        have hw : |(297816883/1250000000 : ℝ)|=(297816883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s4_s4_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6249135853/10000000000 : ℝ)*x 0 + (4635971321/10000000000 : ℝ)*x 1 + (-872925219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6249135853/10000000000 : ℝ)^33 ≤ (26881429481577/50000000000000 : ℝ)^25 := by
    have hnat : (6249135853 : ℕ)^33*50000000000000^25 ≤ 26881429481577^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6249135853 10000000000 26881429481577 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4635971321/10000000000 : ℝ)^33 ≤ (724996271929/2000000000000 : ℝ)^25 := by
    have hnat : (4635971321 : ℕ)^33*2000000000000^25 ≤ 724996271929^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635971321 10000000000 724996271929 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (872925219/5000000000 : ℝ)^33 ≤ (4993663709563/50000000000000 : ℝ)^25 := by
    have hnat : (872925219 : ℕ)^33*50000000000000^25 ≤ 4993663709563^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872925219 5000000000 4993663709563 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6249135853/10000000000 : ℝ), (4635971321/10000000000 : ℝ), (-872925219/5000000000 : ℝ)] ![(26881429481577/50000000000000 : ℝ), (724996271929/2000000000000 : ℝ), (4993663709563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6249135853/10000000000 : ℝ)|^33 ≤ (26881429481577/50000000000000 : ℝ)^25
        have hw : |(6249135853/10000000000 : ℝ)|=(6249135853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4635971321/10000000000 : ℝ)|^33 ≤ (724996271929/2000000000000 : ℝ)^25
        have hw : |(4635971321/10000000000 : ℝ)|=(4635971321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-872925219/5000000000 : ℝ)|^33 ≤ (4993663709563/50000000000000 : ℝ)^25
        have hw : |(-872925219/5000000000 : ℝ)|=(872925219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302054_s4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((62397/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62397/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8199/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8199/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50523/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50523/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44621/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44621/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9303/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9303/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-15807/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-15807/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (62397/100000 : ℝ) ^ (65/16 : ℝ) ≤ (7359063912636121801/50000000000000000000 : ℝ) := by
    have hpowers : (62397/100000 : ℝ)^65 ≤ (7359063912636121801/50000000000000000000 : ℝ)^16 := by
      have hnat : (62397 : ℕ)^65*50000000000000000000^16 ≤ 7359063912636121801^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62397 100000 7359063912636121801 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62397/100000 : ℝ)) (X := (7359063912636121801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (57359063912636121801/50000000000000000000 : ℝ) ≤ (5171882659674411/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (57359063912636121801/50000000000000000000 : ℝ)^16 ≤ (5171882659674411/5000000000000000 : ℝ)^65 := by
      have hnat : (57359063912636121801 : ℕ)^16*5000000000000000^65 ≤ 5171882659674411^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57359063912636121801 50000000000000000000 5171882659674411 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5171882659674411/5000000000000000 : ℝ)) (X := (57359063912636121801/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (32359063912636121801/25000000000000000000 : ℝ) ≤ (5327862464080841/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (32359063912636121801/25000000000000000000 : ℝ)^16 ≤ (5327862464080841/5000000000000000 : ℝ)^65 := by
      have hnat : (32359063912636121801 : ℕ)^16*5000000000000000^65 ≤ 5327862464080841^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32359063912636121801 25000000000000000000 5327862464080841 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5327862464080841/5000000000000000 : ℝ)) (X := (32359063912636121801/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(171882659674411/3119850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15597980440643/311985000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (62397/100000 : ℝ)) (alpha := (171882659674411/3119850000000000 : ℝ)) (beta := (15597980440643/311985000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62397/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(171882659674411/3119850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15597980440643/311985000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (8199/12500 : ℝ) ^ (65/16 : ℝ) ≤ (18028378742321819173/100000000000000000000 : ℝ) := by
    have hpowers : (8199/12500 : ℝ)^65 ≤ (18028378742321819173/100000000000000000000 : ℝ)^16 := by
      have hnat : (8199 : ℕ)^65*100000000000000000000^16 ≤ 18028378742321819173^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8199 12500 18028378742321819173 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8199/12500 : ℝ)) (X := (18028378742321819173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (118028378742321819173/100000000000000000000 : ℝ) ≤ (10416450142353891/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (118028378742321819173/100000000000000000000 : ℝ)^16 ≤ (10416450142353891/10000000000000000 : ℝ)^65 := by
      have hnat : (118028378742321819173 : ℕ)^16*10000000000000000^65 ≤ 10416450142353891^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118028378742321819173 100000000000000000000 10416450142353891 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10416450142353891/10000000000000000 : ℝ)) (X := (118028378742321819173/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (68028378742321819173/50000000000000000000 : ℝ) ≤ (2157474725272459/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (68028378742321819173/50000000000000000000 : ℝ)^16 ≤ (2157474725272459/2000000000000000 : ℝ)^65 := by
      have hnat : (68028378742321819173 : ℕ)^16*2000000000000000^65 ≤ 2157474725272459^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68028378742321819173 50000000000000000000 2157474725272459 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2157474725272459/2000000000000000 : ℝ)) (X := (68028378742321819173/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(416450142353891/6559200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(92730871002101/1639800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (8199/12500 : ℝ)) (alpha := (416450142353891/6559200000000000 : ℝ)) (beta := (92730871002101/1639800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8199/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(416450142353891/6559200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(92730871002101/1639800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (50523/100000 : ℝ) ^ (65/16 : ℝ) ≤ (3121724675812373499/50000000000000000000 : ℝ) := by
    have hpowers : (50523/100000 : ℝ)^65 ≤ (3121724675812373499/50000000000000000000 : ℝ)^16 := by
      have hnat : (50523 : ℕ)^65*50000000000000000000^16 ≤ 3121724675812373499^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50523 100000 3121724675812373499 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50523/100000 : ℝ)) (X := (3121724675812373499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (53121724675812373499/50000000000000000000 : ℝ) ≤ (10150194828149807/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (53121724675812373499/50000000000000000000 : ℝ)^16 ≤ (10150194828149807/10000000000000000 : ℝ)^65 := by
      have hnat : (53121724675812373499 : ℕ)^16*10000000000000000^65 ≤ 10150194828149807^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53121724675812373499 50000000000000000000 10150194828149807 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10150194828149807/10000000000000000 : ℝ)) (X := (53121724675812373499/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (28121724675812373499/25000000000000000000 : ℝ) ≤ (10293876176766297/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (28121724675812373499/25000000000000000000 : ℝ)^16 ≤ (10293876176766297/10000000000000000 : ℝ)^65 := by
      have hnat : (28121724675812373499 : ℕ)^16*10000000000000000^65 ≤ 10293876176766297^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28121724675812373499 25000000000000000000 10293876176766297 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10293876176766297/10000000000000000 : ℝ)) (X := (28121724675812373499/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(150194828149807/5052300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14368134861649/505230000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (50523/100000 : ℝ)) (alpha := (150194828149807/5052300000000000 : ℝ)) (beta := (14368134861649/505230000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (50523/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(150194828149807/5052300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14368134861649/505230000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-134921077/1000000000 : ℝ)*X 0 0+(1123703417/2500000000 : ℝ)*X 0 1+(-6626803047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((5294273871/10000000000 : ℝ)*X 2 0+(5249767987/10000000000 : ℝ)*X 2 1+(283241027/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-262712397/2500000000 : ℝ)*X 0 0+(236522609/625000000 : ℝ)*X 0 1+(-7396434033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((5147025343/10000000000 : ℝ)*X 1 0+(-1427227317/10000000000 : ℝ)*X 1 1+(-299009293/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1175288417/2500000000 : ℝ)*X 2 0+(6579610841/10000000000 : ℝ)*X 2 1+(278856861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((4862786053/10000000000 : ℝ)*X 0 0+(3223667983/5000000000 : ℝ)*X 0 1+(-218094063/2000000000 : ℝ)*X 0 2+(4862786053/10000000000 : ℝ)*X 1 0+(3223667983/5000000000 : ℝ)*X 1 1+(-218094063/2000000000 : ℝ)*X 1 2+(4862786053/10000000000 : ℝ)*X 2 0+(3223667983/5000000000 : ℝ)*X 2 1+(-218094063/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-227754611/5000000000 : ℝ)*X 0 0+(132748133/312500000 : ℝ)*X 0 1+(-7299909669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4718971847/10000000000 : ℝ)*X 1 0+(-1989315609/10000000000 : ℝ)*X 1 1+(-1501642723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((6640552323/10000000000 : ℝ)*X 2 0+(4649686279/10000000000 : ℝ)*X 2 1+(1089044403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((6400063767/10000000000 : ℝ)*X 0 0+(2396218383/5000000000 : ℝ)*X 0 1+(-640958143/5000000000 : ℝ)*X 0 2+(6400063767/10000000000 : ℝ)*X 1 0+(2396218383/5000000000 : ℝ)*X 1 1+(-640958143/5000000000 : ℝ)*X 1 2+(6400063767/10000000000 : ℝ)*X 2 0+(2396218383/5000000000 : ℝ)*X 2 1+(-640958143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-220594859/10000000000 : ℝ)*X 0 0+(5397423923/10000000000 : ℝ)*X 0 1+(-1272266423/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6822818069/10000000000 : ℝ)*X 1 0+(-170914753/1000000000 : ℝ)*X 1 1+(-4008409713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4847715477/10000000000 : ℝ)*X 2 0+(5597890283/10000000000 : ℝ)*X 2 1+(297816883/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((6249135853/10000000000 : ℝ)*X 0 0+(4635971321/10000000000 : ℝ)*X 0 1+(-872925219/5000000000 : ℝ)*X 0 2+(6249135853/10000000000 : ℝ)*X 1 0+(4635971321/10000000000 : ℝ)*X 1 1+(-872925219/5000000000 : ℝ)*X 1 2+(6249135853/10000000000 : ℝ)*X 2 0+(4635971321/10000000000 : ℝ)*X 2 1+(-872925219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((44621/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44621/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (483772275802194465800913981271/31910139864900000000000000000000000 : ℝ) := by norm_num
    linear_combination (2268453/500000000000 : ℝ)*(base23) + (32450626203/100000000000 : ℝ)*(base39) + (4360269/1000000000000 : ℝ)*(base50) + (92323308039/250000000000 : ℝ)*(base60) + (992223440059/250000000000 : ℝ)*(major_s4_0) + (992223440059/250000000000 : ℝ)*(major_s4_1) + (992223440059/250000000000 : ℝ)*(major_s4_2) + (1319269530667/250000000000 : ℝ)*(sp_s4_7) + (2638492197861/500000000000 : ℝ)*(sp_s4_8) + (1319264356249/250000000000 : ℝ)*(sp_s4_9) + (2660651444819/1000000000000 : ℝ)*(sp_s4_13) + (10579899/200000000000 : ℝ)*(sp_s4_14) + (73313221/500000000000 : ℝ)*(sp_s4_15) + (69060261/1000000000000 : ℝ)*(sp_s4_23) + (2660651444819/1000000000000 : ℝ)*(f.failure) + (5277131022163/1000000000000 : ℝ)*(f.sum) + (3725527133273286779/27615871800000000000000000000000 : ℝ)*base62 + (48368310326377/252615000000000000000000000 : ℝ)*base64 + (54209097354121/409950000000000000000000000 : ℝ)*base67 + (1953823859079379/2526150000000000000000000000 : ℝ)*base68 + (2423540974404110773/26270696925000000000000000000000 : ℝ)*base71 + (633999118893589/623970000000000000000000000 : ℝ)*base73 + (363064531043791/1639800000000000000000000000 : ℝ)*base74 + (366647729430209/3119850000000000000000000000 : ℝ)*base76 + (311804627497437907/710545837500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (5023/10000000000000000 : ℝ)*base87 + (5023/10000000000000000 : ℝ)*base89 + (5023/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9303/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9303/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15816022164688312211891918983/1063671328830000000000000000000000 : ℝ) := by norm_num
    linear_combination (65813297883/250000000000 : ℝ)*(base39) + (846077/250000000000 : ℝ)*(base49) + (107696644833/1000000000000 : ℝ)*(base60) + (402421071273/100000000000 : ℝ)*(major_s4_0) + (402421071273/100000000000 : ℝ)*(major_s4_1) + (402421071273/100000000000 : ℝ)*(major_s4_2) + (31086509/500000000000 : ℝ)*(sp_s4_0) + (22524053/250000000000 : ℝ)*(sp_s4_8) + (1337654414547/250000000000 : ℝ)*(sp_s4_14) + (5350591766171/1000000000000 : ℝ)*(sp_s4_15) + (334417616399/62500000000 : ℝ)*(sp_s4_16) + (21074095933/7812500000 : ℝ)*(sp_s4_20) + (1015589/500000000000 : ℝ)*(sp_s4_21) + (250327219/1000000000000 : ℝ)*(sp_s4_27) + (2697734606643/1000000000000 : ℝ)*(f.failure) + (334417616399/62500000000 : ℝ)*(f.sum) + (1037426000321415919/3682116240000000000000000000000 : ℝ)*base62 + (130040379795701/168410000000000000000000000 : ℝ)*base65 + (14447314477493/54660000000000000000000000 : ℝ)*base67 + (50485927324749/168410000000000000000000000 : ℝ)*base69 + (221703887360619529/437844948750000000000000000000 : ℝ)*base71 + (84457059723689/103995000000000000000000000 : ℝ)*base72 + (49125829679473/218640000000000000000000000 : ℝ)*base75 + (56233606859821/207990000000000000000000000 : ℝ)*base77 + (66329370955165169/378957780000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (6369/10000000000000000 : ℝ)*base86 + (6369/10000000000000000 : ℝ)*base88 + (6369/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-15807/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-15807/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17590840070374535610646103/1894788900000000000000000000000 : ℝ) := by norm_num
    linear_combination (174022431353/250000000000 : ℝ)*(base39) + (1487303/500000000000 : ℝ)*(base40) + (595799/500000000000 : ℝ)*(base50) + (3374076952201/1000000000000 : ℝ)*(major_s4_0) + (3374076952201/1000000000000 : ℝ)*(major_s4_1) + (3374076952201/1000000000000 : ℝ)*(major_s4_2) + (3984611/500000000000 : ℝ)*(sp_s4_0) + (282763/12500000000 : ℝ)*(sp_s4_2) + (1886781/62500000000 : ℝ)*(sp_s4_9) + (36908371/250000000000 : ℝ)*(sp_s4_20) + (4486242356429/1000000000000 : ℝ)*(sp_s4_21) + (4486250325651/1000000000000 : ℝ)*(sp_s4_22) + (897239503223/200000000000 : ℝ)*(sp_s4_23) + (2261752850663/1000000000000 : ℝ)*(sp_s4_27) + (2261900484147/1000000000000 : ℝ)*(f.failure) + (4486250325651/1000000000000 : ℝ)*(f.sum) + (19847736805951986859/110463487200000000000000000000000 : ℝ)*base63 + (276494376549641/505230000000000000000000000 : ℝ)*base64 + (1482979418741959/1639800000000000000000000000 : ℝ)*base67 + (3051261131072573/5052300000000000000000000000 : ℝ)*base68 + (2935693164695126861/52541393850000000000000000000000 : ℝ)*base71 + (85368076497943/623970000000000000000000000 : ℝ)*base73 + (1035267080412709/6559200000000000000000000000 : ℝ)*base74 + (676863073546469/3119850000000000000000000000 : ℝ)*base76 + (3573367153824890047/11368733400000000000000000000000 : ℝ)*base79 + (10799/10000000000000000 : ℝ)*base87 + (10799/10000000000000000 : ℝ)*base89 + (10799/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((62397/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62397/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8199/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8199/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50523/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50523/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44621/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44621/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9303/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9303/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-15807/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-15807/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302054_s4 p hpa hpb X hX hprev3

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:59:18.884504+00:00
-- url     : https://prove2.me/submissions/6073955c-7ab4-4800-9c0b-8547161664a7

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
theorem collision_support_c311055_s2_s2_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2415793843/5000000000 : ℝ)*x 0 + (-756302623/10000000000 : ℝ)*x 1 + (161755351/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2415793843/5000000000 : ℝ)^9 ≤ (39249111274217/100000000000000 : ℝ)^7 := by
    have hnat : (2415793843 : ℕ)^9*100000000000000^7 ≤ 39249111274217^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415793843 5000000000 39249111274217 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756302623/10000000000 : ℝ)^9 ≤ (1808393457389/50000000000000 : ℝ)^7 := by
    have hnat : (756302623 : ℕ)^9*50000000000000^7 ≤ 1808393457389^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756302623 10000000000 1808393457389 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161755351/250000000 : ℝ)^9 ≤ (57134101793593/100000000000000 : ℝ)^7 := by
    have hnat : (161755351 : ℕ)^9*100000000000000^7 ≤ 57134101793593^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161755351 250000000 57134101793593 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2415793843/5000000000 : ℝ), (-756302623/10000000000 : ℝ), (161755351/250000000 : ℝ)] ![(39249111274217/100000000000000 : ℝ), (1808393457389/50000000000000 : ℝ), (57134101793593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2415793843/5000000000 : ℝ)|^9 ≤ (39249111274217/100000000000000 : ℝ)^7
        have hw : |(2415793843/5000000000 : ℝ)|=(2415793843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-756302623/10000000000 : ℝ)|^9 ≤ (1808393457389/50000000000000 : ℝ)^7
        have hw : |(-756302623/10000000000 : ℝ)|=(756302623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161755351/250000000 : ℝ)|^9 ≤ (57134101793593/100000000000000 : ℝ)^7
        have hw : |(161755351/250000000 : ℝ)|=(161755351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (784041819/1250000000 : ℝ)*x 0 + (3888480347/10000000000 : ℝ)*x 1 + (145976089/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784041819/1250000000 : ℝ)^9 ≤ (3431088061097/6250000000000 : ℝ)^7 := by
    have hnat : (784041819 : ℕ)^9*6250000000000^7 ≤ 3431088061097^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784041819 1250000000 3431088061097 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3888480347/10000000000 : ℝ)^9 ≤ (29687536971399/100000000000000 : ℝ)^7 := by
    have hnat : (3888480347 : ℕ)^9*100000000000000^7 ≤ 29687536971399^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888480347 10000000000 29687536971399 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145976089/625000000 : ℝ)^9 ≤ (7707527013549/50000000000000 : ℝ)^7 := by
    have hnat : (145976089 : ℕ)^9*50000000000000^7 ≤ 7707527013549^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145976089 625000000 7707527013549 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(784041819/1250000000 : ℝ), (3888480347/10000000000 : ℝ), (145976089/625000000 : ℝ)] ![(3431088061097/6250000000000 : ℝ), (29687536971399/100000000000000 : ℝ), (7707527013549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(784041819/1250000000 : ℝ)|^9 ≤ (3431088061097/6250000000000 : ℝ)^7
        have hw : |(784041819/1250000000 : ℝ)|=(784041819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3888480347/10000000000 : ℝ)|^9 ≤ (29687536971399/100000000000000 : ℝ)^7
        have hw : |(3888480347/10000000000 : ℝ)|=(3888480347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145976089/625000000 : ℝ)|^9 ≤ (7707527013549/50000000000000 : ℝ)^7
        have hw : |(145976089/625000000 : ℝ)|=(145976089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-673165567/5000000000 : ℝ)*x 0 + (4797217469/10000000000 : ℝ)*x 1 + (1537347633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673165567/5000000000 : ℝ)^9 ≤ (303667374327/4000000000000 : ℝ)^7 := by
    have hnat : (673165567 : ℕ)^9*4000000000000^7 ≤ 303667374327^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673165567 5000000000 303667374327 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4797217469/10000000000 : ℝ)^9 ≤ (38890499631977/100000000000000 : ℝ)^7 := by
    have hnat : (4797217469 : ℕ)^9*100000000000000^7 ≤ 38890499631977^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797217469 10000000000 38890499631977 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1537347633/2500000000 : ℝ)^9 ≤ (53517815985181/100000000000000 : ℝ)^7 := by
    have hnat : (1537347633 : ℕ)^9*100000000000000^7 ≤ 53517815985181^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537347633 2500000000 53517815985181 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-673165567/5000000000 : ℝ), (4797217469/10000000000 : ℝ), (1537347633/2500000000 : ℝ)] ![(303667374327/4000000000000 : ℝ), (38890499631977/100000000000000 : ℝ), (53517815985181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-673165567/5000000000 : ℝ)|^9 ≤ (303667374327/4000000000000 : ℝ)^7
        have hw : |(-673165567/5000000000 : ℝ)|=(673165567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4797217469/10000000000 : ℝ)|^9 ≤ (38890499631977/100000000000000 : ℝ)^7
        have hw : |(4797217469/10000000000 : ℝ)|=(4797217469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1537347633/2500000000 : ℝ)|^9 ≤ (53517815985181/100000000000000 : ℝ)^7
        have hw : |(1537347633/2500000000 : ℝ)|=(1537347633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1099597349/2500000000 : ℝ)*x 0 + (-846841/5000000000 : ℝ)*x 1 + (7171372063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099597349/2500000000 : ℝ)^9 ≤ (8695961161691/25000000000000 : ℝ)^7 := by
    have hnat : (1099597349 : ℕ)^9*25000000000000^7 ≤ 8695961161691^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099597349 2500000000 8695961161691 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846841/5000000000 : ℝ)^9 ≤ (141695241/10000000000000 : ℝ)^7 := by
    have hnat : (846841 : ℕ)^9*10000000000000^7 ≤ 141695241^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846841 5000000000 141695241 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7171372063/10000000000 : ℝ)^9 ≤ (13042947678603/20000000000000 : ℝ)^7 := by
    have hnat : (7171372063 : ℕ)^9*20000000000000^7 ≤ 13042947678603^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7171372063 10000000000 13042947678603 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099597349/2500000000 : ℝ), (-846841/5000000000 : ℝ), (7171372063/10000000000 : ℝ)] ![(8695961161691/25000000000000 : ℝ), (141695241/10000000000000 : ℝ), (13042947678603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099597349/2500000000 : ℝ)|^9 ≤ (8695961161691/25000000000000 : ℝ)^7
        have hw : |(1099597349/2500000000 : ℝ)|=(1099597349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-846841/5000000000 : ℝ)|^9 ≤ (141695241/10000000000000 : ℝ)^7
        have hw : |(-846841/5000000000 : ℝ)|=(846841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7171372063/10000000000 : ℝ)|^9 ≤ (13042947678603/20000000000000 : ℝ)^7
        have hw : |(7171372063/10000000000 : ℝ)|=(7171372063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2185429713/5000000000 : ℝ)*x 0 + (6897355761/10000000000 : ℝ)*x 1 + (-731864801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185429713/5000000000 : ℝ)^9 ≤ (8626043798493/25000000000000 : ℝ)^7 := by
    have hnat : (2185429713 : ℕ)^9*25000000000000^7 ≤ 8626043798493^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185429713 5000000000 8626043798493 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6897355761/10000000000 : ℝ)^9 ≤ (12405719145649/20000000000000 : ℝ)^7 := by
    have hnat : (6897355761 : ℕ)^9*20000000000000^7 ≤ 12405719145649^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6897355761 10000000000 12405719145649 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731864801/10000000000 : ℝ)^9 ≤ (1733614532797/50000000000000 : ℝ)^7 := by
    have hnat : (731864801 : ℕ)^9*50000000000000^7 ≤ 1733614532797^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731864801 10000000000 1733614532797 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185429713/5000000000 : ℝ), (6897355761/10000000000 : ℝ), (-731864801/10000000000 : ℝ)] ![(8626043798493/25000000000000 : ℝ), (12405719145649/20000000000000 : ℝ), (1733614532797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185429713/5000000000 : ℝ)|^9 ≤ (8626043798493/25000000000000 : ℝ)^7
        have hw : |(2185429713/5000000000 : ℝ)|=(2185429713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6897355761/10000000000 : ℝ)|^9 ≤ (12405719145649/20000000000000 : ℝ)^7
        have hw : |(6897355761/10000000000 : ℝ)|=(6897355761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-731864801/10000000000 : ℝ)|^9 ≤ (1733614532797/50000000000000 : ℝ)^7
        have hw : |(-731864801/10000000000 : ℝ)|=(731864801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4828865031/10000000000 : ℝ)*x 0 + (6180507329/10000000000 : ℝ)*x 1 + (1251762841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4828865031/10000000000 : ℝ)^9 ≤ (39220677004613/100000000000000 : ℝ)^7 := by
    have hnat : (4828865031 : ℕ)^9*100000000000000^7 ≤ 39220677004613^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828865031 10000000000 39220677004613 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6180507329/10000000000 : ℝ)^9 ≤ (5386624885211/10000000000000 : ℝ)^7 := by
    have hnat : (6180507329 : ℕ)^9*10000000000000^7 ≤ 5386624885211^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6180507329 10000000000 5386624885211 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251762841/10000000000 : ℝ)^9 ≤ (6913074129237/100000000000000 : ℝ)^7 := by
    have hnat : (1251762841 : ℕ)^9*100000000000000^7 ≤ 6913074129237^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251762841 10000000000 6913074129237 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4828865031/10000000000 : ℝ), (6180507329/10000000000 : ℝ), (1251762841/10000000000 : ℝ)] ![(39220677004613/100000000000000 : ℝ), (5386624885211/10000000000000 : ℝ), (6913074129237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4828865031/10000000000 : ℝ)|^9 ≤ (39220677004613/100000000000000 : ℝ)^7
        have hw : |(4828865031/10000000000 : ℝ)|=(4828865031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6180507329/10000000000 : ℝ)|^9 ≤ (5386624885211/10000000000000 : ℝ)^7
        have hw : |(6180507329/10000000000 : ℝ)|=(6180507329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251762841/10000000000 : ℝ)|^9 ≤ (6913074129237/100000000000000 : ℝ)^7
        have hw : |(1251762841/10000000000 : ℝ)|=(1251762841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-61707171/1250000000 : ℝ)*x 0 + (508232493/1000000000 : ℝ)*x 1 + (3186068933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61707171/1250000000 : ℝ)^9 ≤ (417973409943/20000000000000 : ℝ)^7 := by
    have hnat : (61707171 : ℕ)^9*20000000000000^7 ≤ 417973409943^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61707171 1250000000 417973409943 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508232493/1000000000 : ℝ)^9 ≤ (20943548570111/50000000000000 : ℝ)^7 := by
    have hnat : (508232493 : ℕ)^9*50000000000000^7 ≤ 20943548570111^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508232493 1000000000 20943548570111 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186068933/5000000000 : ℝ)^9 ≤ (56023035793721/100000000000000 : ℝ)^7 := by
    have hnat : (3186068933 : ℕ)^9*100000000000000^7 ≤ 56023035793721^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186068933 5000000000 56023035793721 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61707171/1250000000 : ℝ), (508232493/1000000000 : ℝ), (3186068933/5000000000 : ℝ)] ![(417973409943/20000000000000 : ℝ), (20943548570111/50000000000000 : ℝ), (56023035793721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61707171/1250000000 : ℝ)|^9 ≤ (417973409943/20000000000000 : ℝ)^7
        have hw : |(-61707171/1250000000 : ℝ)|=(61707171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508232493/1000000000 : ℝ)|^9 ≤ (20943548570111/50000000000000 : ℝ)^7
        have hw : |(508232493/1000000000 : ℝ)|=(508232493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186068933/5000000000 : ℝ)|^9 ≤ (56023035793721/100000000000000 : ℝ)^7
        have hw : |(3186068933/5000000000 : ℝ)|=(3186068933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2031168001/5000000000 : ℝ)*x 0 + (-8601857/200000000 : ℝ)*x 1 + (1827597979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031168001/5000000000 : ℝ)^9 ≤ (15702453468063/50000000000000 : ℝ)^7 := by
    have hnat : (2031168001 : ℕ)^9*50000000000000^7 ≤ 15702453468063^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031168001 5000000000 15702453468063 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8601857/200000000 : ℝ)^9 ≤ (437614232353/25000000000000 : ℝ)^7 := by
    have hnat : (8601857 : ℕ)^9*25000000000000^7 ≤ 437614232353^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8601857 200000000 437614232353 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1827597979/2500000000 : ℝ)^9 ≤ (66844636115569/100000000000000 : ℝ)^7 := by
    have hnat : (1827597979 : ℕ)^9*100000000000000^7 ≤ 66844636115569^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827597979 2500000000 66844636115569 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2031168001/5000000000 : ℝ), (-8601857/200000000 : ℝ), (1827597979/2500000000 : ℝ)] ![(15702453468063/50000000000000 : ℝ), (437614232353/25000000000000 : ℝ), (66844636115569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2031168001/5000000000 : ℝ)|^9 ≤ (15702453468063/50000000000000 : ℝ)^7
        have hw : |(2031168001/5000000000 : ℝ)|=(2031168001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8601857/200000000 : ℝ)|^9 ≤ (437614232353/25000000000000 : ℝ)^7
        have hw : |(-8601857/200000000 : ℝ)|=(8601857/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1827597979/2500000000 : ℝ)|^9 ≤ (66844636115569/100000000000000 : ℝ)^7
        have hw : |(1827597979/2500000000 : ℝ)|=(1827597979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6296528093/10000000000 : ℝ)*x 0 + (10108387/19531250 : ℝ)*x 1 + (-29273187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6296528093/10000000000 : ℝ)^9 ≤ (11033961602109/20000000000000 : ℝ)^7 := by
    have hnat : (6296528093 : ℕ)^9*20000000000000^7 ≤ 11033961602109^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6296528093 10000000000 11033961602109 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10108387/19531250 : ℝ)^9 ≤ (8575387744263/20000000000000 : ℝ)^7 := by
    have hnat : (10108387 : ℕ)^9*20000000000000^7 ≤ 8575387744263^7*19531250^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10108387 19531250 8575387744263 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29273187/625000000 : ℝ)^9 ≤ (7813013047/400000000000 : ℝ)^7 := by
    have hnat : (29273187 : ℕ)^9*400000000000^7 ≤ 7813013047^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29273187 625000000 7813013047 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6296528093/10000000000 : ℝ), (10108387/19531250 : ℝ), (-29273187/625000000 : ℝ)] ![(11033961602109/20000000000000 : ℝ), (8575387744263/20000000000000 : ℝ), (7813013047/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6296528093/10000000000 : ℝ)|^9 ≤ (11033961602109/20000000000000 : ℝ)^7
        have hw : |(6296528093/10000000000 : ℝ)|=(6296528093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10108387/19531250 : ℝ)|^9 ≤ (8575387744263/20000000000000 : ℝ)^7
        have hw : |(10108387/19531250 : ℝ)|=(10108387/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29273187/625000000 : ℝ)|^9 ≤ (7813013047/400000000000 : ℝ)^7
        have hw : |(-29273187/625000000 : ℝ)|=(29273187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1994019091/2500000000 : ℝ)*x 0 + (294647247/1000000000 : ℝ)*x 1 + (111046979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994019091/2500000000 : ℝ)^9 ≤ (74770296745787/100000000000000 : ℝ)^7 := by
    have hnat : (1994019091 : ℕ)^9*100000000000000^7 ≤ 74770296745787^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994019091 2500000000 74770296745787 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294647247/1000000000 : ℝ)^9 ≤ (20781385487213/100000000000000 : ℝ)^7 := by
    have hnat : (294647247 : ℕ)^9*100000000000000^7 ≤ 20781385487213^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294647247 1000000000 20781385487213 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111046979/1250000000 : ℝ)^9 ≤ (444831775403/10000000000000 : ℝ)^7 := by
    have hnat : (111046979 : ℕ)^9*10000000000000^7 ≤ 444831775403^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111046979 1250000000 444831775403 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1994019091/2500000000 : ℝ), (294647247/1000000000 : ℝ), (111046979/1250000000 : ℝ)] ![(74770296745787/100000000000000 : ℝ), (20781385487213/100000000000000 : ℝ), (444831775403/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1994019091/2500000000 : ℝ)|^9 ≤ (74770296745787/100000000000000 : ℝ)^7
        have hw : |(1994019091/2500000000 : ℝ)|=(1994019091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(294647247/1000000000 : ℝ)|^9 ≤ (20781385487213/100000000000000 : ℝ)^7
        have hw : |(294647247/1000000000 : ℝ)|=(294647247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111046979/1250000000 : ℝ)|^9 ≤ (444831775403/10000000000000 : ℝ)^7
        have hw : |(111046979/1250000000 : ℝ)|=(111046979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-164104261/2500000000 : ℝ)*x 0 + (269983031/400000000 : ℝ)*x 1 + (18327401/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164104261/2500000000 : ℝ)^9 ≤ (3014610687703/100000000000000 : ℝ)^7 := by
    have hnat : (164104261 : ℕ)^9*100000000000000^7 ≤ 3014610687703^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164104261 2500000000 3014610687703 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269983031/400000000 : ℝ)^9 ≤ (60325138551551/100000000000000 : ℝ)^7 := by
    have hnat : (269983031 : ℕ)^9*100000000000000^7 ≤ 60325138551551^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269983031 400000000 60325138551551 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18327401/40000000 : ℝ)^9 ≤ (18330125376191/50000000000000 : ℝ)^7 := by
    have hnat : (18327401 : ℕ)^9*50000000000000^7 ≤ 18330125376191^7*40000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18327401 40000000 18330125376191 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164104261/2500000000 : ℝ), (269983031/400000000 : ℝ), (18327401/40000000 : ℝ)] ![(3014610687703/100000000000000 : ℝ), (60325138551551/100000000000000 : ℝ), (18330125376191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164104261/2500000000 : ℝ)|^9 ≤ (3014610687703/100000000000000 : ℝ)^7
        have hw : |(-164104261/2500000000 : ℝ)|=(164104261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269983031/400000000 : ℝ)|^9 ≤ (60325138551551/100000000000000 : ℝ)^7
        have hw : |(269983031/400000000 : ℝ)|=(269983031/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18327401/40000000 : ℝ)|^9 ≤ (18330125376191/50000000000000 : ℝ)^7
        have hw : |(18327401/40000000 : ℝ)|=(18327401/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3222891947/5000000000 : ℝ)*x 0 + (-3739737/1250000000 : ℝ)*x 1 + (2597567329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3222891947/5000000000 : ℝ)^9 ≤ (56856889327421/100000000000000 : ℝ)^7 := by
    have hnat : (3222891947 : ℕ)^9*100000000000000^7 ≤ 56856889327421^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3222891947 5000000000 56856889327421 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3739737/1250000000 : ℝ)^9 ≤ (56854977303/100000000000000 : ℝ)^7 := by
    have hnat : (3739737 : ℕ)^9*100000000000000^7 ≤ 56854977303^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739737 1250000000 56854977303 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597567329/5000000000 : ℝ)^9 ≤ (21543127844699/50000000000000 : ℝ)^7 := by
    have hnat : (2597567329 : ℕ)^9*50000000000000^7 ≤ 21543127844699^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597567329 5000000000 21543127844699 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3222891947/5000000000 : ℝ), (-3739737/1250000000 : ℝ), (2597567329/5000000000 : ℝ)] ![(56856889327421/100000000000000 : ℝ), (56854977303/100000000000000 : ℝ), (21543127844699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3222891947/5000000000 : ℝ)|^9 ≤ (56856889327421/100000000000000 : ℝ)^7
        have hw : |(3222891947/5000000000 : ℝ)|=(3222891947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3739737/1250000000 : ℝ)|^9 ≤ (56854977303/100000000000000 : ℝ)^7
        have hw : |(-3739737/1250000000 : ℝ)|=(3739737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597567329/5000000000 : ℝ)|^9 ≤ (21543127844699/50000000000000 : ℝ)^7
        have hw : |(2597567329/5000000000 : ℝ)|=(2597567329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1868750429/5000000000 : ℝ)*x 0 + (3557311481/5000000000 : ℝ)*x 1 + (-1296760929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868750429/5000000000 : ℝ)^9 ≤ (28213805803473/100000000000000 : ℝ)^7 := by
    have hnat : (1868750429 : ℕ)^9*100000000000000^7 ≤ 28213805803473^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868750429 5000000000 28213805803473 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3557311481/5000000000 : ℝ)^9 ≤ (64551980675783/100000000000000 : ℝ)^7 := by
    have hnat : (3557311481 : ℕ)^9*100000000000000^7 ≤ 64551980675783^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3557311481 5000000000 64551980675783 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296760929/10000000000 : ℝ)^9 ≤ (7234213499287/100000000000000 : ℝ)^7 := by
    have hnat : (1296760929 : ℕ)^9*100000000000000^7 ≤ 7234213499287^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296760929 10000000000 7234213499287 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1868750429/5000000000 : ℝ), (3557311481/5000000000 : ℝ), (-1296760929/10000000000 : ℝ)] ![(28213805803473/100000000000000 : ℝ), (64551980675783/100000000000000 : ℝ), (7234213499287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1868750429/5000000000 : ℝ)|^9 ≤ (28213805803473/100000000000000 : ℝ)^7
        have hw : |(1868750429/5000000000 : ℝ)|=(1868750429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3557311481/5000000000 : ℝ)|^9 ≤ (64551980675783/100000000000000 : ℝ)^7
        have hw : |(3557311481/5000000000 : ℝ)|=(3557311481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1296760929/10000000000 : ℝ)|^9 ≤ (7234213499287/100000000000000 : ℝ)^7
        have hw : |(-1296760929/10000000000 : ℝ)|=(1296760929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311055_s2_s2_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7813501027/10000000000 : ℝ)*x 0 + (2305245869/10000000000 : ℝ)*x 1 + (481358171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7813501027/10000000000 : ℝ)^9 ≤ (72816558925733/100000000000000 : ℝ)^7 := by
    have hnat : (7813501027 : ℕ)^9*100000000000000^7 ≤ 72816558925733^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7813501027 10000000000 72816558925733 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305245869/10000000000 : ℝ)^9 ≤ (15157810294903/100000000000000 : ℝ)^7 := by
    have hnat : (2305245869 : ℕ)^9*100000000000000^7 ≤ 15157810294903^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305245869 10000000000 15157810294903 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481358171/2500000000 : ℝ)^9 ≤ (12025630768253/100000000000000 : ℝ)^7 := by
    have hnat : (481358171 : ℕ)^9*100000000000000^7 ≤ 12025630768253^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481358171 2500000000 12025630768253 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7813501027/10000000000 : ℝ), (2305245869/10000000000 : ℝ), (481358171/2500000000 : ℝ)] ![(72816558925733/100000000000000 : ℝ), (15157810294903/100000000000000 : ℝ), (12025630768253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7813501027/10000000000 : ℝ)|^9 ≤ (72816558925733/100000000000000 : ℝ)^7
        have hw : |(7813501027/10000000000 : ℝ)|=(7813501027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2305245869/10000000000 : ℝ)|^9 ≤ (15157810294903/100000000000000 : ℝ)^7
        have hw : |(2305245869/10000000000 : ℝ)|=(2305245869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481358171/2500000000 : ℝ)|^9 ≤ (12025630768253/100000000000000 : ℝ)^7
        have hw : |(481358171/2500000000 : ℝ)|=(481358171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311055_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((73347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35427/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35427/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72171/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72171/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11099/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11099/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13847/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13847/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28277/50000 : ℝ)*X 1 2) := by
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
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (73347/100000 : ℝ) ^ (71/16 : ℝ) ≤ (12635842552954246353/50000000000000000000 : ℝ) := by
    have hpowers : (73347/100000 : ℝ)^71 ≤ (12635842552954246353/50000000000000000000 : ℝ)^16 := by
      have hnat : (73347 : ℕ)^71*50000000000000000000^16 ≤ 12635842552954246353^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73347 100000 12635842552954246353 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73347/100000 : ℝ)) (X := (12635842552954246353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (62635842552954246353/50000000000000000000 : ℝ) ≤ (10520862921453839/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (62635842552954246353/50000000000000000000 : ℝ)^16 ≤ (10520862921453839/10000000000000000 : ℝ)^71 := by
      have hnat : (62635842552954246353 : ℕ)^16*10000000000000000^71 ≤ 10520862921453839^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62635842552954246353 50000000000000000000 10520862921453839 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10520862921453839/10000000000000000 : ℝ)) (X := (62635842552954246353/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (37635842552954246353/25000000000000000000 : ℝ) ≤ (10965701625453029/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (37635842552954246353/25000000000000000000 : ℝ)^16 ≤ (10965701625453029/10000000000000000 : ℝ)^71 := by
      have hnat : (37635842552954246353 : ℕ)^16*10000000000000000^71 ≤ 10965701625453029^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37635842552954246353 25000000000000000000 10965701625453029 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10965701625453029/10000000000000000 : ℝ)) (X := (37635842552954246353/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(520862921453839/7334700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14827956799973/244490000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (73347/100000 : ℝ)) (alpha := (520862921453839/7334700000000000 : ℝ)) (beta := (14827956799973/244490000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73347/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(520862921453839/7334700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14827956799973/244490000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (35427/50000 : ℝ) ^ (71/16 : ℝ) ≤ (21676637010837837689/100000000000000000000 : ℝ) := by
    have hpowers : (35427/50000 : ℝ)^71 ≤ (21676637010837837689/100000000000000000000 : ℝ)^16 := by
      have hnat : (35427 : ℕ)^71*100000000000000000000^16 ≤ 21676637010837837689^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35427 50000 21676637010837837689 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35427/50000 : ℝ)) (X := (21676637010837837689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (121676637010837837689/100000000000000000000 : ℝ) ≤ (10452053452029987/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (121676637010837837689/100000000000000000000 : ℝ)^16 ≤ (10452053452029987/10000000000000000 : ℝ)^71 := by
      have hnat : (121676637010837837689 : ℕ)^16*10000000000000000^71 ≤ 10452053452029987^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121676637010837837689 100000000000000000000 10452053452029987 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10452053452029987/10000000000000000 : ℝ)) (X := (121676637010837837689/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (71676637010837837689/50000000000000000000 : ℝ) ≤ (2711357569479271/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (71676637010837837689/50000000000000000000 : ℝ)^16 ≤ (2711357569479271/2500000000000000 : ℝ)^71 := by
      have hnat : (71676637010837837689 : ℕ)^16*2500000000000000^71 ≤ 2711357569479271^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71676637010837837689 50000000000000000000 2711357569479271 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2711357569479271/2500000000000000 : ℝ)) (X := (71676637010837837689/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(452053452029987/7085400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(393376825887097/7085400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (35427/50000 : ℝ)) (alpha := (452053452029987/7085400000000000 : ℝ)) (beta := (393376825887097/7085400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35427/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(452053452029987/7085400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(393376825887097/7085400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (72171/100000 : ℝ) ^ (71/16 : ℝ) ≤ (23522559889409930739/100000000000000000000 : ℝ) := by
    have hpowers : (72171/100000 : ℝ)^71 ≤ (23522559889409930739/100000000000000000000 : ℝ)^16 := by
      have hnat : (72171 : ℕ)^71*100000000000000000000^16 ≤ 23522559889409930739^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72171 100000 23522559889409930739 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72171/100000 : ℝ)) (X := (23522559889409930739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (123522559889409930739/100000000000000000000 : ℝ) ≤ (10487578360872307/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (123522559889409930739/100000000000000000000 : ℝ)^16 ≤ (10487578360872307/10000000000000000 : ℝ)^71 := by
      have hnat : (123522559889409930739 : ℕ)^16*10000000000000000^71 ≤ 10487578360872307^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123522559889409930739 100000000000000000000 10487578360872307 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10487578360872307/10000000000000000 : ℝ)) (X := (123522559889409930739/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (73522559889409930739/50000000000000000000 : ℝ) ≤ (10907754379834337/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (73522559889409930739/50000000000000000000 : ℝ)^16 ≤ (10907754379834337/10000000000000000 : ℝ)^71 := by
      have hnat : (73522559889409930739 : ℕ)^16*10000000000000000^71 ≤ 10907754379834337^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73522559889409930739 50000000000000000000 10907754379834337 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10907754379834337/10000000000000000 : ℝ)) (X := (73522559889409930739/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(162526120290769/2405700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(42017601896203/721710000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (72171/100000 : ℝ)) (alpha := (162526120290769/2405700000000000 : ℝ)) (beta := (42017601896203/721710000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (72171/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(162526120290769/2405700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(42017601896203/721710000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((2415793843/5000000000 : ℝ)*X 1 0+(-756302623/10000000000 : ℝ)*X 1 1+(161755351/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((784041819/1250000000 : ℝ)*X 0 0+(3888480347/10000000000 : ℝ)*X 0 1+(145976089/625000000 : ℝ)*X 0 2+(784041819/1250000000 : ℝ)*X 1 0+(3888480347/10000000000 : ℝ)*X 1 1+(145976089/625000000 : ℝ)*X 1 2+(784041819/1250000000 : ℝ)*X 2 0+(3888480347/10000000000 : ℝ)*X 2 1+(145976089/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-673165567/5000000000 : ℝ)*X 0 0+(4797217469/10000000000 : ℝ)*X 0 1+(1537347633/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1099597349/2500000000 : ℝ)*X 1 0+(-846841/5000000000 : ℝ)*X 1 1+(7171372063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2185429713/5000000000 : ℝ)*X 2 0+(6897355761/10000000000 : ℝ)*X 2 1+(-731864801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4828865031/10000000000 : ℝ)*X 0 0+(6180507329/10000000000 : ℝ)*X 0 1+(1251762841/10000000000 : ℝ)*X 0 2+(4828865031/10000000000 : ℝ)*X 1 0+(6180507329/10000000000 : ℝ)*X 1 1+(1251762841/10000000000 : ℝ)*X 1 2+(4828865031/10000000000 : ℝ)*X 2 0+(6180507329/10000000000 : ℝ)*X 2 1+(1251762841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-61707171/1250000000 : ℝ)*X 0 0+(508232493/1000000000 : ℝ)*X 0 1+(3186068933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2031168001/5000000000 : ℝ)*X 1 0+(-8601857/200000000 : ℝ)*X 1 1+(1827597979/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6296528093/10000000000 : ℝ)*X 2 0+(10108387/19531250 : ℝ)*X 2 1+(-29273187/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1994019091/2500000000 : ℝ)*X 0 0+(294647247/1000000000 : ℝ)*X 0 1+(111046979/1250000000 : ℝ)*X 0 2+(1994019091/2500000000 : ℝ)*X 1 0+(294647247/1000000000 : ℝ)*X 1 1+(111046979/1250000000 : ℝ)*X 1 2+(1994019091/2500000000 : ℝ)*X 2 0+(294647247/1000000000 : ℝ)*X 2 1+(111046979/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-164104261/2500000000 : ℝ)*X 0 0+(269983031/400000000 : ℝ)*X 0 1+(18327401/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3222891947/5000000000 : ℝ)*X 1 0+(-3739737/1250000000 : ℝ)*X 1 1+(2597567329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1868750429/5000000000 : ℝ)*X 2 0+(3557311481/5000000000 : ℝ)*X 2 1+(-1296760929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7813501027/10000000000 : ℝ)*X 0 0+(2305245869/10000000000 : ℝ)*X 0 1+(481358171/2500000000 : ℝ)*X 0 2+(7813501027/10000000000 : ℝ)*X 1 0+(2305245869/10000000000 : ℝ)*X 1 1+(481358171/2500000000 : ℝ)*X 1 2+(7813501027/10000000000 : ℝ)*X 2 0+(2305245869/10000000000 : ℝ)*X 2 1+(481358171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((11099/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11099/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (208821106411069446124607541/14435912050000000000000000000000 : ℝ) := by norm_num
    linear_combination (161234056533/1000000000000 : ℝ)*(base7) + (85223737031/1000000000000 : ℝ)*(base49) + (324429/250000000000 : ℝ)*(base60) + (228192456669/62500000000 : ℝ)*(major_s2_0) + (228192456669/62500000000 : ℝ)*(major_s2_1) + (228192456669/62500000000 : ℝ)*(major_s2_2) + (3924407/1000000000000 : ℝ)*(sp_s2_6) + (1245993226841/250000000000 : ℝ)*(sp_s2_7) + (4984043323451/1000000000000 : ℝ)*(sp_s2_8) + (4984023618403/1000000000000 : ℝ)*(sp_s2_9) + (1191391986593/500000000000 : ℝ)*(sp_s2_13) + (12851449/250000000000 : ℝ)*(sp_s2_14) + (19010291/1000000000000 : ℝ)*(sp_s2_21) + (2463131/125000000000 : ℝ)*(sp_s2_23) + (2221553841059/1000000000000 : ℝ)*(f.failure) + (4984043323451/1000000000000 : ℝ)*(f.sum) + (6562690555041377/473481855000000000000000000000 : ℝ)*base62 + (1325888896687/30071250000000000000000000 : ℝ)*base65 + (98332686087179/147612500000000000000000000 : ℝ)*base67 + (104347800134213/200475000000000000000000000 : ℝ)*base69 + (16978802203109823853/29408479650000000000000000000000 : ℝ)*base70 + (133428972266249/244490000000000000000000000 : ℝ)*base73 + (11999779104783/73806250000000000000000000 : ℝ)*base75 + (238315541302343/611225000000000000000000000 : ℝ)*base77 + (1281122770296075569/14435912050000000000000000000000 : ℝ)*base79 + (8867/25000000000000000 : ℝ)*base86 + (8867/25000000000000000 : ℝ)*base88 + (8867/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13847/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13847/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (701291522320632000910111/45093510000000000000000000000 : ℝ) := by norm_num
    linear_combination (49237239231/500000000000 : ℝ)*(base7) + (2550558279/62500000000 : ℝ)*(base49) + (80499980379/25000000000 : ℝ)*(major_s2_0) + (80499980379/25000000000 : ℝ)*(major_s2_1) + (80499980379/25000000000 : ℝ)*(major_s2_2) + (413623/12500000000 : ℝ)*(sp_s2_1) + (901373/500000000000 : ℝ)*(sp_s2_7) + (162869803/1000000000000 : ℝ)*(sp_s2_8) + (2210879504397/500000000000 : ℝ)*(sp_s2_14) + (884313630419/200000000000 : ℝ)*(sp_s2_15) + (2210882055869/500000000000 : ℝ)*(sp_s2_16) + (2057676021039/1000000000000 : ℝ)*(sp_s2_20) + (1650099/500000000000 : ℝ)*(sp_s2_21) + (27582923/500000000000 : ℝ)*(sp_s2_27) + (1959256708423/1000000000000 : ℝ)*(f.failure) + (2210882055869/500000000000 : ℝ)*(f.sum) + (586914426389/16910066250000000000000000 : ℝ)*base63 + (6170928565939/15035625000000000000000000 : ℝ)*base65 + (3100270966069/8435000000000000000000000 : ℝ)*base67 + (8746366086901/20047500000000000000000000 : ℝ)*base69 + (1024214838190993/367605995625000000000000000000 : ℝ)*base70 + (124561566763551/244490000000000000000000000 : ℝ)*base73 + (3794358738481/8435000000000000000000000 : ℝ)*base75 + (25713753602221/61122500000000000000000000 : ℝ)*base77 + (13976960860891771/206227315000000000000000000000 : ℝ)*base78 + (24199/25000000000000000 : ℝ)*base86 + (24199/25000000000000000 : ℝ)*base88 + (24199/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28277/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41673444172002694314337837/2673498150000000000000000000000 : ℝ) := by norm_num
    linear_combination (346742187213/1000000000000 : ℝ)*(base7) + (100003102779/1000000000000 : ℝ)*(base40) + (720659/1000000000000 : ℝ)*(base59) + (1415471814317/500000000000 : ℝ)*(major_s2_0) + (1415471814317/500000000000 : ℝ)*(major_s2_1) + (1415471814317/500000000000 : ℝ)*(major_s2_2) + (3218563/1000000000000 : ℝ)*(sp_s2_1) + (43589/5000000000 : ℝ)*(sp_s2_8) + (36878183/250000000000 : ℝ)*(sp_s2_9) + (111017/3906250000 : ℝ)*(sp_s2_20) + (3731702020413/1000000000000 : ℝ)*(sp_s2_21) + (74633801681/20000000000 : ℝ)*(sp_s2_22) + (3731554507681/1000000000000 : ℝ)*(sp_s2_23) + (2069243781607/1000000000000 : ℝ)*(sp_s2_27) + (861265007373/500000000000 : ℝ)*(f.failure) + (3731702020413/1000000000000 : ℝ)*(f.sum) + (40988829443594083/516525660000000000000000000000 : ℝ)*base63 + (15713340346249/16402500000000000000000000 : ℝ)*base64 + (1674919219987289/3542700000000000000000000000 : ℝ)*base66 + (26110303034191/54675000000000000000000000 : ℝ)*base68 + (3454609580862930259/8020494450000000000000000000000 : ℝ)*base70 + (65240322083323/122245000000000000000000000 : ℝ)*base72 + (1528480490728811/3542700000000000000000000000 : ℝ)*base74 + (594718404398833/916837500000000000000000000 : ℝ)*base76 + (10787678953814517509/86615472300000000000000000000000 : ℝ)*base79 + (9451/12500000000000000 : ℝ)*base87 + (9451/12500000000000000 : ℝ)*base89 + (9451/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((73347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35427/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35427/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72171/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72171/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11099/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11099/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13847/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13847/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28277/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28277/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311055_s2 p hpa hpb X hX hprev1

#print axioms solution

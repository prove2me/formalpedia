-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307060_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:14:59.019098+00:00
-- url     : https://prove2.me/submissions/145068da-61e8-4790-8cef-35f34e43339d

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
theorem collision_support_c307060_s3_s3_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1103444481/5000000000 : ℝ)*x 0 + (4153405057/10000000000 : ℝ)*x 1 + (-6281532437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103444481/5000000000 : ℝ)^17 ≤ (866456575989/6250000000000 : ℝ)^13 := by
    have hnat : (1103444481 : ℕ)^17*6250000000000^13 ≤ 866456575989^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103444481 5000000000 866456575989 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153405057/10000000000 : ℝ)^17 ≤ (31694961014157/100000000000000 : ℝ)^13 := by
    have hnat : (4153405057 : ℕ)^17*100000000000000^13 ≤ 31694961014157^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153405057 10000000000 31694961014157 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6281532437/10000000000 : ℝ)^17 ≤ (54441733751463/100000000000000 : ℝ)^13 := by
    have hnat : (6281532437 : ℕ)^17*100000000000000^13 ≤ 54441733751463^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6281532437 10000000000 54441733751463 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1103444481/5000000000 : ℝ), (4153405057/10000000000 : ℝ), (-6281532437/10000000000 : ℝ)] ![(866456575989/6250000000000 : ℝ), (31694961014157/100000000000000 : ℝ), (54441733751463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1103444481/5000000000 : ℝ)|^17 ≤ (866456575989/6250000000000 : ℝ)^13
        have hw : |(-1103444481/5000000000 : ℝ)|=(1103444481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153405057/10000000000 : ℝ)|^17 ≤ (31694961014157/100000000000000 : ℝ)^13
        have hw : |(4153405057/10000000000 : ℝ)|=(4153405057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6281532437/10000000000 : ℝ)|^17 ≤ (54441733751463/100000000000000 : ℝ)^13
        have hw : |(-6281532437/10000000000 : ℝ)|=(6281532437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4468749659/10000000000 : ℝ)*x 0 + (-1276085693/5000000000 : ℝ)*x 1 + (-2868600349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468749659/10000000000 : ℝ)^17 ≤ (6975590101751/20000000000000 : ℝ)^13 := by
    have hnat : (4468749659 : ℕ)^17*20000000000000^13 ≤ 6975590101751^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468749659 10000000000 6975590101751 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276085693/5000000000 : ℝ)^17 ≤ (16765656105669/100000000000000 : ℝ)^13 := by
    have hnat : (1276085693 : ℕ)^17*100000000000000^13 ≤ 16765656105669^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276085693 5000000000 16765656105669 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2868600349/5000000000 : ℝ)^17 ≤ (48356393371079/100000000000000 : ℝ)^13 := by
    have hnat : (2868600349 : ℕ)^17*100000000000000^13 ≤ 48356393371079^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868600349 5000000000 48356393371079 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468749659/10000000000 : ℝ), (-1276085693/5000000000 : ℝ), (-2868600349/5000000000 : ℝ)] ![(6975590101751/20000000000000 : ℝ), (16765656105669/100000000000000 : ℝ), (48356393371079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468749659/10000000000 : ℝ)|^17 ≤ (6975590101751/20000000000000 : ℝ)^13
        have hw : |(4468749659/10000000000 : ℝ)|=(4468749659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1276085693/5000000000 : ℝ)|^17 ≤ (16765656105669/100000000000000 : ℝ)^13
        have hw : |(-1276085693/5000000000 : ℝ)|=(1276085693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2868600349/5000000000 : ℝ)|^17 ≤ (48356393371079/100000000000000 : ℝ)^13
        have hw : |(-2868600349/5000000000 : ℝ)|=(2868600349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4730925777/10000000000 : ℝ)*x 0 + (2919742487/5000000000 : ℝ)*x 1 + (1046515327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4730925777/10000000000 : ℝ)^17 ≤ (587150704779/1562500000000 : ℝ)^13 := by
    have hnat : (4730925777 : ℕ)^17*1562500000000^13 ≤ 587150704779^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730925777 10000000000 587150704779 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2919742487/5000000000 : ℝ)^17 ≤ (49486847667603/100000000000000 : ℝ)^13 := by
    have hnat : (2919742487 : ℕ)^17*100000000000000^13 ≤ 49486847667603^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919742487 5000000000 49486847667603 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046515327/5000000000 : ℝ)^17 ≤ (6467753606633/50000000000000 : ℝ)^13 := by
    have hnat : (1046515327 : ℕ)^17*50000000000000^13 ≤ 6467753606633^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046515327 5000000000 6467753606633 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4730925777/10000000000 : ℝ), (2919742487/5000000000 : ℝ), (1046515327/5000000000 : ℝ)] ![(587150704779/1562500000000 : ℝ), (49486847667603/100000000000000 : ℝ), (6467753606633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4730925777/10000000000 : ℝ)|^17 ≤ (587150704779/1562500000000 : ℝ)^13
        have hw : |(4730925777/10000000000 : ℝ)|=(4730925777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2919742487/5000000000 : ℝ)|^17 ≤ (49486847667603/100000000000000 : ℝ)^13
        have hw : |(2919742487/5000000000 : ℝ)|=(2919742487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046515327/5000000000 : ℝ)|^17 ≤ (6467753606633/50000000000000 : ℝ)^13
        have hw : |(1046515327/5000000000 : ℝ)|=(1046515327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6816162629/10000000000 : ℝ)*x 0 + (1098353631/2500000000 : ℝ)*x 1 + (-21188701/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6816162629/10000000000 : ℝ)^17 ≤ (30289455715453/50000000000000 : ℝ)^13 := by
    have hnat : (6816162629 : ℕ)^17*50000000000000^13 ≤ 30289455715453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6816162629 10000000000 30289455715453 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098353631/2500000000 : ℝ)^17 ≤ (6822211136073/20000000000000 : ℝ)^13 := by
    have hnat : (1098353631 : ℕ)^17*20000000000000^13 ≤ 6822211136073^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098353631 2500000000 6822211136073 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21188701/200000000 : ℝ)^17 ≤ (5310032874119/100000000000000 : ℝ)^13 := by
    have hnat : (21188701 : ℕ)^17*100000000000000^13 ≤ 5310032874119^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21188701 200000000 5310032874119 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6816162629/10000000000 : ℝ), (1098353631/2500000000 : ℝ), (-21188701/200000000 : ℝ)] ![(30289455715453/50000000000000 : ℝ), (6822211136073/20000000000000 : ℝ), (5310032874119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6816162629/10000000000 : ℝ)|^17 ≤ (30289455715453/50000000000000 : ℝ)^13
        have hw : |(6816162629/10000000000 : ℝ)|=(6816162629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098353631/2500000000 : ℝ)|^17 ≤ (6822211136073/20000000000000 : ℝ)^13
        have hw : |(1098353631/2500000000 : ℝ)|=(1098353631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21188701/200000000 : ℝ)|^17 ≤ (5310032874119/100000000000000 : ℝ)^13
        have hw : |(-21188701/200000000 : ℝ)|=(21188701/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004052533/5000000000 : ℝ)*x 0 + (76354361/200000000 : ℝ)*x 1 + (-3355472293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004052533/5000000000 : ℝ)^17 ≤ (12253472487797/100000000000000 : ℝ)^13 := by
    have hnat : (1004052533 : ℕ)^17*100000000000000^13 ≤ 12253472487797^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004052533 5000000000 12253472487797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76354361/200000000 : ℝ)^17 ≤ (28387563141617/100000000000000 : ℝ)^13 := by
    have hnat : (76354361 : ℕ)^17*100000000000000^13 ≤ 28387563141617^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76354361 200000000 28387563141617 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3355472293/5000000000 : ℝ)^17 ≤ (29679482177483/50000000000000 : ℝ)^13 := by
    have hnat : (3355472293 : ℕ)^17*50000000000000^13 ≤ 29679482177483^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355472293 5000000000 29679482177483 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004052533/5000000000 : ℝ), (76354361/200000000 : ℝ), (-3355472293/5000000000 : ℝ)] ![(12253472487797/100000000000000 : ℝ), (28387563141617/100000000000000 : ℝ), (29679482177483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004052533/5000000000 : ℝ)|^17 ≤ (12253472487797/100000000000000 : ℝ)^13
        have hw : |(-1004052533/5000000000 : ℝ)|=(1004052533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76354361/200000000 : ℝ)|^17 ≤ (28387563141617/100000000000000 : ℝ)^13
        have hw : |(76354361/200000000 : ℝ)|=(76354361/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3355472293/5000000000 : ℝ)|^17 ≤ (29679482177483/50000000000000 : ℝ)^13
        have hw : |(-3355472293/5000000000 : ℝ)|=(3355472293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4098214033/10000000000 : ℝ)*x 0 + (-324261061/2000000000 : ℝ)*x 1 + (-6731063577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4098214033/10000000000 : ℝ)^17 ≤ (7786333375901/25000000000000 : ℝ)^13 := by
    have hnat : (4098214033 : ℕ)^17*25000000000000^13 ≤ 7786333375901^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098214033 10000000000 7786333375901 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324261061/2000000000 : ℝ)^17 ≤ (9262885203777/100000000000000 : ℝ)^13 := by
    have hnat : (324261061 : ℕ)^17*100000000000000^13 ≤ 9262885203777^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324261061 2000000000 9262885203777 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6731063577/10000000000 : ℝ)^17 ≤ (29795890640043/50000000000000 : ℝ)^13 := by
    have hnat : (6731063577 : ℕ)^17*50000000000000^13 ≤ 29795890640043^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6731063577 10000000000 29795890640043 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4098214033/10000000000 : ℝ), (-324261061/2000000000 : ℝ), (-6731063577/10000000000 : ℝ)] ![(7786333375901/25000000000000 : ℝ), (9262885203777/100000000000000 : ℝ), (29795890640043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4098214033/10000000000 : ℝ)|^17 ≤ (7786333375901/25000000000000 : ℝ)^13
        have hw : |(4098214033/10000000000 : ℝ)|=(4098214033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-324261061/2000000000 : ℝ)|^17 ≤ (9262885203777/100000000000000 : ℝ)^13
        have hw : |(-324261061/2000000000 : ℝ)|=(324261061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6731063577/10000000000 : ℝ)|^17 ≤ (29795890640043/50000000000000 : ℝ)^13
        have hw : |(-6731063577/10000000000 : ℝ)|=(6731063577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1090690287/2500000000 : ℝ)*x 0 + (3389790719/5000000000 : ℝ)*x 1 + (1169947787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090690287/2500000000 : ℝ)^17 ≤ (33800163582553/100000000000000 : ℝ)^13 := by
    have hnat : (1090690287 : ℕ)^17*100000000000000^13 ≤ 33800163582553^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090690287 2500000000 33800163582553 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3389790719/5000000000 : ℝ)^17 ≤ (15038527552721/25000000000000 : ℝ)^13 := by
    have hnat : (3389790719 : ℕ)^17*25000000000000^13 ≤ 15038527552721^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389790719 5000000000 15038527552721 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169947787/10000000000 : ℝ)^17 ≤ (755715773829/12500000000000 : ℝ)^13 := by
    have hnat : (1169947787 : ℕ)^17*12500000000000^13 ≤ 755715773829^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169947787 10000000000 755715773829 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090690287/2500000000 : ℝ), (3389790719/5000000000 : ℝ), (1169947787/10000000000 : ℝ)] ![(33800163582553/100000000000000 : ℝ), (15038527552721/25000000000000 : ℝ), (755715773829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090690287/2500000000 : ℝ)|^17 ≤ (33800163582553/100000000000000 : ℝ)^13
        have hw : |(1090690287/2500000000 : ℝ)|=(1090690287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3389790719/5000000000 : ℝ)|^17 ≤ (15038527552721/25000000000000 : ℝ)^13
        have hw : |(3389790719/5000000000 : ℝ)|=(3389790719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1169947787/10000000000 : ℝ)|^17 ≤ (755715773829/12500000000000 : ℝ)^13
        have hw : |(1169947787/10000000000 : ℝ)|=(1169947787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3177431509/5000000000 : ℝ)*x 0 + (1330262869/2500000000 : ℝ)*x 1 + (-273569577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3177431509/5000000000 : ℝ)^17 ≤ (13818582400097/25000000000000 : ℝ)^13 := by
    have hnat : (3177431509 : ℕ)^17*25000000000000^13 ≤ 13818582400097^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177431509 5000000000 13818582400097 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1330262869/2500000000 : ℝ)^17 ≤ (5477709538389/12500000000000 : ℝ)^13 := by
    have hnat : (1330262869 : ℕ)^17*12500000000000^13 ≤ 5477709538389^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330262869 2500000000 5477709538389 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273569577/10000000000 : ℝ)^17 ≤ (180798814659/20000000000000 : ℝ)^13 := by
    have hnat : (273569577 : ℕ)^17*20000000000000^13 ≤ 180798814659^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273569577 10000000000 180798814659 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3177431509/5000000000 : ℝ), (1330262869/2500000000 : ℝ), (-273569577/10000000000 : ℝ)] ![(13818582400097/25000000000000 : ℝ), (5477709538389/12500000000000 : ℝ), (180798814659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3177431509/5000000000 : ℝ)|^17 ≤ (13818582400097/25000000000000 : ℝ)^13
        have hw : |(3177431509/5000000000 : ℝ)|=(3177431509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1330262869/2500000000 : ℝ)|^17 ≤ (5477709538389/12500000000000 : ℝ)^13
        have hw : |(1330262869/2500000000 : ℝ)|=(1330262869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273569577/10000000000 : ℝ)|^17 ≤ (180798814659/20000000000000 : ℝ)^13
        have hw : |(-273569577/10000000000 : ℝ)|=(273569577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-657914449/5000000000 : ℝ)*x 0 + (4359710937/10000000000 : ℝ)*x 1 + (-6695537691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657914449/5000000000 : ℝ)^17 ≤ (1762478653501/25000000000000 : ℝ)^13 := by
    have hnat : (657914449 : ℕ)^17*25000000000000^13 ≤ 1762478653501^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657914449 5000000000 1762478653501 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4359710937/10000000000 : ℝ)^17 ≤ (33769264463763/100000000000000 : ℝ)^13 := by
    have hnat : (4359710937 : ℕ)^17*100000000000000^13 ≤ 33769264463763^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359710937 10000000000 33769264463763 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6695537691/10000000000 : ℝ)^17 ≤ (29590410453487/50000000000000 : ℝ)^13 := by
    have hnat : (6695537691 : ℕ)^17*50000000000000^13 ≤ 29590410453487^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6695537691 10000000000 29590410453487 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-657914449/5000000000 : ℝ), (4359710937/10000000000 : ℝ), (-6695537691/10000000000 : ℝ)] ![(1762478653501/25000000000000 : ℝ), (33769264463763/100000000000000 : ℝ), (29590410453487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-657914449/5000000000 : ℝ)|^17 ≤ (1762478653501/25000000000000 : ℝ)^13
        have hw : |(-657914449/5000000000 : ℝ)|=(657914449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4359710937/10000000000 : ℝ)|^17 ≤ (33769264463763/100000000000000 : ℝ)^13
        have hw : |(4359710937/10000000000 : ℝ)|=(4359710937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6695537691/10000000000 : ℝ)|^17 ≤ (29590410453487/50000000000000 : ℝ)^13
        have hw : |(-6695537691/10000000000 : ℝ)|=(6695537691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4054841587/10000000000 : ℝ)*x 0 + (-851079449/5000000000 : ℝ)*x 1 + (-1678914029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4054841587/10000000000 : ℝ)^17 ≤ (30714996784521/100000000000000 : ℝ)^13 := by
    have hnat : (4054841587 : ℕ)^17*100000000000000^13 ≤ 30714996784521^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054841587 10000000000 30714996784521 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (851079449/5000000000 : ℝ)^17 ≤ (9871536266193/100000000000000 : ℝ)^13 := by
    have hnat : (851079449 : ℕ)^17*100000000000000^13 ≤ 9871536266193^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851079449 5000000000 9871536266193 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678914029/2500000000 : ℝ)^17 ≤ (59413466938643/100000000000000 : ℝ)^13 := by
    have hnat : (1678914029 : ℕ)^17*100000000000000^13 ≤ 59413466938643^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678914029 2500000000 59413466938643 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4054841587/10000000000 : ℝ), (-851079449/5000000000 : ℝ), (-1678914029/2500000000 : ℝ)] ![(30714996784521/100000000000000 : ℝ), (9871536266193/100000000000000 : ℝ), (59413466938643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4054841587/10000000000 : ℝ)|^17 ≤ (30714996784521/100000000000000 : ℝ)^13
        have hw : |(4054841587/10000000000 : ℝ)|=(4054841587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-851079449/5000000000 : ℝ)|^17 ≤ (9871536266193/100000000000000 : ℝ)^13
        have hw : |(-851079449/5000000000 : ℝ)|=(851079449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1678914029/2500000000 : ℝ)|^17 ≤ (59413466938643/100000000000000 : ℝ)^13
        have hw : |(-1678914029/2500000000 : ℝ)|=(1678914029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (355293689/625000000 : ℝ)*x 0 + (110574273/200000000 : ℝ)*x 1 + (237071013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355293689/625000000 : ℝ)^17 ≤ (4777853764091/10000000000000 : ℝ)^13 := by
    have hnat : (355293689 : ℕ)^17*10000000000000^13 ≤ 4777853764091^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355293689 625000000 4777853764091 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110574273/200000000 : ℝ)^17 ≤ (11517852700817/25000000000000 : ℝ)^13 := by
    have hnat : (110574273 : ℕ)^17*25000000000000^13 ≤ 11517852700817^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110574273 200000000 11517852700817 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237071013/2000000000 : ℝ)^17 ≤ (3075025768089/50000000000000 : ℝ)^13 := by
    have hnat : (237071013 : ℕ)^17*50000000000000^13 ≤ 3075025768089^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237071013 2000000000 3075025768089 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(355293689/625000000 : ℝ), (110574273/200000000 : ℝ), (237071013/2000000000 : ℝ)] ![(4777853764091/10000000000000 : ℝ), (11517852700817/25000000000000 : ℝ), (3075025768089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(355293689/625000000 : ℝ)|^17 ≤ (4777853764091/10000000000000 : ℝ)^13
        have hw : |(355293689/625000000 : ℝ)|=(355293689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110574273/200000000 : ℝ)|^17 ≤ (11517852700817/25000000000000 : ℝ)^13
        have hw : |(110574273/200000000 : ℝ)|=(110574273/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237071013/2000000000 : ℝ)|^17 ≤ (3075025768089/50000000000000 : ℝ)^13
        have hw : |(237071013/2000000000 : ℝ)|=(237071013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (777426813/1000000000 : ℝ)*x 0 + (229672111/625000000 : ℝ)*x 1 + (-153030893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777426813/1000000000 : ℝ)^17 ≤ (17986899068663/25000000000000 : ℝ)^13 := by
    have hnat : (777426813 : ℕ)^17*25000000000000^13 ≤ 17986899068663^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777426813 1000000000 17986899068663 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229672111/625000000 : ℝ)^17 ≤ (27005506070409/100000000000000 : ℝ)^13 := by
    have hnat : (229672111 : ℕ)^17*100000000000000^13 ≤ 27005506070409^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229672111 625000000 27005506070409 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153030893/5000000000 : ℝ)^17 ≤ (523448817167/50000000000000 : ℝ)^13 := by
    have hnat : (153030893 : ℕ)^17*50000000000000^13 ≤ 523448817167^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153030893 5000000000 523448817167 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777426813/1000000000 : ℝ), (229672111/625000000 : ℝ), (-153030893/5000000000 : ℝ)] ![(17986899068663/25000000000000 : ℝ), (27005506070409/100000000000000 : ℝ), (523448817167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777426813/1000000000 : ℝ)|^17 ≤ (17986899068663/25000000000000 : ℝ)^13
        have hw : |(777426813/1000000000 : ℝ)|=(777426813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229672111/625000000 : ℝ)|^17 ≤ (27005506070409/100000000000000 : ℝ)^13
        have hw : |(229672111/625000000 : ℝ)|=(229672111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153030893/5000000000 : ℝ)|^17 ≤ (523448817167/50000000000000 : ℝ)^13
        have hw : |(-153030893/5000000000 : ℝ)|=(153030893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051834243/10000000000 : ℝ)*x 0 + (5223398891/10000000000 : ℝ)*x 1 + (-6061967879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051834243/10000000000 : ℝ)^17 ≤ (5260269739239/100000000000000 : ℝ)^13 := by
    have hnat : (1051834243 : ℕ)^17*100000000000000^13 ≤ 5260269739239^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051834243 10000000000 5260269739239 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223398891/10000000000 : ℝ)^17 ≤ (42772984999859/100000000000000 : ℝ)^13 := by
    have hnat : (5223398891 : ℕ)^17*100000000000000^13 ≤ 42772984999859^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223398891 10000000000 42772984999859 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6061967879/10000000000 : ℝ)^17 ≤ (12991686312763/25000000000000 : ℝ)^13 := by
    have hnat : (6061967879 : ℕ)^17*25000000000000^13 ≤ 12991686312763^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6061967879 10000000000 12991686312763 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051834243/10000000000 : ℝ), (5223398891/10000000000 : ℝ), (-6061967879/10000000000 : ℝ)] ![(5260269739239/100000000000000 : ℝ), (42772984999859/100000000000000 : ℝ), (12991686312763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051834243/10000000000 : ℝ)|^17 ≤ (5260269739239/100000000000000 : ℝ)^13
        have hw : |(-1051834243/10000000000 : ℝ)|=(1051834243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223398891/10000000000 : ℝ)|^17 ≤ (42772984999859/100000000000000 : ℝ)^13
        have hw : |(5223398891/10000000000 : ℝ)|=(5223398891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6061967879/10000000000 : ℝ)|^17 ≤ (12991686312763/25000000000000 : ℝ)^13
        have hw : |(-6061967879/10000000000 : ℝ)|=(6061967879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2842073633/5000000000 : ℝ)*x 0 + (-771396063/5000000000 : ℝ)*x 1 + (-2647754757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2842073633/5000000000 : ℝ)^17 ≤ (23886236723361/50000000000000 : ℝ)^13 := by
    have hnat : (2842073633 : ℕ)^17*50000000000000^13 ≤ 23886236723361^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842073633 5000000000 23886236723361 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771396063/5000000000 : ℝ)^17 ≤ (4340361004843/50000000000000 : ℝ)^13 := by
    have hnat : (771396063 : ℕ)^17*50000000000000^13 ≤ 4340361004843^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771396063 5000000000 4340361004843 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2647754757/5000000000 : ℝ)^17 ≤ (4354680452779/10000000000000 : ℝ)^13 := by
    have hnat : (2647754757 : ℕ)^17*10000000000000^13 ≤ 4354680452779^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647754757 5000000000 4354680452779 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2842073633/5000000000 : ℝ), (-771396063/5000000000 : ℝ), (-2647754757/5000000000 : ℝ)] ![(23886236723361/50000000000000 : ℝ), (4340361004843/50000000000000 : ℝ), (4354680452779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2842073633/5000000000 : ℝ)|^17 ≤ (23886236723361/50000000000000 : ℝ)^13
        have hw : |(2842073633/5000000000 : ℝ)|=(2842073633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-771396063/5000000000 : ℝ)|^17 ≤ (4340361004843/50000000000000 : ℝ)^13
        have hw : |(-771396063/5000000000 : ℝ)|=(771396063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2647754757/5000000000 : ℝ)|^17 ≤ (4354680452779/10000000000000 : ℝ)^13
        have hw : |(-2647754757/5000000000 : ℝ)|=(2647754757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2109078693/5000000000 : ℝ)*x 0 + (637449273/1000000000 : ℝ)*x 1 + (499083063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109078693/5000000000 : ℝ)^17 ≤ (32342675465013/100000000000000 : ℝ)^13 := by
    have hnat : (2109078693 : ℕ)^17*100000000000000^13 ≤ 32342675465013^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109078693 5000000000 32342675465013 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (637449273/1000000000 : ℝ)^17 ≤ (277488544633/500000000000 : ℝ)^13 := by
    have hnat : (637449273 : ℕ)^17*500000000000^13 ≤ 277488544633^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637449273 1000000000 277488544633 500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499083063/2500000000 : ℝ)^17 ≤ (12159615593097/100000000000000 : ℝ)^13 := by
    have hnat : (499083063 : ℕ)^17*100000000000000^13 ≤ 12159615593097^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499083063 2500000000 12159615593097 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109078693/5000000000 : ℝ), (637449273/1000000000 : ℝ), (499083063/2500000000 : ℝ)] ![(32342675465013/100000000000000 : ℝ), (277488544633/500000000000 : ℝ), (12159615593097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109078693/5000000000 : ℝ)|^17 ≤ (32342675465013/100000000000000 : ℝ)^13
        have hw : |(2109078693/5000000000 : ℝ)|=(2109078693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(637449273/1000000000 : ℝ)|^17 ≤ (277488544633/500000000000 : ℝ)^13
        have hw : |(637449273/1000000000 : ℝ)|=(637449273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499083063/2500000000 : ℝ)|^17 ≤ (12159615593097/100000000000000 : ℝ)^13
        have hw : |(499083063/2500000000 : ℝ)|=(499083063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s3_s3_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (319510311/400000000 : ℝ)*x 0 + (1688213583/5000000000 : ℝ)*x 1 + (-35752357/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319510311/400000000 : ℝ)^17 ≤ (37271062982793/50000000000000 : ℝ)^13 := by
    have hnat : (319510311 : ℕ)^17*50000000000000^13 ≤ 37271062982793^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319510311 400000000 37271062982793 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688213583/5000000000 : ℝ)^17 ≤ (24175048315759/100000000000000 : ℝ)^13 := by
    have hnat : (1688213583 : ℕ)^17*100000000000000^13 ≤ 24175048315759^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688213583 5000000000 24175048315759 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35752357/1000000000 : ℝ)^17 ≤ (1282825712493/100000000000000 : ℝ)^13 := by
    have hnat : (35752357 : ℕ)^17*100000000000000^13 ≤ 1282825712493^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35752357 1000000000 1282825712493 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(319510311/400000000 : ℝ), (1688213583/5000000000 : ℝ), (-35752357/1000000000 : ℝ)] ![(37271062982793/50000000000000 : ℝ), (24175048315759/100000000000000 : ℝ), (1282825712493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(319510311/400000000 : ℝ)|^17 ≤ (37271062982793/50000000000000 : ℝ)^13
        have hw : |(319510311/400000000 : ℝ)|=(319510311/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1688213583/5000000000 : ℝ)|^17 ≤ (24175048315759/100000000000000 : ℝ)^13
        have hw : |(1688213583/5000000000 : ℝ)|=(1688213583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35752357/1000000000 : ℝ)|^17 ≤ (1282825712493/100000000000000 : ℝ)^13
        have hw : |(-35752357/1000000000 : ℝ)|=(35752357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307060_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((74127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75413/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75413/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31367/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31367/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9489/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9489/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12897/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17601/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17601/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (74127/100000 : ℝ) ^ (135/32 : ℝ) ≤ (28278934319103859793/100000000000000000000 : ℝ) := by
    have hpowers : (74127/100000 : ℝ)^135 ≤ (28278934319103859793/100000000000000000000 : ℝ)^32 := by
      have hnat : (74127 : ℕ)^135*100000000000000000000^32 ≤ 28278934319103859793^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74127 100000 28278934319103859793 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74127/100000 : ℝ)) (X := (28278934319103859793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (128278934319103859793/100000000000000000000 : ℝ) ≤ (2121616175176147/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (128278934319103859793/100000000000000000000 : ℝ)^32 ≤ (2121616175176147/2000000000000000 : ℝ)^135 := by
      have hnat : (128278934319103859793 : ℕ)^32*2000000000000000^135 ≤ 2121616175176147^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128278934319103859793 100000000000000000000 2121616175176147 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2121616175176147/2000000000000000 : ℝ)) (X := (128278934319103859793/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (78278934319103859793/50000000000000000000 : ℝ) ≤ (5560516910819271/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (78278934319103859793/50000000000000000000 : ℝ)^32 ≤ (5560516910819271/5000000000000000 : ℝ)^135 := by
      have hnat : (78278934319103859793 : ℕ)^32*5000000000000000^135 ≤ 5560516910819271^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78278934319103859793 50000000000000000000 5560516910819271 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5560516910819271/5000000000000000 : ℝ)) (X := (78278934319103859793/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(121616175176147/1482540000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(512952945757807/7412700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (74127/100000 : ℝ)) (alpha := (121616175176147/1482540000000000 : ℝ)) (beta := (512952945757807/7412700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (74127/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(121616175176147/1482540000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(512952945757807/7412700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (75413/100000 : ℝ) ^ (135/32 : ℝ) ≤ (7601796509508762867/25000000000000000000 : ℝ) := by
    have hpowers : (75413/100000 : ℝ)^135 ≤ (7601796509508762867/25000000000000000000 : ℝ)^32 := by
      have hnat : (75413 : ℕ)^135*25000000000000000000^32 ≤ 7601796509508762867^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75413 100000 7601796509508762867 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75413/100000 : ℝ)) (X := (7601796509508762867/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (32601796509508762867/25000000000000000000 : ℝ) ≤ (10649537117014551/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (32601796509508762867/25000000000000000000 : ℝ)^32 ≤ (10649537117014551/10000000000000000 : ℝ)^135 := by
      have hnat : (32601796509508762867 : ℕ)^32*10000000000000000^135 ≤ 10649537117014551^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32601796509508762867 25000000000000000000 10649537117014551 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10649537117014551/10000000000000000 : ℝ)) (X := (32601796509508762867/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (20101796509508762867/12500000000000000000 : ℝ) ≤ (11191972472788851/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (20101796509508762867/12500000000000000000 : ℝ)^32 ≤ (11191972472788851/10000000000000000 : ℝ)^135 := by
      have hnat : (20101796509508762867 : ℕ)^32*10000000000000000^135 ≤ 11191972472788851^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20101796509508762867 12500000000000000000 11191972472788851 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11191972472788851/10000000000000000 : ℝ)) (X := (20101796509508762867/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(649537117014551/7541300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5424353557743/75413000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (75413/100000 : ℝ)) (alpha := (649537117014551/7541300000000000 : ℝ)) (beta := (5424353557743/75413000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75413/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(649537117014551/7541300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5424353557743/75413000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (31367/50000 : ℝ) ^ (135/32 : ℝ) ≤ (6993357010026290751/50000000000000000000 : ℝ) := by
    have hpowers : (31367/50000 : ℝ)^135 ≤ (6993357010026290751/50000000000000000000 : ℝ)^32 := by
      have hnat : (31367 : ℕ)^135*50000000000000000000^32 ≤ 6993357010026290751^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31367 50000 6993357010026290751 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31367/50000 : ℝ)) (X := (6993357010026290751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (56993357010026290751/50000000000000000000 : ℝ) ≤ (10315174023567573/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (56993357010026290751/50000000000000000000 : ℝ)^32 ≤ (10315174023567573/10000000000000000 : ℝ)^135 := by
      have hnat : (56993357010026290751 : ℕ)^32*10000000000000000^135 ≤ 10315174023567573^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56993357010026290751 50000000000000000000 10315174023567573 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10315174023567573/10000000000000000 : ℝ)) (X := (56993357010026290751/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (31993357010026290751/25000000000000000000 : ℝ) ≤ (5301043465317647/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (31993357010026290751/25000000000000000000 : ℝ)^32 ≤ (5301043465317647/5000000000000000 : ℝ)^135 := by
      have hnat : (31993357010026290751 : ℕ)^32*5000000000000000^135 ≤ 5301043465317647^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31993357010026290751 25000000000000000000 5301043465317647 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5301043465317647/5000000000000000 : ℝ)) (X := (31993357010026290751/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(315174023567573/6273400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(286912907067721/6273400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (31367/50000 : ℝ)) (alpha := (315174023567573/6273400000000000 : ℝ)) (beta := (286912907067721/6273400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31367/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(315174023567573/6273400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(286912907067721/6273400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1103444481/5000000000 : ℝ)*X 0 0+(4153405057/10000000000 : ℝ)*X 0 1+(-6281532437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4468749659/10000000000 : ℝ)*X 1 0+(-1276085693/5000000000 : ℝ)*X 1 1+(-2868600349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((4730925777/10000000000 : ℝ)*X 2 0+(2919742487/5000000000 : ℝ)*X 2 1+(1046515327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((6816162629/10000000000 : ℝ)*X 0 0+(1098353631/2500000000 : ℝ)*X 0 1+(-21188701/200000000 : ℝ)*X 0 2+(6816162629/10000000000 : ℝ)*X 1 0+(1098353631/2500000000 : ℝ)*X 1 1+(-21188701/200000000 : ℝ)*X 1 2+(6816162629/10000000000 : ℝ)*X 2 0+(1098353631/2500000000 : ℝ)*X 2 1+(-21188701/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1004052533/5000000000 : ℝ)*X 0 0+(76354361/200000000 : ℝ)*X 0 1+(-3355472293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4098214033/10000000000 : ℝ)*X 1 0+(-324261061/2000000000 : ℝ)*X 1 1+(-6731063577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1090690287/2500000000 : ℝ)*X 2 0+(3389790719/5000000000 : ℝ)*X 2 1+(1169947787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((3177431509/5000000000 : ℝ)*X 0 0+(1330262869/2500000000 : ℝ)*X 0 1+(-273569577/10000000000 : ℝ)*X 0 2+(3177431509/5000000000 : ℝ)*X 1 0+(1330262869/2500000000 : ℝ)*X 1 1+(-273569577/10000000000 : ℝ)*X 1 2+(3177431509/5000000000 : ℝ)*X 2 0+(1330262869/2500000000 : ℝ)*X 2 1+(-273569577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-657914449/5000000000 : ℝ)*X 0 0+(4359710937/10000000000 : ℝ)*X 0 1+(-6695537691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4054841587/10000000000 : ℝ)*X 1 0+(-851079449/5000000000 : ℝ)*X 1 1+(-1678914029/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((355293689/625000000 : ℝ)*X 2 0+(110574273/200000000 : ℝ)*X 2 1+(237071013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((777426813/1000000000 : ℝ)*X 0 0+(229672111/625000000 : ℝ)*X 0 1+(-153030893/5000000000 : ℝ)*X 0 2+(777426813/1000000000 : ℝ)*X 1 0+(229672111/625000000 : ℝ)*X 1 1+(-153030893/5000000000 : ℝ)*X 1 2+(777426813/1000000000 : ℝ)*X 2 0+(229672111/625000000 : ℝ)*X 2 1+(-153030893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1051834243/10000000000 : ℝ)*X 0 0+(5223398891/10000000000 : ℝ)*X 0 1+(-6061967879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((2842073633/5000000000 : ℝ)*X 1 0+(-771396063/5000000000 : ℝ)*X 1 1+(-2647754757/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2109078693/5000000000 : ℝ)*X 2 0+(637449273/1000000000 : ℝ)*X 2 1+(499083063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((319510311/400000000 : ℝ)*X 0 0+(1688213583/5000000000 : ℝ)*X 0 1+(-35752357/1000000000 : ℝ)*X 0 2+(319510311/400000000 : ℝ)*X 1 0+(1688213583/5000000000 : ℝ)*X 1 1+(-35752357/1000000000 : ℝ)*X 1 2+(319510311/400000000 : ℝ)*X 2 0+(1688213583/5000000000 : ℝ)*X 2 1+(-35752357/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((9489/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9489/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (138219167237418279/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (60373/62500000000 : ℝ)*(base5) + (9911007/1000000000000 : ℝ)*(base39) + (833711/250000000000 : ℝ)*(base49) + (522131487597/1000000000000 : ℝ)*(base59) + (5553867441821/1000000000000 : ℝ)*(major_s3_0) + (5553867441821/1000000000000 : ℝ)*(major_s3_1) + (5553867441821/1000000000000 : ℝ)*(major_s3_2) + (12003891/200000000000 : ℝ)*(sp_s3_1) + (3767458287701/500000000000 : ℝ)*(sp_s3_7) + (7534043074543/1000000000000 : ℝ)*(sp_s3_8) + (7534750626579/1000000000000 : ℝ)*(sp_s3_9) + (1786406367481/500000000000 : ℝ)*(sp_s3_13) + (203370351/250000000000 : ℝ)*(sp_s3_15) + (16691479/100000000000 : ℝ)*(sp_s3_23) + (357281370093/100000000000 : ℝ)*(f.failure) + (3767458287701/500000000000 : ℝ)*(f.sum) + (65199819044307562863/473095914200000000000000000000000 : ℝ)*base63 + (2530297477488021/6273400000000000000000000000 : ℝ)*base64 + (52179701407207/188532500000000000000000000 : ℝ)*base67 + (2990360251103087/6273400000000000000000000000 : ℝ)*base68 + (99750029558339497283/465028321800000000000000000000000 : ℝ)*base71 + (3270006329562077/7412700000000000000000000000 : ℝ)*base73 + (1555662646357869/7541300000000000000000000000 : ℝ)*base74 + (225200652416669/1482540000000000000000000000 : ℝ)*base76 + (251891448777873245279/559013945100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (833/1250000000000000 : ℝ)*base87 + (833/1250000000000000 : ℝ)*base89 + (833/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12897/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26268855794163149130081745887129/1461215867995975000000000000000000000 : ℝ) := by norm_num
    linear_combination (1661209/1000000000000 : ℝ)*(base5) + (166455644127/1000000000000 : ℝ)*(base59) + (5398674207609/1000000000000 : ℝ)*(major_s3_0) + (5398674207609/1000000000000 : ℝ)*(major_s3_1) + (5398674207609/1000000000000 : ℝ)*(major_s3_2) + (82443/250000000000 : ℝ)*(sp_s3_1) + (9750391/200000000000 : ℝ)*(sp_s3_2) + (4213901/125000000000 : ℝ)*(sp_s3_6) + (14157319/125000000000 : ℝ)*(sp_s3_7) + (7324251571937/1000000000000 : ℝ)*(sp_s3_14) + (7324364500717/1000000000000 : ℝ)*(sp_s3_15) + (228884929367/31250000000 : ℝ)*(sp_s3_16) + (868154466199/250000000000 : ℝ)*(sp_s3_20) + (324355041/1000000000000 : ℝ)*(sp_s3_27) + (694595518451/200000000000 : ℝ)*(f.failure) + (7324364830489/1000000000000 : ℝ)*(f.sum) + (325528418686998801367/473095914200000000000000000000000 : ℝ)*base63 + (3595455058408491/6273400000000000000000000000 : ℝ)*base65 + (71730318932477/150826000000000000000000000 : ℝ)*base66 + (6800986907302197/6273400000000000000000000000 : ℝ)*base69 + (20573510069833634209/155009440600000000000000000000000 : ℝ)*base71 + (1123485414083319/2470900000000000000000000000 : ℝ)*base72 + (5230232006659419/7541300000000000000000000000 : ℝ)*base75 + (165632901350489/494180000000000000000000000 : ℝ)*base77 + (19965499663867244307/186337981700000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1119/2500000000000000 : ℝ)*base86 + (1119/2500000000000000 : ℝ)*base88 + (1119/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17601/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17601/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1183004972065084256208446271/118273978550000000000000000000000 : ℝ) := by norm_num
    linear_combination (12947/1250000000 : ℝ)*(base11) + (11941/500000000000 : ℝ)*(base15) + (454522792841/1000000000000 : ℝ)*(base39) + (60484978127/500000000000 : ℝ)*(base59) + (4259288887639/1000000000000 : ℝ)*(major_s3_0) + (4259288887639/1000000000000 : ℝ)*(major_s3_1) + (4259288887639/1000000000000 : ℝ)*(major_s3_2) + (30241599/1000000000000 : ℝ)*(sp_s3_0) + (3668229/250000000000 : ℝ)*(sp_s3_2) + (2451407/40000000000 : ℝ)*(sp_s3_9) + (5778525036711/1000000000000 : ℝ)*(sp_s3_21) + (1444641403007/250000000000 : ℝ)*(sp_s3_22) + (5778489677819/1000000000000 : ℝ)*(sp_s3_23) + (548001761057/200000000000 : ℝ)*(sp_s3_27) + (548001761057/200000000000 : ℝ)*(f.failure) + (577856563591/100000000000 : ℝ)*(f.sum) + (61219788066745837843/473095914200000000000000000000000 : ℝ)*base62 + (1243010329216921/6273400000000000000000000000 : ℝ)*base65 + (39117067584117/94266250000000000000000000 : ℝ)*base67 + (1839844230740673/6273400000000000000000000000 : ℝ)*base68 + (50283521679146412037/465028321800000000000000000000000 : ℝ)*base71 + (659140618467013/7412700000000000000000000000 : ℝ)*base73 + (2325732016102241/7541300000000000000000000000 : ℝ)*base74 + (349422396524623/1482540000000000000000000000 : ℝ)*base76 + (46764686616737626921/559013945100000000000000000000000 : ℝ)*base78 + (1067/2500000000000000 : ℝ)*base87 + (1067/2500000000000000 : ℝ)*base89 + (1067/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((74127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75413/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75413/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31367/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31367/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9489/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9489/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12897/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17601/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17601/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307060_s3 p hpa hpb X hX hprev2

#print axioms solution

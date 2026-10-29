-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c327061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:17:26.35898+00:00
-- url     : https://prove2.me/submissions/733f0d7f-3471-4924-a96c-f37ac7203fae

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
theorem collision_support_c327061_s1_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1760188093/10000000000 : ℝ)*x 0 + (547829607/1250000000 : ℝ)*x 1 + (5749789387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760188093/10000000000 : ℝ)^91 ≤ (12150990527757/100000000000000 : ℝ)^75 := by
    have hnat : (1760188093 : ℕ)^91*100000000000000^75 ≤ 12150990527757^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760188093 10000000000 12150990527757 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547829607/1250000000 : ℝ)^91 ≤ (7350818834837/20000000000000 : ℝ)^75 := by
    have hnat : (547829607 : ℕ)^91*20000000000000^75 ≤ 7350818834837^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547829607 1250000000 7350818834837 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5749789387/10000000000 : ℝ)^91 ≤ (1596716102723/3125000000000 : ℝ)^75 := by
    have hnat : (5749789387 : ℕ)^91*3125000000000^75 ≤ 1596716102723^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5749789387 10000000000 1596716102723 3125000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1760188093/10000000000 : ℝ), (547829607/1250000000 : ℝ), (5749789387/10000000000 : ℝ)] ![(12150990527757/100000000000000 : ℝ), (7350818834837/20000000000000 : ℝ), (1596716102723/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1760188093/10000000000 : ℝ)|^91 ≤ (12150990527757/100000000000000 : ℝ)^75
        have hw : |(-1760188093/10000000000 : ℝ)|=(1760188093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547829607/1250000000 : ℝ)|^91 ≤ (7350818834837/20000000000000 : ℝ)^75
        have hw : |(547829607/1250000000 : ℝ)|=(547829607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5749789387/10000000000 : ℝ)|^91 ≤ (1596716102723/3125000000000 : ℝ)^75
        have hw : |(5749789387/10000000000 : ℝ)|=(5749789387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4611181887/10000000000 : ℝ)*x 0 + (-1760915133/10000000000 : ℝ)*x 1 + (5531464483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4611181887/10000000000 : ℝ)^91 ≤ (19546193998669/50000000000000 : ℝ)^75 := by
    have hnat : (4611181887 : ℕ)^91*50000000000000^75 ≤ 19546193998669^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4611181887 10000000000 19546193998669 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760915133/10000000000 : ℝ)^91 ≤ (12157080427873/100000000000000 : ℝ)^75 := by
    have hnat : (1760915133 : ℕ)^91*100000000000000^75 ≤ 12157080427873^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760915133 10000000000 12157080427873 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5531464483/10000000000 : ℝ)^91 ≤ (48750531565657/100000000000000 : ℝ)^75 := by
    have hnat : (5531464483 : ℕ)^91*100000000000000^75 ≤ 48750531565657^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531464483 10000000000 48750531565657 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4611181887/10000000000 : ℝ), (-1760915133/10000000000 : ℝ), (5531464483/10000000000 : ℝ)] ![(19546193998669/50000000000000 : ℝ), (12157080427873/100000000000000 : ℝ), (48750531565657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4611181887/10000000000 : ℝ)|^91 ≤ (19546193998669/50000000000000 : ℝ)^75
        have hw : |(4611181887/10000000000 : ℝ)|=(4611181887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760915133/10000000000 : ℝ)|^91 ≤ (12157080427873/100000000000000 : ℝ)^75
        have hw : |(-1760915133/10000000000 : ℝ)|=(1760915133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5531464483/10000000000 : ℝ)|^91 ≤ (48750531565657/100000000000000 : ℝ)^75
        have hw : |(5531464483/10000000000 : ℝ)|=(5531464483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4655025833/10000000000 : ℝ)*x 0 + (6149948189/10000000000 : ℝ)*x 1 + (-169761643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4655025833/10000000000 : ℝ)^91 ≤ (39543837167241/100000000000000 : ℝ)^75 := by
    have hnat : (4655025833 : ℕ)^91*100000000000000^75 ≤ 39543837167241^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655025833 10000000000 39543837167241 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6149948189/10000000000 : ℝ)^91 ≤ (55440954816943/100000000000000 : ℝ)^75 := by
    have hnat : (6149948189 : ℕ)^91*100000000000000^75 ≤ 55440954816943^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6149948189 10000000000 55440954816943 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169761643/2000000000 : ℝ)^91 ≤ (1003041600821/20000000000000 : ℝ)^75 := by
    have hnat : (169761643 : ℕ)^91*20000000000000^75 ≤ 1003041600821^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169761643 2000000000 1003041600821 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4655025833/10000000000 : ℝ), (6149948189/10000000000 : ℝ), (-169761643/2000000000 : ℝ)] ![(39543837167241/100000000000000 : ℝ), (55440954816943/100000000000000 : ℝ), (1003041600821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4655025833/10000000000 : ℝ)|^91 ≤ (39543837167241/100000000000000 : ℝ)^75
        have hw : |(4655025833/10000000000 : ℝ)|=(4655025833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6149948189/10000000000 : ℝ)|^91 ≤ (55440954816943/100000000000000 : ℝ)^75
        have hw : |(6149948189/10000000000 : ℝ)|=(6149948189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169761643/2000000000 : ℝ)|^91 ≤ (1003041600821/20000000000000 : ℝ)^75
        have hw : |(-169761643/2000000000 : ℝ)|=(169761643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6523947417/10000000000 : ℝ)*x 0 + (482038033/2000000000 : ℝ)*x 1 + (735200991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6523947417/10000000000 : ℝ)^91 ≤ (59557896184739/100000000000000 : ℝ)^75 := by
    have hnat : (6523947417 : ℕ)^91*100000000000000^75 ≤ 59557896184739^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6523947417 10000000000 59557896184739 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482038033/2000000000 : ℝ)^91 ≤ (3558379402861/20000000000000 : ℝ)^75 := by
    have hnat : (482038033 : ℕ)^91*20000000000000^75 ≤ 3558379402861^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482038033 2000000000 3558379402861 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735200991/2500000000 : ℝ)^91 ≤ (2831275847281/12500000000000 : ℝ)^75 := by
    have hnat : (735200991 : ℕ)^91*12500000000000^75 ≤ 2831275847281^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735200991 2500000000 2831275847281 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6523947417/10000000000 : ℝ), (482038033/2000000000 : ℝ), (735200991/2500000000 : ℝ)] ![(59557896184739/100000000000000 : ℝ), (3558379402861/20000000000000 : ℝ), (2831275847281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6523947417/10000000000 : ℝ)|^91 ≤ (59557896184739/100000000000000 : ℝ)^75
        have hw : |(6523947417/10000000000 : ℝ)|=(6523947417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482038033/2000000000 : ℝ)|^91 ≤ (3558379402861/20000000000000 : ℝ)^75
        have hw : |(482038033/2000000000 : ℝ)|=(482038033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(735200991/2500000000 : ℝ)|^91 ≤ (2831275847281/12500000000000 : ℝ)^75
        have hw : |(735200991/2500000000 : ℝ)|=(735200991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-179669257/1000000000 : ℝ)*x 0 + (1993674553/5000000000 : ℝ)*x 1 + (1217727183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179669257/1000000000 : ℝ)^91 ≤ (12457421997227/100000000000000 : ℝ)^75 := by
    have hnat : (179669257 : ℕ)^91*100000000000000^75 ≤ 12457421997227^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179669257 1000000000 12457421997227 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993674553/5000000000 : ℝ)^91 ≤ (819288600873/2500000000000 : ℝ)^75 := by
    have hnat : (1993674553 : ℕ)^91*2500000000000^75 ≤ 819288600873^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993674553 5000000000 819288600873 2500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217727183/2000000000 : ℝ)^91 ≤ (10954206791747/20000000000000 : ℝ)^75 := by
    have hnat : (1217727183 : ℕ)^91*20000000000000^75 ≤ 10954206791747^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217727183 2000000000 10954206791747 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179669257/1000000000 : ℝ), (1993674553/5000000000 : ℝ), (1217727183/2000000000 : ℝ)] ![(12457421997227/100000000000000 : ℝ), (819288600873/2500000000000 : ℝ), (10954206791747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179669257/1000000000 : ℝ)|^91 ≤ (12457421997227/100000000000000 : ℝ)^75
        have hw : |(-179669257/1000000000 : ℝ)|=(179669257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1993674553/5000000000 : ℝ)|^91 ≤ (819288600873/2500000000000 : ℝ)^75
        have hw : |(1993674553/5000000000 : ℝ)|=(1993674553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1217727183/2000000000 : ℝ)|^91 ≤ (10954206791747/20000000000000 : ℝ)^75
        have hw : |(1217727183/2000000000 : ℝ)|=(1217727183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54154113/125000000 : ℝ)*x 0 + (-17081953/125000000 : ℝ)*x 1 + (6093069713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54154113/125000000 : ℝ)^91 ≤ (1449712880967/4000000000000 : ℝ)^75 := by
    have hnat : (54154113 : ℕ)^91*4000000000000^75 ≤ 1449712880967^75*125000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54154113 125000000 1449712880967 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17081953/125000000 : ℝ)^91 ≤ (8937746753113/100000000000000 : ℝ)^75 := by
    have hnat : (17081953 : ℕ)^91*100000000000000^75 ≤ 8937746753113^75*125000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17081953 125000000 8937746753113 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6093069713/10000000000 : ℝ)^91 ≤ (10963886241919/20000000000000 : ℝ)^75 := by
    have hnat : (6093069713 : ℕ)^91*20000000000000^75 ≤ 10963886241919^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6093069713 10000000000 10963886241919 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54154113/125000000 : ℝ), (-17081953/125000000 : ℝ), (6093069713/10000000000 : ℝ)] ![(1449712880967/4000000000000 : ℝ), (8937746753113/100000000000000 : ℝ), (10963886241919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54154113/125000000 : ℝ)|^91 ≤ (1449712880967/4000000000000 : ℝ)^75
        have hw : |(54154113/125000000 : ℝ)|=(54154113/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17081953/125000000 : ℝ)|^91 ≤ (8937746753113/100000000000000 : ℝ)^75
        have hw : |(-17081953/125000000 : ℝ)|=(17081953/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6093069713/10000000000 : ℝ)|^91 ≤ (10963886241919/20000000000000 : ℝ)^75
        have hw : |(6093069713/10000000000 : ℝ)|=(6093069713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4376370543/10000000000 : ℝ)*x 0 + (1345138347/2000000000 : ℝ)*x 1 + (-315579203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376370543/10000000000 : ℝ)^91 ≤ (18345170913069/50000000000000 : ℝ)^75 := by
    have hnat : (4376370543 : ℕ)^91*50000000000000^75 ≤ 18345170913069^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376370543 10000000000 18345170913069 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345138347/2000000000 : ℝ)^91 ≤ (30899931266201/50000000000000 : ℝ)^75 := by
    have hnat : (1345138347 : ℕ)^91*50000000000000^75 ≤ 30899931266201^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345138347 2000000000 30899931266201 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315579203/10000000000 : ℝ)^91 ≤ (377448905491/25000000000000 : ℝ)^75 := by
    have hnat : (315579203 : ℕ)^91*25000000000000^75 ≤ 377448905491^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315579203 10000000000 377448905491 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376370543/10000000000 : ℝ), (1345138347/2000000000 : ℝ), (-315579203/10000000000 : ℝ)] ![(18345170913069/50000000000000 : ℝ), (30899931266201/50000000000000 : ℝ), (377448905491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376370543/10000000000 : ℝ)|^91 ≤ (18345170913069/50000000000000 : ℝ)^75
        have hw : |(4376370543/10000000000 : ℝ)|=(4376370543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1345138347/2000000000 : ℝ)|^91 ≤ (30899931266201/50000000000000 : ℝ)^75
        have hw : |(1345138347/2000000000 : ℝ)|=(1345138347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315579203/10000000000 : ℝ)|^91 ≤ (377448905491/25000000000000 : ℝ)^75
        have hw : |(-315579203/10000000000 : ℝ)|=(315579203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (330831339/500000000 : ℝ)*x 0 + (1639138127/5000000000 : ℝ)*x 1 + (964118331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330831339/500000000 : ℝ)^91 ≤ (60586024276281/100000000000000 : ℝ)^75 := by
    have hnat : (330831339 : ℕ)^91*100000000000000^75 ≤ 60586024276281^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330831339 500000000 60586024276281 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1639138127/5000000000 : ℝ)^91 ≤ (25841433296511/100000000000000 : ℝ)^75 := by
    have hnat : (1639138127 : ℕ)^91*100000000000000^75 ≤ 25841433296511^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639138127 5000000000 25841433296511 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964118331/5000000000 : ℝ)^91 ≤ (13572542417651/100000000000000 : ℝ)^75 := by
    have hnat : (964118331 : ℕ)^91*100000000000000^75 ≤ 13572542417651^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964118331 5000000000 13572542417651 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330831339/500000000 : ℝ), (1639138127/5000000000 : ℝ), (964118331/5000000000 : ℝ)] ![(60586024276281/100000000000000 : ℝ), (25841433296511/100000000000000 : ℝ), (13572542417651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330831339/500000000 : ℝ)|^91 ≤ (60586024276281/100000000000000 : ℝ)^75
        have hw : |(330831339/500000000 : ℝ)|=(330831339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1639138127/5000000000 : ℝ)|^91 ≤ (25841433296511/100000000000000 : ℝ)^75
        have hw : |(1639138127/5000000000 : ℝ)|=(1639138127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(964118331/5000000000 : ℝ)|^91 ≤ (13572542417651/100000000000000 : ℝ)^75
        have hw : |(964118331/5000000000 : ℝ)|=(964118331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1011979989/10000000000 : ℝ)*x 0 + (921418171/2000000000 : ℝ)*x 1 + (3042980037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011979989/10000000000 : ℝ)^91 ≤ (6207860304473/100000000000000 : ℝ)^75 := by
    have hnat : (1011979989 : ℕ)^91*100000000000000^75 ≤ 6207860304473^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011979989 10000000000 6207860304473 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921418171/2000000000 : ℝ)^91 ≤ (781006206239/2000000000000 : ℝ)^75 := by
    have hnat : (921418171 : ℕ)^91*2000000000000^75 ≤ 781006206239^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921418171 2000000000 781006206239 2000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3042980037/5000000000 : ℝ)^91 ≤ (13685457344001/25000000000000 : ℝ)^75 := by
    have hnat : (3042980037 : ℕ)^91*25000000000000^75 ≤ 13685457344001^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3042980037 5000000000 13685457344001 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1011979989/10000000000 : ℝ), (921418171/2000000000 : ℝ), (3042980037/5000000000 : ℝ)] ![(6207860304473/100000000000000 : ℝ), (781006206239/2000000000000 : ℝ), (13685457344001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1011979989/10000000000 : ℝ)|^91 ≤ (6207860304473/100000000000000 : ℝ)^75
        have hw : |(-1011979989/10000000000 : ℝ)|=(1011979989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921418171/2000000000 : ℝ)|^91 ≤ (781006206239/2000000000000 : ℝ)^75
        have hw : |(921418171/2000000000 : ℝ)|=(921418171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3042980037/5000000000 : ℝ)|^91 ≤ (13685457344001/25000000000000 : ℝ)^75
        have hw : |(3042980037/5000000000 : ℝ)|=(3042980037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4286094063/10000000000 : ℝ)*x 0 + (-357252811/2500000000 : ℝ)*x 1 + (60903909/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286094063/10000000000 : ℝ)^91 ≤ (35774056900487/100000000000000 : ℝ)^75 := by
    have hnat : (4286094063 : ℕ)^91*100000000000000^75 ≤ 35774056900487^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286094063 10000000000 35774056900487 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357252811/2500000000 : ℝ)^91 ≤ (9435753434271/100000000000000 : ℝ)^75 := by
    have hnat : (357252811 : ℕ)^91*100000000000000^75 ≤ 9435753434271^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357252811 2500000000 9435753434271 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60903909/100000000 : ℝ)^91 ≤ (5479018964977/10000000000000 : ℝ)^75 := by
    have hnat : (60903909 : ℕ)^91*10000000000000^75 ≤ 5479018964977^75*100000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60903909 100000000 5479018964977 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286094063/10000000000 : ℝ), (-357252811/2500000000 : ℝ), (60903909/100000000 : ℝ)] ![(35774056900487/100000000000000 : ℝ), (9435753434271/100000000000000 : ℝ), (5479018964977/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286094063/10000000000 : ℝ)|^91 ≤ (35774056900487/100000000000000 : ℝ)^75
        have hw : |(4286094063/10000000000 : ℝ)|=(4286094063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-357252811/2500000000 : ℝ)|^91 ≤ (9435753434271/100000000000000 : ℝ)^75
        have hw : |(-357252811/2500000000 : ℝ)|=(357252811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60903909/100000000 : ℝ)|^91 ≤ (5479018964977/10000000000000 : ℝ)^75
        have hw : |(60903909/100000000 : ℝ)|=(60903909/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5431766613/10000000000 : ℝ)*x 0 + (28606633/50000000 : ℝ)*x 1 + (-15912729/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5431766613/10000000000 : ℝ)^91 ≤ (47686473079103/100000000000000 : ℝ)^75 := by
    have hnat : (5431766613 : ℕ)^91*100000000000000^75 ≤ 47686473079103^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431766613 10000000000 47686473079103 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28606633/50000000 : ℝ)^91 ≤ (6348523393397/12500000000000 : ℝ)^75 := by
    have hnat : (28606633 : ℕ)^91*12500000000000^75 ≤ 6348523393397^75*50000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28606633 50000000 6348523393397 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15912729/500000000 : ℝ)^91 ≤ (305067951571/20000000000000 : ℝ)^75 := by
    have hnat : (15912729 : ℕ)^91*20000000000000^75 ≤ 305067951571^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15912729 500000000 305067951571 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5431766613/10000000000 : ℝ), (28606633/50000000 : ℝ), (-15912729/500000000 : ℝ)] ![(47686473079103/100000000000000 : ℝ), (6348523393397/12500000000000 : ℝ), (305067951571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5431766613/10000000000 : ℝ)|^91 ≤ (47686473079103/100000000000000 : ℝ)^75
        have hw : |(5431766613/10000000000 : ℝ)|=(5431766613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28606633/50000000 : ℝ)|^91 ≤ (6348523393397/12500000000000 : ℝ)^75
        have hw : |(28606633/50000000 : ℝ)|=(28606633/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15912729/500000000 : ℝ)|^91 ≤ (305067951571/20000000000000 : ℝ)^75
        have hw : |(-15912729/500000000 : ℝ)|=(15912729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (764100149/1000000000 : ℝ)*x 0 + (1001049003/5000000000 : ℝ)*x 1 + (968441441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (764100149/1000000000 : ℝ)^91 ≤ (14429535158461/20000000000000 : ℝ)^75 := by
    have hnat : (764100149 : ℕ)^91*20000000000000^75 ≤ 14429535158461^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764100149 1000000000 14429535158461 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001049003/5000000000 : ℝ)^91 ≤ (7102951923639/50000000000000 : ℝ)^75 := by
    have hnat : (1001049003 : ℕ)^91*50000000000000^75 ≤ 7102951923639^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001049003 5000000000 7102951923639 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968441441/5000000000 : ℝ)^91 ≤ (3411605086533/25000000000000 : ℝ)^75 := by
    have hnat : (968441441 : ℕ)^91*25000000000000^75 ≤ 3411605086533^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968441441 5000000000 3411605086533 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(764100149/1000000000 : ℝ), (1001049003/5000000000 : ℝ), (968441441/5000000000 : ℝ)] ![(14429535158461/20000000000000 : ℝ), (7102951923639/50000000000000 : ℝ), (3411605086533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(764100149/1000000000 : ℝ)|^91 ≤ (14429535158461/20000000000000 : ℝ)^75
        have hw : |(764100149/1000000000 : ℝ)|=(764100149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001049003/5000000000 : ℝ)|^91 ≤ (7102951923639/50000000000000 : ℝ)^75
        have hw : |(1001049003/5000000000 : ℝ)|=(1001049003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968441441/5000000000 : ℝ)|^91 ≤ (3411605086533/25000000000000 : ℝ)^75
        have hw : |(968441441/5000000000 : ℝ)|=(968441441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-989454961/10000000000 : ℝ)*x 0 + (1242554989/2500000000 : ℝ)*x 1 + (5754318899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989454961/10000000000 : ℝ)^91 ≤ (1208121219821/20000000000000 : ℝ)^75 := by
    have hnat : (989454961 : ℕ)^91*20000000000000^75 ≤ 1208121219821^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989454961 10000000000 1208121219821 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1242554989/2500000000 : ℝ)^91 ≤ (66899432131/156250000000 : ℝ)^75 := by
    have hnat : (1242554989 : ℕ)^91*156250000000^75 ≤ 66899432131^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242554989 2500000000 66899432131 156250000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5754318899/10000000000 : ℝ)^91 ≤ (12785939331201/25000000000000 : ℝ)^75 := by
    have hnat : (5754318899 : ℕ)^91*25000000000000^75 ≤ 12785939331201^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754318899 10000000000 12785939331201 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989454961/10000000000 : ℝ), (1242554989/2500000000 : ℝ), (5754318899/10000000000 : ℝ)] ![(1208121219821/20000000000000 : ℝ), (66899432131/156250000000 : ℝ), (12785939331201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989454961/10000000000 : ℝ)|^91 ≤ (1208121219821/20000000000000 : ℝ)^75
        have hw : |(-989454961/10000000000 : ℝ)|=(989454961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1242554989/2500000000 : ℝ)|^91 ≤ (66899432131/156250000000 : ℝ)^75
        have hw : |(1242554989/2500000000 : ℝ)|=(1242554989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5754318899/10000000000 : ℝ)|^91 ≤ (12785939331201/25000000000000 : ℝ)^75
        have hw : |(5754318899/10000000000 : ℝ)|=(5754318899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2705127459/5000000000 : ℝ)*x 0 + (-987393389/10000000000 : ℝ)*x 1 + (5321761533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705127459/5000000000 : ℝ)^91 ≤ (9491485156491/20000000000000 : ℝ)^75 := by
    have hnat : (2705127459 : ℕ)^91*20000000000000^75 ≤ 9491485156491^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705127459 5000000000 9491485156491 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987393389/10000000000 : ℝ)^91 ≤ (6025338647947/100000000000000 : ℝ)^75 := by
    have hnat : (987393389 : ℕ)^91*100000000000000^75 ≤ 6025338647947^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987393389 10000000000 6025338647947 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5321761533/10000000000 : ℝ)^91 ≤ (46517235563637/100000000000000 : ℝ)^75 := by
    have hnat : (5321761533 : ℕ)^91*100000000000000^75 ≤ 46517235563637^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321761533 10000000000 46517235563637 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705127459/5000000000 : ℝ), (-987393389/10000000000 : ℝ), (5321761533/10000000000 : ℝ)] ![(9491485156491/20000000000000 : ℝ), (6025338647947/100000000000000 : ℝ), (46517235563637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705127459/5000000000 : ℝ)|^91 ≤ (9491485156491/20000000000000 : ℝ)^75
        have hw : |(2705127459/5000000000 : ℝ)|=(2705127459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987393389/10000000000 : ℝ)|^91 ≤ (6025338647947/100000000000000 : ℝ)^75
        have hw : |(-987393389/10000000000 : ℝ)|=(987393389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5321761533/10000000000 : ℝ)|^91 ≤ (46517235563637/100000000000000 : ℝ)^75
        have hw : |(5321761533/10000000000 : ℝ)|=(5321761533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2116168283/5000000000 : ℝ)*x 0 + (6620061511/10000000000 : ℝ)*x 1 + (-90686941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116168283/5000000000 : ℝ)^91 ≤ (35230378184497/100000000000000 : ℝ)^75 := by
    have hnat : (2116168283 : ℕ)^91*100000000000000^75 ≤ 35230378184497^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116168283 5000000000 35230378184497 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6620061511/10000000000 : ℝ)^91 ≤ (12124837283221/20000000000000 : ℝ)^75 := by
    have hnat : (6620061511 : ℕ)^91*20000000000000^75 ≤ 12124837283221^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6620061511 10000000000 12124837283221 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90686941/1250000000 : ℝ)^91 ≤ (4145435392043/100000000000000 : ℝ)^75 := by
    have hnat : (90686941 : ℕ)^91*100000000000000^75 ≤ 4145435392043^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90686941 1250000000 4145435392043 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116168283/5000000000 : ℝ), (6620061511/10000000000 : ℝ), (-90686941/1250000000 : ℝ)] ![(35230378184497/100000000000000 : ℝ), (12124837283221/20000000000000 : ℝ), (4145435392043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116168283/5000000000 : ℝ)|^91 ≤ (35230378184497/100000000000000 : ℝ)^75
        have hw : |(2116168283/5000000000 : ℝ)|=(2116168283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6620061511/10000000000 : ℝ)|^91 ≤ (12124837283221/20000000000000 : ℝ)^75
        have hw : |(6620061511/10000000000 : ℝ)|=(6620061511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90686941/1250000000 : ℝ)|^91 ≤ (4145435392043/100000000000000 : ℝ)^75
        have hw : |(-90686941/1250000000 : ℝ)|=(90686941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327061_s1_s1_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (15914171/20000000 : ℝ)*x 0 + (834194301/5000000000 : ℝ)*x 1 + (115045757/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15914171/20000000 : ℝ)^91 ≤ (18946175616759/25000000000000 : ℝ)^75 := by
    have hnat : (15914171 : ℕ)^91*25000000000000^75 ≤ 18946175616759^75*20000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15914171 20000000 18946175616759 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834194301/5000000000 : ℝ)^91 ≤ (11386422290981/100000000000000 : ℝ)^75 := by
    have hnat : (834194301 : ℕ)^91*100000000000000^75 ≤ 11386422290981^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834194301 5000000000 11386422290981 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115045757/625000000 : ℝ)^91 ≤ (6414437610377/50000000000000 : ℝ)^75 := by
    have hnat : (115045757 : ℕ)^91*50000000000000^75 ≤ 6414437610377^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115045757 625000000 6414437610377 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15914171/20000000 : ℝ), (834194301/5000000000 : ℝ), (115045757/625000000 : ℝ)] ![(18946175616759/25000000000000 : ℝ), (11386422290981/100000000000000 : ℝ), (6414437610377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15914171/20000000 : ℝ)|^91 ≤ (18946175616759/25000000000000 : ℝ)^75
        have hw : |(15914171/20000000 : ℝ)|=(15914171/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834194301/5000000000 : ℝ)|^91 ≤ (11386422290981/100000000000000 : ℝ)^75
        have hw : |(834194301/5000000000 : ℝ)|=(834194301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115045757/625000000 : ℝ)|^91 ≤ (6414437610377/50000000000000 : ℝ)^75
        have hw : |(115045757/625000000 : ℝ)|=(115045757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327061_s1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((64361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31931/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31931/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29463/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32543/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1183/4000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (64361/100000 : ℝ) ^ (89/16 : ℝ) ≤ (4309572946722020583/50000000000000000000 : ℝ) := by
    have hpowers : (64361/100000 : ℝ)^89 ≤ (4309572946722020583/50000000000000000000 : ℝ)^16 := by
      have hnat : (64361 : ℕ)^89*50000000000000000000^16 ≤ 4309572946722020583^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64361 100000 4309572946722020583 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64361/100000 : ℝ)) (X := (4309572946722020583/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (54309572946722020583/50000000000000000000 : ℝ) ≤ (2537435951497381/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (54309572946722020583/50000000000000000000 : ℝ)^16 ≤ (2537435951497381/2500000000000000 : ℝ)^89 := by
      have hnat : (54309572946722020583 : ℕ)^16*2500000000000000^89 ≤ 2537435951497381^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54309572946722020583 50000000000000000000 2537435951497381 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2537435951497381/2500000000000000 : ℝ)) (X := (54309572946722020583/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (29309572946722020583/25000000000000000000 : ℝ) ≤ (2572509541176361/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (29309572946722020583/25000000000000000000 : ℝ)^16 ≤ (2572509541176361/2500000000000000 : ℝ)^89 := by
      have hnat : (29309572946722020583 : ℕ)^16*2500000000000000^89 ≤ 2572509541176361^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29309572946722020583 25000000000000000000 2572509541176361 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2572509541176361/2500000000000000 : ℝ)) (X := (29309572946722020583/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(37435951497381/1609025000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1753679483949/80451250000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (64361/100000 : ℝ)) (alpha := (37435951497381/1609025000000000 : ℝ)) (beta := (1753679483949/80451250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64361/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(37435951497381/1609025000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1753679483949/80451250000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (31931/50000 : ℝ) ^ (89/16 : ℝ) ≤ (257935734645826407/3125000000000000000 : ℝ) := by
    have hpowers : (31931/50000 : ℝ)^89 ≤ (257935734645826407/3125000000000000000 : ℝ)^16 := by
      have hnat : (31931 : ℕ)^89*3125000000000000000^16 ≤ 257935734645826407^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31931 50000 257935734645826407 3125000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31931/50000 : ℝ)) (X := (257935734645826407/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3382935734645826407/3125000000000000000 : ℝ) ≤ (10143600361579381/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3382935734645826407/3125000000000000000 : ℝ)^16 ≤ (10143600361579381/10000000000000000 : ℝ)^89 := by
      have hnat : (3382935734645826407 : ℕ)^16*10000000000000000^89 ≤ 10143600361579381^89*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3382935734645826407 3125000000000000000 10143600361579381 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10143600361579381/10000000000000000 : ℝ)) (X := (3382935734645826407/3125000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1820435734645826407/1562500000000000000 : ℝ) ≤ (10278483602232623/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (1820435734645826407/1562500000000000000 : ℝ)^16 ≤ (10278483602232623/10000000000000000 : ℝ)^89 := by
      have hnat : (1820435734645826407 : ℕ)^16*10000000000000000^89 ≤ 10278483602232623^89*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1820435734645826407 1562500000000000000 10278483602232623 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10278483602232623/10000000000000000 : ℝ)) (X := (1820435734645826407/1562500000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(143600361579381/6386200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(67441620326621/3193100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (31931/50000 : ℝ)) (alpha := (143600361579381/6386200000000000 : ℝ)) (beta := (67441620326621/3193100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (31931/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(143600361579381/6386200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(67441620326621/3193100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (29463/50000 : ℝ) ^ (89/16 : ℝ) ≤ (131908408828039713/2500000000000000000 : ℝ) := by
    have hpowers : (29463/50000 : ℝ)^89 ≤ (131908408828039713/2500000000000000000 : ℝ)^16 := by
      have hnat : (29463 : ℕ)^89*2500000000000000000^16 ≤ 131908408828039713^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29463 50000 131908408828039713 2500000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29463/50000 : ℝ)) (X := (131908408828039713/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2631908408828039713/2500000000000000000 : ℝ) ≤ (10092866276360589/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2631908408828039713/2500000000000000000 : ℝ)^16 ≤ (10092866276360589/10000000000000000 : ℝ)^89 := by
      have hnat : (2631908408828039713 : ℕ)^16*10000000000000000^89 ≤ 10092866276360589^89*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2631908408828039713 2500000000000000000 10092866276360589 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10092866276360589/10000000000000000 : ℝ)) (X := (2631908408828039713/2500000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1381908408828039713/1250000000000000000 : ℝ) ≤ (2545497543114991/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (1381908408828039713/1250000000000000000 : ℝ)^16 ≤ (2545497543114991/2500000000000000 : ℝ)^89 := by
      have hnat : (1381908408828039713 : ℕ)^16*2500000000000000^89 ≤ 2545497543114991^89*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1381908408828039713 1250000000000000000 2545497543114991 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2545497543114991/2500000000000000 : ℝ)) (X := (1381908408828039713/1250000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(92866276360589/5892600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(142598233759/9428160000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (29463/50000 : ℝ)) (alpha := (92866276360589/5892600000000000 : ℝ)) (beta := (142598233759/9428160000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29463/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(92866276360589/5892600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(142598233759/9428160000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1760188093/10000000000 : ℝ)*X 0 0+(547829607/1250000000 : ℝ)*X 0 1+(5749789387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4611181887/10000000000 : ℝ)*X 1 0+(-1760915133/10000000000 : ℝ)*X 1 1+(5531464483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4655025833/10000000000 : ℝ)*X 2 0+(6149948189/10000000000 : ℝ)*X 2 1+(-169761643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6523947417/10000000000 : ℝ)*X 0 0+(482038033/2000000000 : ℝ)*X 0 1+(735200991/2500000000 : ℝ)*X 0 2+(6523947417/10000000000 : ℝ)*X 1 0+(482038033/2000000000 : ℝ)*X 1 1+(735200991/2500000000 : ℝ)*X 1 2+(6523947417/10000000000 : ℝ)*X 2 0+(482038033/2000000000 : ℝ)*X 2 1+(735200991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-179669257/1000000000 : ℝ)*X 0 0+(1993674553/5000000000 : ℝ)*X 0 1+(1217727183/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((54154113/125000000 : ℝ)*X 1 0+(-17081953/125000000 : ℝ)*X 1 1+(6093069713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4376370543/10000000000 : ℝ)*X 2 0+(1345138347/2000000000 : ℝ)*X 2 1+(-315579203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((330831339/500000000 : ℝ)*X 0 0+(1639138127/5000000000 : ℝ)*X 0 1+(964118331/5000000000 : ℝ)*X 0 2+(330831339/500000000 : ℝ)*X 1 0+(1639138127/5000000000 : ℝ)*X 1 1+(964118331/5000000000 : ℝ)*X 1 2+(330831339/500000000 : ℝ)*X 2 0+(1639138127/5000000000 : ℝ)*X 2 1+(964118331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1011979989/10000000000 : ℝ)*X 0 0+(921418171/2000000000 : ℝ)*X 0 1+(3042980037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4286094063/10000000000 : ℝ)*X 1 0+(-357252811/2500000000 : ℝ)*X 1 1+(60903909/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5431766613/10000000000 : ℝ)*X 2 0+(28606633/50000000 : ℝ)*X 2 1+(-15912729/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((764100149/1000000000 : ℝ)*X 0 0+(1001049003/5000000000 : ℝ)*X 0 1+(968441441/5000000000 : ℝ)*X 0 2+(764100149/1000000000 : ℝ)*X 1 0+(1001049003/5000000000 : ℝ)*X 1 1+(968441441/5000000000 : ℝ)*X 1 2+(764100149/1000000000 : ℝ)*X 2 0+(1001049003/5000000000 : ℝ)*X 2 1+(968441441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-989454961/10000000000 : ℝ)*X 0 0+(1242554989/2500000000 : ℝ)*X 0 1+(5754318899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2705127459/5000000000 : ℝ)*X 1 0+(-987393389/10000000000 : ℝ)*X 1 1+(5321761533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2116168283/5000000000 : ℝ)*X 2 0+(6620061511/10000000000 : ℝ)*X 2 1+(-90686941/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((15914171/20000000 : ℝ)*X 0 0+(834194301/5000000000 : ℝ)*X 0 1+(115045757/625000000 : ℝ)*X 0 2+(15914171/20000000 : ℝ)*X 1 0+(834194301/5000000000 : ℝ)*X 1 1+(115045757/625000000 : ℝ)*X 1 2+(15914171/20000000 : ℝ)*X 2 0+(834194301/5000000000 : ℝ)*X 2 1+(115045757/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((26011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (117096340544333160449897384097/7792759082900000000000000000000000 : ℝ) := by norm_num
    linear_combination (347443196521/250000000000 : ℝ)*(base59) + (6291012858387/1000000000000 : ℝ)*(major_s1_0) + (6291012858387/1000000000000 : ℝ)*(major_s1_1) + (6291012858387/1000000000000 : ℝ)*(major_s1_2) + (14511411/62500000000 : ℝ)*(sp_s1_0) + (32837951/200000000000 : ℝ)*(sp_s1_1) + (49774409/500000000000 : ℝ)*(sp_s1_6) + (9608872814241/1000000000000 : ℝ)*(sp_s1_7) + (96082869597/10000000000 : ℝ)*(sp_s1_8) + (9608855978277/1000000000000 : ℝ)*(sp_s1_9) + (743203590803/250000000000 : ℝ)*(sp_s1_13) + (1799151/1000000000000 : ℝ)*(sp_s1_14) + (40977907/62500000000 : ℝ)*(sp_s1_15) + (25081769/100000000000 : ℝ)*(sp_s1_23) + (297291391203/100000000000 : ℝ)*(f.failure) + (9609106795967/1000000000000 : ℝ)*(f.sum) + (381539411132346007/847552300000000000000000000000 : ℝ)*base63 + (2551377691921/15713600000000000000000000 : ℝ)*base65 + (22696154946939/86300000000000000000000000 : ℝ)*base66 + (1058464996747041/1964200000000000000000000000 : ℝ)*base69 + (46343506281170048021/126417876200000000000000000000000 : ℝ)*base71 + (226637282540683/643610000000000000000000000 : ℝ)*base73 + (94846294115511/172600000000000000000000000 : ℝ)*base75 + (1251253558838479/3218050000000000000000000000 : ℝ)*base77 + (420714510485811901/5554354300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (11967/10000000000000000 : ℝ)*base86 + (11967/10000000000000000 : ℝ)*base88 + (11967/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32543/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1160344413542513450274073777189/144166043033650000000000000000000000 : ℝ) := by norm_num
    linear_combination (50183/1000000000000 : ℝ)*(base40) + (607029/500000000000 : ℝ)*(base49) + (78328834737/100000000000 : ℝ)*(base59) + (5942922608189/1000000000000 : ℝ)*(major_s1_0) + (5942922608189/1000000000000 : ℝ)*(major_s1_1) + (5942922608189/1000000000000 : ℝ)*(major_s1_2) + (5382419/200000000000 : ℝ)*(sp_s1_2) + (40391389/1000000000000 : ℝ)*(sp_s1_6) + (5354953/125000000000 : ℝ)*(sp_s1_7) + (4538690564759/500000000000 : ℝ)*(sp_s1_14) + (4538711984571/500000000000 : ℝ)*(sp_s1_15) + (9077397057047/1000000000000 : ℝ)*(sp_s1_16) + (1404123759141/500000000000 : ℝ)*(sp_s1_20) + (13065467/100000000000 : ℝ)*(sp_s1_27) + (1404209282171/500000000000 : ℝ)*(f.failure) + (4538711984571/500000000000 : ℝ)*(f.sum) + (6558694431884436097/13439757900000000000000000000000 : ℝ)*base63 + (13000989002461/168360000000000000000000000 : ℝ)*base64 + (1018564812915249/3193100000000000000000000000 : ℝ)*base67 + (383068603434883/841800000000000000000000000 : ℝ)*base69 + (25468036673079761303/54179089800000000000000000000000 : ℝ)*base71 + (14896321428767/40225625000000000000000000 : ℝ)*base72 + (3111501837478829/6386200000000000000000000000 : ℝ)*base75 + (937813442742279/1609025000000000000000000000 : ℝ)*base77 + (28425623662899342761/205511109100000000000000000000000 : ℝ)*base78 + (37481/50000000000000000 : ℝ)*base87 + (37481/50000000000000000 : ℝ)*base89 + (37481/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1183/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36993276212800548824972717769/8775324358570000000000000000000000 : ℝ) := by norm_num
    linear_combination (2352561/500000000000 : ℝ)*(base11) + (2181283/1000000000000 : ℝ)*(base15) + (357613659813/1000000000000 : ℝ)*(base40) + (39343048179/50000000000 : ℝ)*(base59) + (1071549663699/200000000000 : ℝ)*(major_s1_0) + (1071549663699/200000000000 : ℝ)*(major_s1_1) + (1071549663699/200000000000 : ℝ)*(major_s1_2) + (5871801/1000000000000 : ℝ)*(sp_s1_0) + (69491/6250000000 : ℝ)*(sp_s1_2) + (65097/2500000000 : ℝ)*(sp_s1_9) + (818359911087/100000000000 : ℝ)*(sp_s1_21) + (8183607506509/1000000000000 : ℝ)*(sp_s1_22) + (8183572530431/1000000000000 : ℝ)*(sp_s1_23) + (2531885543991/1000000000000 : ℝ)*(sp_s1_27) + (2531885543991/1000000000000 : ℝ)*(f.failure) + (511475605487/62500000000 : ℝ)*(f.sum) + (26172479405223413/272690740000000000000000000000 : ℝ)*base63 + (4905699913889/17080000000000000000000000 : ℝ)*base64 + (105414905443879/638620000000000000000000000 : ℝ)*base66 + (7426994035123/17080000000000000000000000 : ℝ)*base69 + (312926413732853451/1099285880000000000000000000000 : ℝ)*base71 + (49639430083289/643610000000000000000000000 : ℝ)*base72 + (175591808855259/255448000000000000000000000 : ℝ)*base75 + (133543890323259/128722000000000000000000000 : ℝ)*base77 + (7785204918948561569/41102221820000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + (20499/100000000000000000 : ℝ)*base86 + (20499/100000000000000000 : ℝ)*base88 + (20499/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((64361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31931/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31931/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29463/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32543/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1183/4000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c327061_s1 p hpa hpb X hX hprev0

#print axioms solution

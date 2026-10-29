-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c329054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:28:07.807431+00:00
-- url     : https://prove2.me/submissions/65e2a32b-a9a3-4274-8ba3-23a9390514e7

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
theorem collision_support_c329054_s1_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-226246821/2500000000 : ℝ)*x 0 + (1140906621/2500000000 : ℝ)*x 1 + (-6128985143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226246821/2500000000 : ℝ)^95 ≤ (1112652521767/20000000000000 : ℝ)^79 := by
    have hnat : (226246821 : ℕ)^95*20000000000000^79 ≤ 1112652521767^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226246821 2500000000 1112652521767 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140906621/2500000000 : ℝ)^95 ≤ (2433266188451/6250000000000 : ℝ)^79 := by
    have hnat : (1140906621 : ℕ)^95*6250000000000^79 ≤ 2433266188451^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140906621 2500000000 2433266188451 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6128985143/10000000000 : ℝ)^95 ≤ (2220179134869/4000000000000 : ℝ)^79 := by
    have hnat : (6128985143 : ℕ)^95*4000000000000^79 ≤ 2220179134869^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6128985143 10000000000 2220179134869 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226246821/2500000000 : ℝ), (1140906621/2500000000 : ℝ), (-6128985143/10000000000 : ℝ)] ![(1112652521767/20000000000000 : ℝ), (2433266188451/6250000000000 : ℝ), (2220179134869/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226246821/2500000000 : ℝ)|^95 ≤ (1112652521767/20000000000000 : ℝ)^79
        have hw : |(-226246821/2500000000 : ℝ)|=(226246821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140906621/2500000000 : ℝ)|^95 ≤ (2433266188451/6250000000000 : ℝ)^79
        have hw : |(1140906621/2500000000 : ℝ)|=(1140906621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6128985143/10000000000 : ℝ)|^95 ≤ (2220179134869/4000000000000 : ℝ)^79
        have hw : |(-6128985143/10000000000 : ℝ)|=(6128985143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5044490569/10000000000 : ℝ)*x 0 + (5027293263/10000000000 : ℝ)*x 1 + (878065383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5044490569/10000000000 : ℝ)^95 ≤ (43916570289677/100000000000000 : ℝ)^79 := by
    have hnat : (5044490569 : ℕ)^95*100000000000000^79 ≤ 43916570289677^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044490569 10000000000 43916570289677 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027293263/10000000000 : ℝ)^95 ≤ (43736592902781/100000000000000 : ℝ)^79 := by
    have hnat : (5027293263 : ℕ)^95*100000000000000^79 ≤ 43736592902781^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027293263 10000000000 43736592902781 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878065383/5000000000 : ℝ)^95 ≤ (12346836792897/100000000000000 : ℝ)^79 := by
    have hnat : (878065383 : ℕ)^95*100000000000000^79 ≤ 12346836792897^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878065383 5000000000 12346836792897 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5044490569/10000000000 : ℝ), (5027293263/10000000000 : ℝ), (878065383/5000000000 : ℝ)] ![(43916570289677/100000000000000 : ℝ), (43736592902781/100000000000000 : ℝ), (12346836792897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5044490569/10000000000 : ℝ)|^95 ≤ (43916570289677/100000000000000 : ℝ)^79
        have hw : |(5044490569/10000000000 : ℝ)|=(5044490569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027293263/10000000000 : ℝ)|^95 ≤ (43736592902781/100000000000000 : ℝ)^79
        have hw : |(5027293263/10000000000 : ℝ)|=(5027293263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(878065383/5000000000 : ℝ)|^95 ≤ (12346836792897/100000000000000 : ℝ)^79
        have hw : |(878065383/5000000000 : ℝ)|=(878065383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5176332609/10000000000 : ℝ)*x 0 + (1290423947/2500000000 : ℝ)*x 1 + (-177344791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176332609/10000000000 : ℝ)^95 ≤ (45300460293791/100000000000000 : ℝ)^79 := by
    have hnat : (5176332609 : ℕ)^95*100000000000000^79 ≤ 45300460293791^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176332609 10000000000 45300460293791 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290423947/2500000000 : ℝ)^95 ≤ (4514646790811/10000000000000 : ℝ)^79 := by
    have hnat : (1290423947 : ℕ)^95*10000000000000^79 ≤ 4514646790811^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290423947 2500000000 4514646790811 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177344791/1250000000 : ℝ)^95 ≤ (9553071787387/100000000000000 : ℝ)^79 := by
    have hnat : (177344791 : ℕ)^95*100000000000000^79 ≤ 9553071787387^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177344791 1250000000 9553071787387 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176332609/10000000000 : ℝ), (1290423947/2500000000 : ℝ), (-177344791/1250000000 : ℝ)] ![(45300460293791/100000000000000 : ℝ), (4514646790811/10000000000000 : ℝ), (9553071787387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176332609/10000000000 : ℝ)|^95 ≤ (45300460293791/100000000000000 : ℝ)^79
        have hw : |(5176332609/10000000000 : ℝ)|=(5176332609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1290423947/2500000000 : ℝ)|^95 ≤ (4514646790811/10000000000000 : ℝ)^79
        have hw : |(1290423947/2500000000 : ℝ)|=(1290423947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177344791/1250000000 : ℝ)|^95 ≤ (9553071787387/100000000000000 : ℝ)^79
        have hw : |(-177344791/1250000000 : ℝ)|=(177344791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-871116007/10000000000 : ℝ)*x 0 + (885959527/2000000000 : ℝ)*x 1 + (-6277220591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871116007/10000000000 : ℝ)^95 ≤ (2656916129641/50000000000000 : ℝ)^79 := by
    have hnat : (871116007 : ℕ)^95*50000000000000^79 ≤ 2656916129641^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871116007 10000000000 2656916129641 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885959527/2000000000 : ℝ)^95 ≤ (9390861648851/25000000000000 : ℝ)^79 := by
    have hnat : (885959527 : ℕ)^95*25000000000000^79 ≤ 9390861648851^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885959527 2000000000 9390861648851 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6277220591/10000000000 : ℝ)^95 ≤ (57122721126383/100000000000000 : ℝ)^79 := by
    have hnat : (6277220591 : ℕ)^95*100000000000000^79 ≤ 57122721126383^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6277220591 10000000000 57122721126383 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-871116007/10000000000 : ℝ), (885959527/2000000000 : ℝ), (-6277220591/10000000000 : ℝ)] ![(2656916129641/50000000000000 : ℝ), (9390861648851/25000000000000 : ℝ), (57122721126383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-871116007/10000000000 : ℝ)|^95 ≤ (2656916129641/50000000000000 : ℝ)^79
        have hw : |(-871116007/10000000000 : ℝ)|=(871116007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(885959527/2000000000 : ℝ)|^95 ≤ (9390861648851/25000000000000 : ℝ)^79
        have hw : |(885959527/2000000000 : ℝ)|=(885959527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6277220591/10000000000 : ℝ)|^95 ≤ (57122721126383/100000000000000 : ℝ)^79
        have hw : |(-6277220591/10000000000 : ℝ)|=(6277220591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5342071979/10000000000 : ℝ)*x 0 + (-137973039/1000000000 : ℝ)*x 1 + (-2512459827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342071979/10000000000 : ℝ)^95 ≤ (23525146919957/50000000000000 : ℝ)^79 := by
    have hnat : (5342071979 : ℕ)^95*50000000000000^79 ≤ 23525146919957^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342071979 10000000000 23525146919957 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137973039/1000000000 : ℝ)^95 ≤ (4618972157983/50000000000000 : ℝ)^79 := by
    have hnat : (137973039 : ℕ)^95*50000000000000^79 ≤ 4618972157983^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137973039 1000000000 4618972157983 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512459827/5000000000 : ℝ)^95 ≤ (8742352364037/20000000000000 : ℝ)^79 := by
    have hnat : (2512459827 : ℕ)^95*20000000000000^79 ≤ 8742352364037^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512459827 5000000000 8742352364037 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342071979/10000000000 : ℝ), (-137973039/1000000000 : ℝ), (-2512459827/5000000000 : ℝ)] ![(23525146919957/50000000000000 : ℝ), (4618972157983/50000000000000 : ℝ), (8742352364037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342071979/10000000000 : ℝ)|^95 ≤ (23525146919957/50000000000000 : ℝ)^79
        have hw : |(5342071979/10000000000 : ℝ)|=(5342071979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137973039/1000000000 : ℝ)|^95 ≤ (4618972157983/50000000000000 : ℝ)^79
        have hw : |(-137973039/1000000000 : ℝ)|=(137973039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2512459827/5000000000 : ℝ)|^95 ≤ (8742352364037/20000000000000 : ℝ)^79
        have hw : |(-2512459827/5000000000 : ℝ)|=(2512459827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (616377439/1250000000 : ℝ)*x 0 + (5472786643/10000000000 : ℝ)*x 1 + (1328934769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (616377439/1250000000 : ℝ)^95 ≤ (21365678752137/50000000000000 : ℝ)^79 := by
    have hnat : (616377439 : ℕ)^95*50000000000000^79 ≤ 21365678752137^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616377439 1250000000 21365678752137 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472786643/10000000000 : ℝ)^95 ≤ (48438139956829/100000000000000 : ℝ)^79 := by
    have hnat : (5472786643 : ℕ)^95*100000000000000^79 ≤ 48438139956829^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472786643 10000000000 48438139956829 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328934769/10000000000 : ℝ)^95 ≤ (2207625629911/25000000000000 : ℝ)^79 := by
    have hnat : (1328934769 : ℕ)^95*25000000000000^79 ≤ 2207625629911^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328934769 10000000000 2207625629911 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(616377439/1250000000 : ℝ), (5472786643/10000000000 : ℝ), (1328934769/10000000000 : ℝ)] ![(21365678752137/50000000000000 : ℝ), (48438139956829/100000000000000 : ℝ), (2207625629911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(616377439/1250000000 : ℝ)|^95 ≤ (21365678752137/50000000000000 : ℝ)^79
        have hw : |(616377439/1250000000 : ℝ)|=(616377439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472786643/10000000000 : ℝ)|^95 ≤ (48438139956829/100000000000000 : ℝ)^79
        have hw : |(5472786643/10000000000 : ℝ)|=(5472786643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1328934769/10000000000 : ℝ)|^95 ≤ (2207625629911/25000000000000 : ℝ)^79
        have hw : |(1328934769/10000000000 : ℝ)|=(1328934769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1023274643/2000000000 : ℝ)*x 0 + (5579709243/10000000000 : ℝ)*x 1 + (-232592073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023274643/2000000000 : ℝ)^95 ≤ (44670195738243/100000000000000 : ℝ)^79 := by
    have hnat : (1023274643 : ℕ)^95*100000000000000^79 ≤ 44670195738243^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023274643 2000000000 44670195738243 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5579709243/10000000000 : ℝ)^95 ≤ (247891934661/500000000000 : ℝ)^79 := by
    have hnat : (5579709243 : ℕ)^95*500000000000^79 ≤ 247891934661^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579709243 10000000000 247891934661 500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232592073/2500000000 : ℝ)^95 ≤ (5751417315857/100000000000000 : ℝ)^79 := by
    have hnat : (232592073 : ℕ)^95*100000000000000^79 ≤ 5751417315857^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232592073 2500000000 5751417315857 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1023274643/2000000000 : ℝ), (5579709243/10000000000 : ℝ), (-232592073/2500000000 : ℝ)] ![(44670195738243/100000000000000 : ℝ), (247891934661/500000000000 : ℝ), (5751417315857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1023274643/2000000000 : ℝ)|^95 ≤ (44670195738243/100000000000000 : ℝ)^79
        have hw : |(1023274643/2000000000 : ℝ)|=(1023274643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5579709243/10000000000 : ℝ)|^95 ≤ (247891934661/500000000000 : ℝ)^79
        have hw : |(5579709243/10000000000 : ℝ)|=(5579709243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232592073/2500000000 : ℝ)|^95 ≤ (5751417315857/100000000000000 : ℝ)^79
        have hw : |(-232592073/2500000000 : ℝ)|=(232592073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-628512419/10000000000 : ℝ)*x 0 + (577702927/1250000000 : ℝ)*x 1 + (-6255336063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628512419/10000000000 : ℝ)^95 ≤ (3588677177809/100000000000000 : ℝ)^79 := by
    have hnat : (628512419 : ℕ)^95*100000000000000^79 ≤ 3588677177809^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628512419 10000000000 3588677177809 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (577702927/1250000000 : ℝ)^95 ≤ (19764000167039/50000000000000 : ℝ)^79 := by
    have hnat : (577702927 : ℕ)^95*50000000000000^79 ≤ 19764000167039^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577702927 1250000000 19764000167039 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6255336063/10000000000 : ℝ)^95 ≤ (28441661237573/50000000000000 : ℝ)^79 := by
    have hnat : (6255336063 : ℕ)^95*50000000000000^79 ≤ 28441661237573^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6255336063 10000000000 28441661237573 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-628512419/10000000000 : ℝ), (577702927/1250000000 : ℝ), (-6255336063/10000000000 : ℝ)] ![(3588677177809/100000000000000 : ℝ), (19764000167039/50000000000000 : ℝ), (28441661237573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-628512419/10000000000 : ℝ)|^95 ≤ (3588677177809/100000000000000 : ℝ)^79
        have hw : |(-628512419/10000000000 : ℝ)|=(628512419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(577702927/1250000000 : ℝ)|^95 ≤ (19764000167039/50000000000000 : ℝ)^79
        have hw : |(577702927/1250000000 : ℝ)|=(577702927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6255336063/10000000000 : ℝ)|^95 ≤ (28441661237573/50000000000000 : ℝ)^79
        have hw : |(-6255336063/10000000000 : ℝ)|=(6255336063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1031204099/2000000000 : ℝ)*x 0 + (-320645351/2000000000 : ℝ)*x 1 + (-1259472001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031204099/2000000000 : ℝ)^95 ≤ (22543391275061/50000000000000 : ℝ)^79 := by
    have hnat : (1031204099 : ℕ)^95*50000000000000^79 ≤ 22543391275061^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031204099 2000000000 22543391275061 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320645351/2000000000 : ℝ)^95 ≤ (2213152124531/20000000000000 : ℝ)^79 := by
    have hnat : (320645351 : ℕ)^95*20000000000000^79 ≤ 2213152124531^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320645351 2000000000 2213152124531 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259472001/2500000000 : ℝ)^95 ≤ (43847456817127/100000000000000 : ℝ)^79 := by
    have hnat : (1259472001 : ℕ)^95*100000000000000^79 ≤ 43847456817127^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259472001 2500000000 43847456817127 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031204099/2000000000 : ℝ), (-320645351/2000000000 : ℝ), (-1259472001/2500000000 : ℝ)] ![(22543391275061/50000000000000 : ℝ), (2213152124531/20000000000000 : ℝ), (43847456817127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031204099/2000000000 : ℝ)|^95 ≤ (22543391275061/50000000000000 : ℝ)^79
        have hw : |(1031204099/2000000000 : ℝ)|=(1031204099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-320645351/2000000000 : ℝ)|^95 ≤ (2213152124531/20000000000000 : ℝ)^79
        have hw : |(-320645351/2000000000 : ℝ)|=(320645351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1259472001/2500000000 : ℝ)|^95 ≤ (43847456817127/100000000000000 : ℝ)^79
        have hw : |(-1259472001/2500000000 : ℝ)|=(1259472001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (275047847/500000000 : ℝ)*x 0 + (4912158941/10000000000 : ℝ)*x 1 + (1315967679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275047847/500000000 : ℝ)^95 ≤ (48738120362463/100000000000000 : ℝ)^79 := by
    have hnat : (275047847 : ℕ)^95*100000000000000^79 ≤ 48738120362463^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275047847 500000000 48738120362463 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4912158941/10000000000 : ℝ)^95 ≤ (42534889017403/100000000000000 : ℝ)^79 := by
    have hnat : (4912158941 : ℕ)^95*100000000000000^79 ≤ 42534889017403^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4912158941 10000000000 42534889017403 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315967679/10000000000 : ℝ)^95 ≤ (4363495303251/50000000000000 : ℝ)^79 := by
    have hnat : (1315967679 : ℕ)^95*50000000000000^79 ≤ 4363495303251^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315967679 10000000000 4363495303251 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275047847/500000000 : ℝ), (4912158941/10000000000 : ℝ), (1315967679/10000000000 : ℝ)] ![(48738120362463/100000000000000 : ℝ), (42534889017403/100000000000000 : ℝ), (4363495303251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275047847/500000000 : ℝ)|^95 ≤ (48738120362463/100000000000000 : ℝ)^79
        have hw : |(275047847/500000000 : ℝ)|=(275047847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4912158941/10000000000 : ℝ)|^95 ≤ (42534889017403/100000000000000 : ℝ)^79
        have hw : |(4912158941/10000000000 : ℝ)|=(4912158941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315967679/10000000000 : ℝ)|^95 ≤ (4363495303251/50000000000000 : ℝ)^79
        have hw : |(1315967679/10000000000 : ℝ)|=(1315967679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5568757061/10000000000 : ℝ)*x 0 + (2536816061/5000000000 : ℝ)*x 1 + (-251453459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5568757061/10000000000 : ℝ)^95 ≤ (6182673172897/12500000000000 : ℝ)^79 := by
    have hnat : (5568757061 : ℕ)^95*12500000000000^79 ≤ 6182673172897^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5568757061 10000000000 6182673172897 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536816061/5000000000 : ℝ)^95 ≤ (176887332429/400000000000 : ℝ)^79 := by
    have hnat : (2536816061 : ℕ)^95*400000000000^79 ≤ 176887332429^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536816061 5000000000 176887332429 400000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251453459/2500000000 : ℝ)^95 ≤ (6316781499577/100000000000000 : ℝ)^79 := by
    have hnat : (251453459 : ℕ)^95*100000000000000^79 ≤ 6316781499577^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251453459 2500000000 6316781499577 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5568757061/10000000000 : ℝ), (2536816061/5000000000 : ℝ), (-251453459/2500000000 : ℝ)] ![(6182673172897/12500000000000 : ℝ), (176887332429/400000000000 : ℝ), (6316781499577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5568757061/10000000000 : ℝ)|^95 ≤ (6182673172897/12500000000000 : ℝ)^79
        have hw : |(5568757061/10000000000 : ℝ)|=(5568757061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536816061/5000000000 : ℝ)|^95 ≤ (176887332429/400000000000 : ℝ)^79
        have hw : |(2536816061/5000000000 : ℝ)|=(2536816061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251453459/2500000000 : ℝ)|^95 ≤ (6316781499577/100000000000000 : ℝ)^79
        have hw : |(-251453459/2500000000 : ℝ)|=(251453459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-115288613/2500000000 : ℝ)*x 0 + (4957664447/10000000000 : ℝ)*x 1 + (-3019121941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115288613/2500000000 : ℝ)^95 ≤ (2473050697583/100000000000000 : ℝ)^79 := by
    have hnat : (115288613 : ℕ)^95*100000000000000^79 ≤ 2473050697583^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115288613 2500000000 2473050697583 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4957664447/10000000000 : ℝ)^95 ≤ (2688073389261/6250000000000 : ℝ)^79 := by
    have hnat : (4957664447 : ℕ)^95*6250000000000^79 ≤ 2688073389261^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4957664447 10000000000 2688073389261 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3019121941/5000000000 : ℝ)^95 ≤ (54517775061223/100000000000000 : ℝ)^79 := by
    have hnat : (3019121941 : ℕ)^95*100000000000000^79 ≤ 54517775061223^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019121941 5000000000 54517775061223 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115288613/2500000000 : ℝ), (4957664447/10000000000 : ℝ), (-3019121941/5000000000 : ℝ)] ![(2473050697583/100000000000000 : ℝ), (2688073389261/6250000000000 : ℝ), (54517775061223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115288613/2500000000 : ℝ)|^95 ≤ (2473050697583/100000000000000 : ℝ)^79
        have hw : |(-115288613/2500000000 : ℝ)|=(115288613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4957664447/10000000000 : ℝ)|^95 ≤ (2688073389261/6250000000000 : ℝ)^79
        have hw : |(4957664447/10000000000 : ℝ)|=(4957664447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3019121941/5000000000 : ℝ)|^95 ≤ (54517775061223/100000000000000 : ℝ)^79
        have hw : |(-3019121941/5000000000 : ℝ)|=(3019121941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2944146149/5000000000 : ℝ)*x 0 + (-1413244731/10000000000 : ℝ)*x 1 + (-554144999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2944146149/5000000000 : ℝ)^95 ≤ (52893819292121/100000000000000 : ℝ)^79 := by
    have hnat : (2944146149 : ℕ)^95*100000000000000^79 ≤ 52893819292121^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944146149 5000000000 52893819292121 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413244731/10000000000 : ℝ)^95 ≤ (9508445061233/100000000000000 : ℝ)^79 := by
    have hnat : (1413244731 : ℕ)^95*100000000000000^79 ≤ 9508445061233^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413244731 10000000000 9508445061233 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554144999/1250000000 : ℝ)^95 ≤ (37597735629963/100000000000000 : ℝ)^79 := by
    have hnat : (554144999 : ℕ)^95*100000000000000^79 ≤ 37597735629963^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554144999 1250000000 37597735629963 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2944146149/5000000000 : ℝ), (-1413244731/10000000000 : ℝ), (-554144999/1250000000 : ℝ)] ![(52893819292121/100000000000000 : ℝ), (9508445061233/100000000000000 : ℝ), (37597735629963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2944146149/5000000000 : ℝ)|^95 ≤ (52893819292121/100000000000000 : ℝ)^79
        have hw : |(2944146149/5000000000 : ℝ)|=(2944146149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1413244731/10000000000 : ℝ)|^95 ≤ (9508445061233/100000000000000 : ℝ)^79
        have hw : |(-1413244731/10000000000 : ℝ)|=(1413244731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554144999/1250000000 : ℝ)|^95 ≤ (37597735629963/100000000000000 : ℝ)^79
        have hw : |(-554144999/1250000000 : ℝ)|=(554144999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (201366833/400000000 : ℝ)*x 0 + (1254197151/2500000000 : ℝ)*x 1 + (1781864383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201366833/400000000 : ℝ)^95 ≤ (21904277341269/50000000000000 : ℝ)^79 := by
    have hnat : (201366833 : ℕ)^95*50000000000000^79 ≤ 21904277341269^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201366833 400000000 21904277341269 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1254197151/2500000000 : ℝ)^95 ≤ (43626718318561/100000000000000 : ℝ)^79 := by
    have hnat : (1254197151 : ℕ)^95*100000000000000^79 ≤ 43626718318561^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254197151 2500000000 43626718318561 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1781864383/10000000000 : ℝ)^95 ≤ (2512945397619/20000000000000 : ℝ)^79 := by
    have hnat : (1781864383 : ℕ)^95*20000000000000^79 ≤ 2512945397619^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781864383 10000000000 2512945397619 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(201366833/400000000 : ℝ), (1254197151/2500000000 : ℝ), (1781864383/10000000000 : ℝ)] ![(21904277341269/50000000000000 : ℝ), (43626718318561/100000000000000 : ℝ), (2512945397619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(201366833/400000000 : ℝ)|^95 ≤ (21904277341269/50000000000000 : ℝ)^79
        have hw : |(201366833/400000000 : ℝ)|=(201366833/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1254197151/2500000000 : ℝ)|^95 ≤ (43626718318561/100000000000000 : ℝ)^79
        have hw : |(1254197151/2500000000 : ℝ)|=(1254197151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1781864383/10000000000 : ℝ)|^95 ≤ (2512945397619/20000000000000 : ℝ)^79
        have hw : |(1781864383/10000000000 : ℝ)|=(1781864383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s1_s1_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (653812781/1250000000 : ℝ)*x 0 + (5216441397/10000000000 : ℝ)*x 1 + (-637793151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653812781/1250000000 : ℝ)^95 ≤ (45871138931057/100000000000000 : ℝ)^79 := by
    have hnat : (653812781 : ℕ)^95*100000000000000^79 ≤ 45871138931057^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653812781 1250000000 45871138931057 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216441397/10000000000 : ℝ)^95 ≤ (45722891927819/100000000000000 : ℝ)^79 := by
    have hnat : (5216441397 : ℕ)^95*100000000000000^79 ≤ 45722891927819^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216441397 10000000000 45722891927819 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637793151/5000000000 : ℝ)^95 ≤ (2101492281457/25000000000000 : ℝ)^79 := by
    have hnat : (637793151 : ℕ)^95*25000000000000^79 ≤ 2101492281457^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637793151 5000000000 2101492281457 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653812781/1250000000 : ℝ), (5216441397/10000000000 : ℝ), (-637793151/5000000000 : ℝ)] ![(45871138931057/100000000000000 : ℝ), (45722891927819/100000000000000 : ℝ), (2101492281457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653812781/1250000000 : ℝ)|^95 ≤ (45871138931057/100000000000000 : ℝ)^79
        have hw : |(653812781/1250000000 : ℝ)|=(653812781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216441397/10000000000 : ℝ)|^95 ≤ (45722891927819/100000000000000 : ℝ)^79
        have hw : |(5216441397/10000000000 : ℝ)|=(5216441397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-637793151/5000000000 : ℝ)|^95 ≤ (2101492281457/25000000000000 : ℝ)^79
        have hw : |(-637793151/5000000000 : ℝ)|=(637793151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329054_s1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((58043/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58043/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61069/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10763/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10763/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((24273/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24273/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(808/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(808/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-401/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-401/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (58043/100000 : ℝ) ^ (93/16 : ℝ) ≤ (2117220130012829933/50000000000000000000 : ℝ) := by
    have hpowers : (58043/100000 : ℝ)^93 ≤ (2117220130012829933/50000000000000000000 : ℝ)^16 := by
      have hnat : (58043 : ℕ)^93*50000000000000000000^16 ≤ 2117220130012829933^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58043 100000 2117220130012829933 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58043/100000 : ℝ)) (X := (2117220130012829933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (52117220130012829933/50000000000000000000 : ℝ) ≤ (1007160553217521/1000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (52117220130012829933/50000000000000000000 : ℝ)^16 ≤ (1007160553217521/1000000000000000 : ℝ)^93 := by
      have hnat : (52117220130012829933 : ℕ)^16*1000000000000000^93 ≤ 1007160553217521^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52117220130012829933 50000000000000000000 1007160553217521 1000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007160553217521/1000000000000000 : ℝ)) (X := (52117220130012829933/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (27117220130012829933/25000000000000000000 : ℝ) ≤ (5070420876816051/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (27117220130012829933/25000000000000000000 : ℝ)^16 ≤ (5070420876816051/5000000000000000 : ℝ)^93 := by
      have hnat : (27117220130012829933 : ℕ)^16*5000000000000000^93 ≤ 5070420876816051^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27117220130012829933 25000000000000000000 5070420876816051 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5070420876816051/5000000000000000 : ℝ)) (X := (27117220130012829933/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7160553217521/580430000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(17309055364223/1451075000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (58043/100000 : ℝ)) (alpha := (7160553217521/580430000000000 : ℝ)) (beta := (17309055364223/1451075000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (58043/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7160553217521/580430000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(17309055364223/1451075000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (61069/100000 : ℝ) ^ (93/16 : ℝ) ≤ (56896224619841609/1000000000000000000 : ℝ) := by
    have hpowers : (61069/100000 : ℝ)^93 ≤ (56896224619841609/1000000000000000000 : ℝ)^16 := by
      have hnat : (61069 : ℕ)^93*1000000000000000000^16 ≤ 56896224619841609^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61069 100000 56896224619841609 1000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61069/100000 : ℝ)) (X := (56896224619841609/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (1056896224619841609/1000000000000000000 : ℝ) ≤ (2523914309634411/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (1056896224619841609/1000000000000000000 : ℝ)^16 ≤ (2523914309634411/2500000000000000 : ℝ)^93 := by
      have hnat : (1056896224619841609 : ℕ)^16*2500000000000000^93 ≤ 2523914309634411^93*1000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1056896224619841609 1000000000000000000 2523914309634411 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523914309634411/2500000000000000 : ℝ)) (X := (1056896224619841609/1000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (556896224619841609/500000000000000000 : ℝ) ≤ (2546785426822167/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (556896224619841609/500000000000000000 : ℝ)^16 ≤ (2546785426822167/2500000000000000 : ℝ)^93 := by
      have hnat : (556896224619841609 : ℕ)^16*2500000000000000^93 ≤ 2546785426822167^93*500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        556896224619841609 500000000000000000 2546785426822167 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2546785426822167/2500000000000000 : ℝ)) (X := (556896224619841609/500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(23914309634411/1526725000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5717779296939/381681250000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (61069/100000 : ℝ)) (alpha := (23914309634411/1526725000000000 : ℝ)) (beta := (5717779296939/381681250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61069/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(23914309634411/1526725000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5717779296939/381681250000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10763/20000 : ℝ) ^ (93/16 : ℝ) ≤ (136409838544359863/5000000000000000000 : ℝ) := by
    have hpowers : (10763/20000 : ℝ)^93 ≤ (136409838544359863/5000000000000000000 : ℝ)^16 := by
      have hnat : (10763 : ℕ)^93*5000000000000000000^16 ≤ 136409838544359863^16*20000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10763 20000 136409838544359863 5000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10763/20000 : ℝ)) (X := (136409838544359863/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5136409838544359863/5000000000000000000 : ℝ) ≤ (10046415254144311/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (5136409838544359863/5000000000000000000 : ℝ)^16 ≤ (10046415254144311/10000000000000000 : ℝ)^93 := by
      have hnat : (5136409838544359863 : ℕ)^16*10000000000000000^93 ≤ 10046415254144311^93*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5136409838544359863 5000000000000000000 10046415254144311 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046415254144311/10000000000000000 : ℝ)) (X := (5136409838544359863/5000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2636409838544359863/2500000000000000000 : ℝ) ≤ (1009182088356743/1000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2636409838544359863/2500000000000000000 : ℝ)^16 ≤ (1009182088356743/1000000000000000 : ℝ)^93 := by
      have hnat : (2636409838544359863 : ℕ)^16*1000000000000000^93 ≤ 1009182088356743^93*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2636409838544359863 2500000000000000000 1009182088356743 1000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009182088356743/1000000000000000 : ℝ)) (X := (2636409838544359863/2500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(46415254144311/5381500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(45405629423119/5381500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (10763/20000 : ℝ)) (alpha := (46415254144311/5381500000000000 : ℝ)) (beta := (45405629423119/5381500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10763/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(46415254144311/5381500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(45405629423119/5381500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-226246821/2500000000 : ℝ)*X 0 0+(1140906621/2500000000 : ℝ)*X 0 1+(-6128985143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5044490569/10000000000 : ℝ)*X 2 0+(5027293263/10000000000 : ℝ)*X 2 1+(878065383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5176332609/10000000000 : ℝ)*X 0 0+(1290423947/2500000000 : ℝ)*X 0 1+(-177344791/1250000000 : ℝ)*X 0 2+(5176332609/10000000000 : ℝ)*X 1 0+(1290423947/2500000000 : ℝ)*X 1 1+(-177344791/1250000000 : ℝ)*X 1 2+(5176332609/10000000000 : ℝ)*X 2 0+(1290423947/2500000000 : ℝ)*X 2 1+(-177344791/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-871116007/10000000000 : ℝ)*X 0 0+(885959527/2000000000 : ℝ)*X 0 1+(-6277220591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5342071979/10000000000 : ℝ)*X 1 0+(-137973039/1000000000 : ℝ)*X 1 1+(-2512459827/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((616377439/1250000000 : ℝ)*X 2 0+(5472786643/10000000000 : ℝ)*X 2 1+(1328934769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1023274643/2000000000 : ℝ)*X 0 0+(5579709243/10000000000 : ℝ)*X 0 1+(-232592073/2500000000 : ℝ)*X 0 2+(1023274643/2000000000 : ℝ)*X 1 0+(5579709243/10000000000 : ℝ)*X 1 1+(-232592073/2500000000 : ℝ)*X 1 2+(1023274643/2000000000 : ℝ)*X 2 0+(5579709243/10000000000 : ℝ)*X 2 1+(-232592073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-628512419/10000000000 : ℝ)*X 0 0+(577702927/1250000000 : ℝ)*X 0 1+(-6255336063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1031204099/2000000000 : ℝ)*X 1 0+(-320645351/2000000000 : ℝ)*X 1 1+(-1259472001/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((275047847/500000000 : ℝ)*X 2 0+(4912158941/10000000000 : ℝ)*X 2 1+(1315967679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((5568757061/10000000000 : ℝ)*X 0 0+(2536816061/5000000000 : ℝ)*X 0 1+(-251453459/2500000000 : ℝ)*X 0 2+(5568757061/10000000000 : ℝ)*X 1 0+(2536816061/5000000000 : ℝ)*X 1 1+(-251453459/2500000000 : ℝ)*X 1 2+(5568757061/10000000000 : ℝ)*X 2 0+(2536816061/5000000000 : ℝ)*X 2 1+(-251453459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-115288613/2500000000 : ℝ)*X 0 0+(4957664447/10000000000 : ℝ)*X 0 1+(-3019121941/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2944146149/5000000000 : ℝ)*X 1 0+(-1413244731/10000000000 : ℝ)*X 1 1+(-554144999/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((201366833/400000000 : ℝ)*X 2 0+(1254197151/2500000000 : ℝ)*X 2 1+(1781864383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((653812781/1250000000 : ℝ)*X 0 0+(5216441397/10000000000 : ℝ)*X 0 1+(-637793151/5000000000 : ℝ)*X 0 2+(653812781/1250000000 : ℝ)*X 1 0+(5216441397/10000000000 : ℝ)*X 1 1+(-637793151/5000000000 : ℝ)*X 1 2+(653812781/1250000000 : ℝ)*X 2 0+(5216441397/10000000000 : ℝ)*X 2 1+(-637793151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((24273/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24273/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (61253556092439939900523320413289/4768853851102625000000000000000000000 : ℝ) := by norm_num
    linear_combination (11116733/1000000000000 : ℝ)*(base23) + (19215615797/10000000000 : ℝ)*(base39) + (203274767121/250000000000 : ℝ)*(base60) + (11490426844603/1000000000000 : ℝ)*(major_s1_0) + (11490426844603/1000000000000 : ℝ)*(major_s1_1) + (11490426844603/1000000000000 : ℝ)*(major_s1_2) + (10994251/200000000000 : ℝ)*(sp_s1_6) + (4453297557281/250000000000 : ℝ)*(sp_s1_7) + (1781308680779/100000000000 : ℝ)*(sp_s1_8) + (8906580574359/500000000000 : ℝ)*(sp_s1_9) + (645940778117/125000000000 : ℝ)*(sp_s1_13) + (15596477/200000000000 : ℝ)*(sp_s1_14) + (181403719/1000000000000 : ℝ)*(sp_s1_15) + (47973029/500000000000 : ℝ)*(sp_s1_23) + (5167581196191/1000000000000 : ℝ)*(f.failure) + (17813268211509/1000000000000 : ℝ)*(f.sum) + (939926882715838843/328642823500000000000000000000000 : ℝ)*base62 + (2324269509689557/5381500000000000000000000000 : ℝ)*base65 + (954670560752341/3053450000000000000000000000 : ℝ)*base66 + (1684355319076033/5381500000000000000000000000 : ℝ)*base69 + (37983436600818805651/312358404500000000000000000000000 : ℝ)*base71 + (579800901284071/1451075000000000000000000000 : ℝ)*base72 + (1148661760047321/3053450000000000000000000000 : ℝ)*base75 + (206759535411121/580430000000000000000000000 : ℝ)*base77 + (8063575178092652133/88615699175000000000000000000000 : ℝ)*base78 + (13501/25000000000000000 : ℝ)*base86 + (13501/25000000000000000 : ℝ)*base88 + (13501/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(808/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(808/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84558929240076770221719692817183/4768853851102625000000000000000000000 : ℝ) := by norm_num
    linear_combination (8841413/500000000000 : ℝ)*(base21) + (461961510783/250000000000 : ℝ)*(base39) + (469771554899/1000000000000 : ℝ)*(base60) + (11418551178757/1000000000000 : ℝ)*(major_s1_0) + (11418551178757/1000000000000 : ℝ)*(major_s1_1) + (11418551178757/1000000000000 : ℝ)*(major_s1_2) + (10400263/500000000000 : ℝ)*(sp_s1_0) + (99926927/1000000000000 : ℝ)*(sp_s1_7) + (150394447/1000000000000 : ℝ)*(sp_s1_8) + (2212714889199/125000000000 : ℝ)*(sp_s1_14) + (8850844723299/500000000000 : ℝ)*(sp_s1_15) + (17701727119039/1000000000000 : ℝ)*(sp_s1_16) + (1283814151491/250000000000 : ℝ)*(sp_s1_20) + (95039181/1000000000000 : ℝ)*(sp_s1_23) + (1283814151491/250000000000 : ℝ)*(f.failure) + (3540367968209/200000000000 : ℝ)*(f.sum) + (150227712327482388433/328642823500000000000000000000000 : ℝ)*base63 + (3506487232275267/5381500000000000000000000000 : ℝ)*base64 + (350688773696291/3053450000000000000000000000 : ℝ)*base67 + (1865897216111377/5381500000000000000000000000 : ℝ)*base69 + (172952886338545342481/312358404500000000000000000000000 : ℝ)*base70 + (220835538988233/725537500000000000000000000 : ℝ)*base73 + (2704511982272951/3053450000000000000000000000 : ℝ)*base74 + (31136605625217/72553750000000000000000000 : ℝ)*base76 + (12592496319997875653/88615699175000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1949/6250000000000000 : ℝ)*base87 + (1949/6250000000000000 : ℝ)*base89 + (1949/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-401/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-401/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (680944385073681374593942587/82160705875000000000000000000000 : ℝ) := by norm_num
    linear_combination (6751917/1000000000000 : ℝ)*(base11) + (51683197841/31250000000 : ℝ)*(base39) + (132699/500000000000 : ℝ)*(base50) + (4906074653/125000000000 : ℝ)*(base60) + (7452448638401/1000000000000 : ℝ)*(major_s1_0) + (7452448638401/1000000000000 : ℝ)*(major_s1_1) + (7452448638401/1000000000000 : ℝ)*(major_s1_2) + (49671333/1000000000000 : ℝ)*(sp_s1_0) + (596232179/500000000000 : ℝ)*(sp_s1_2) + (990763/50000000000 : ℝ)*(sp_s1_20) + (11553253857321/1000000000000 : ℝ)*(sp_s1_21) + (2888327570143/250000000000 : ℝ)*(sp_s1_22) + (5776058908107/500000000000 : ℝ)*(sp_s1_23) + (418945552289/125000000000 : ℝ)*(sp_s1_27) + (837896058393/250000000000 : ℝ)*(f.failure) + (2888327570143/250000000000 : ℝ)*(f.sum) + (163882827786746664281/328642823500000000000000000000000 : ℝ)*base62 + (1246757166872269/5381500000000000000000000000 : ℝ)*base65 + (26729298425813/3053450000000000000000000000 : ℝ)*base67 + (5825486294613089/5381500000000000000000000000 : ℝ)*base68 + (151163866273416741667/312358404500000000000000000000000 : ℝ)*base71 + (951751160800783/1451075000000000000000000000 : ℝ)*base73 + (1035707490207369/1526725000000000000000000000 : ℝ)*base74 + (370361636854821/580430000000000000000000000 : ℝ)*base76 + (3650118158693986763/44307849587500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (2227/6250000000000000 : ℝ)*base87 + (2227/6250000000000000 : ℝ)*base89 + (2227/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((58043/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58043/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61069/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10763/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10763/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((24273/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24273/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(808/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(808/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-401/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-401/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c329054_s1 p hpa hpb X hX hprev0

#print axioms solution

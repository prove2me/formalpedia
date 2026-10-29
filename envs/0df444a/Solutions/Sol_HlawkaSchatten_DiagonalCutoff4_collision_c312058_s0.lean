-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312058_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:06.484391+00:00
-- url     : https://prove2.me/submissions/bee7c8e2-c592-43ba-97bb-5f8e721ce1fa

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
theorem collision_support_c312058_s0_s0_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3015618611/10000000000 : ℝ)*x 0 + (603123891/2000000000 : ℝ)*x 1 + (-3220185429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3015618611/10000000000 : ℝ)^73 ≤ (538488545837/2500000000000 : ℝ)^57 := by
    have hnat : (3015618611 : ℕ)^73*2500000000000^57 ≤ 538488545837^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015618611 10000000000 538488545837 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603123891/2000000000 : ℝ)^73 ≤ (21539549554071/100000000000000 : ℝ)^57 := by
    have hnat : (603123891 : ℕ)^73*100000000000000^57 ≤ 21539549554071^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603123891 2000000000 21539549554071 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3220185429/5000000000 : ℝ)^73 ≤ (28460454300983/50000000000000 : ℝ)^57 := by
    have hnat : (3220185429 : ℕ)^73*50000000000000^57 ≤ 28460454300983^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220185429 5000000000 28460454300983 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3015618611/10000000000 : ℝ), (603123891/2000000000 : ℝ), (-3220185429/5000000000 : ℝ)] ![(538488545837/2500000000000 : ℝ), (21539549554071/100000000000000 : ℝ), (28460454300983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3015618611/10000000000 : ℝ)|^73 ≤ (538488545837/2500000000000 : ℝ)^57
        have hw : |(-3015618611/10000000000 : ℝ)|=(3015618611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603123891/2000000000 : ℝ)|^73 ≤ (21539549554071/100000000000000 : ℝ)^57
        have hw : |(603123891/2000000000 : ℝ)|=(603123891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3220185429/5000000000 : ℝ)|^73 ≤ (28460454300983/50000000000000 : ℝ)^57
        have hw : |(-3220185429/5000000000 : ℝ)|=(3220185429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (60312417/200000000 : ℝ)*x 0 + (-1507811183/5000000000 : ℝ)*x 1 + (-805045837/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60312417/200000000 : ℝ)^73 ≤ (21539562315001/100000000000000 : ℝ)^57 := by
    have hnat : (60312417 : ℕ)^73*100000000000000^57 ≤ 21539562315001^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60312417 200000000 21539562315001 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507811183/5000000000 : ℝ)^73 ≤ (10769788091397/50000000000000 : ℝ)^57 := by
    have hnat : (1507811183 : ℕ)^73*50000000000000^57 ≤ 10769788091397^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507811183 5000000000 10769788091397 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805045837/1250000000 : ℝ)^73 ≤ (14230215373049/25000000000000 : ℝ)^57 := by
    have hnat : (805045837 : ℕ)^73*25000000000000^57 ≤ 14230215373049^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805045837 1250000000 14230215373049 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60312417/200000000 : ℝ), (-1507811183/5000000000 : ℝ), (-805045837/1250000000 : ℝ)] ![(21539562315001/100000000000000 : ℝ), (10769788091397/50000000000000 : ℝ), (14230215373049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60312417/200000000 : ℝ)|^73 ≤ (21539562315001/100000000000000 : ℝ)^57
        have hw : |(60312417/200000000 : ℝ)|=(60312417/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1507811183/5000000000 : ℝ)|^73 ≤ (10769788091397/50000000000000 : ℝ)^57
        have hw : |(-1507811183/5000000000 : ℝ)|=(1507811183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-805045837/1250000000 : ℝ)|^73 ≤ (14230215373049/25000000000000 : ℝ)^57
        have hw : |(-805045837/1250000000 : ℝ)|=(805045837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025469579/5000000000 : ℝ)*x 0 + (423984021/5000000000 : ℝ)*x 1 + (-8614349169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025469579/5000000000 : ℝ)^73 ≤ (3286674710419/25000000000000 : ℝ)^57 := by
    have hnat : (1025469579 : ℕ)^73*25000000000000^57 ≤ 3286674710419^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025469579 5000000000 3286674710419 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423984021/5000000000 : ℝ)^73 ≤ (424202991041/10000000000000 : ℝ)^57 := by
    have hnat : (423984021 : ℕ)^73*10000000000000^57 ≤ 424202991041^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423984021 5000000000 424202991041 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8614349169/10000000000 : ℝ)^73 ≤ (16522254248723/20000000000000 : ℝ)^57 := by
    have hnat : (8614349169 : ℕ)^73*20000000000000^57 ≤ 16522254248723^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8614349169 10000000000 16522254248723 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025469579/5000000000 : ℝ), (423984021/5000000000 : ℝ), (-8614349169/10000000000 : ℝ)] ![(3286674710419/25000000000000 : ℝ), (424202991041/10000000000000 : ℝ), (16522254248723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025469579/5000000000 : ℝ)|^73 ≤ (3286674710419/25000000000000 : ℝ)^57
        have hw : |(-1025469579/5000000000 : ℝ)|=(1025469579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423984021/5000000000 : ℝ)|^73 ≤ (424202991041/10000000000000 : ℝ)^57
        have hw : |(423984021/5000000000 : ℝ)|=(423984021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8614349169/10000000000 : ℝ)|^73 ≤ (16522254248723/20000000000000 : ℝ)^57
        have hw : |(-8614349169/10000000000 : ℝ)|=(8614349169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9935617/62500000 : ℝ)*x 0 + (-172279403/1250000000 : ℝ)*x 1 + (-1722869807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9935617/62500000 : ℝ)^73 ≤ (948686006469/10000000000000 : ℝ)^57 := by
    have hnat : (9935617 : ℕ)^73*10000000000000^57 ≤ 948686006469^57*62500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9935617 62500000 948686006469 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172279403/1250000000 : ℝ)^73 ≤ (7901870321389/100000000000000 : ℝ)^57 := by
    have hnat : (172279403 : ℕ)^73*100000000000000^57 ≤ 7901870321389^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172279403 1250000000 7901870321389 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722869807/2000000000 : ℝ)^73 ≤ (82611269597843/100000000000000 : ℝ)^57 := by
    have hnat : (1722869807 : ℕ)^73*100000000000000^57 ≤ 82611269597843^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722869807 2000000000 82611269597843 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9935617/62500000 : ℝ), (-172279403/1250000000 : ℝ), (-1722869807/2000000000 : ℝ)] ![(948686006469/10000000000000 : ℝ), (7901870321389/100000000000000 : ℝ), (82611269597843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9935617/62500000 : ℝ)|^73 ≤ (948686006469/10000000000000 : ℝ)^57
        have hw : |(9935617/62500000 : ℝ)|=(9935617/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172279403/1250000000 : ℝ)|^73 ≤ (7901870321389/100000000000000 : ℝ)^57
        have hw : |(-172279403/1250000000 : ℝ)|=(172279403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722869807/2000000000 : ℝ)|^73 ≤ (82611269597843/100000000000000 : ℝ)^57
        have hw : |(-1722869807/2000000000 : ℝ)|=(1722869807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3282851799/10000000000 : ℝ)*x 0 + (7083723477/10000000000 : ℝ)*x 1 + (1870406861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3282851799/10000000000 : ℝ)^73 ≤ (24013870389101/100000000000000 : ℝ)^57 := by
    have hnat : (3282851799 : ℕ)^73*100000000000000^57 ≤ 24013870389101^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282851799 10000000000 24013870389101 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7083723477/10000000000 : ℝ)^73 ≤ (12860556553393/20000000000000 : ℝ)^57 := by
    have hnat : (7083723477 : ℕ)^73*20000000000000^57 ≤ 12860556553393^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7083723477 10000000000 12860556553393 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870406861/10000000000 : ℝ)^73 ≤ (1460418353403/12500000000000 : ℝ)^57 := by
    have hnat : (1870406861 : ℕ)^73*12500000000000^57 ≤ 1460418353403^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870406861 10000000000 1460418353403 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3282851799/10000000000 : ℝ), (7083723477/10000000000 : ℝ), (1870406861/10000000000 : ℝ)] ![(24013870389101/100000000000000 : ℝ), (12860556553393/20000000000000 : ℝ), (1460418353403/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3282851799/10000000000 : ℝ)|^73 ≤ (24013870389101/100000000000000 : ℝ)^57
        have hw : |(3282851799/10000000000 : ℝ)|=(3282851799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7083723477/10000000000 : ℝ)|^73 ≤ (12860556553393/20000000000000 : ℝ)^57
        have hw : |(7083723477/10000000000 : ℝ)|=(7083723477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870406861/10000000000 : ℝ)|^73 ≤ (1460418353403/12500000000000 : ℝ)^57
        have hw : |(1870406861/10000000000 : ℝ)|=(1870406861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1705224923/10000000000 : ℝ)*x 0 + (4589990123/5000000000 : ℝ)*x 1 + (-38009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1705224923/10000000000 : ℝ)^73 ≤ (324333240059/3125000000000 : ℝ)^57 := by
    have hnat : (1705224923 : ℕ)^73*3125000000000^57 ≤ 324333240059^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705224923 10000000000 324333240059 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4589990123/5000000000 : ℝ)^73 ≤ (89621324864079/100000000000000 : ℝ)^57 := by
    have hnat : (4589990123 : ℕ)^73*100000000000000^57 ≤ 89621324864079^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589990123 5000000000 89621324864079 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38009/10000000000 : ℝ)^73 ≤ (572033/5000000000000 : ℝ)^57 := by
    have hnat : (38009 : ℕ)^73*5000000000000^57 ≤ 572033^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38009 10000000000 572033 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1705224923/10000000000 : ℝ), (4589990123/5000000000 : ℝ), (-38009/10000000000 : ℝ)] ![(324333240059/3125000000000 : ℝ), (89621324864079/100000000000000 : ℝ), (572033/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1705224923/10000000000 : ℝ)|^73 ≤ (324333240059/3125000000000 : ℝ)^57
        have hw : |(1705224923/10000000000 : ℝ)|=(1705224923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4589990123/5000000000 : ℝ)|^73 ≤ (89621324864079/100000000000000 : ℝ)^57
        have hw : |(4589990123/5000000000 : ℝ)|=(4589990123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38009/10000000000 : ℝ)|^73 ≤ (572033/5000000000000 : ℝ)^57
        have hw : |(-38009/10000000000 : ℝ)|=(38009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1202147041/10000000000 : ℝ)*x 0 + (1768735813/10000000000 : ℝ)*x 1 + (-4302272013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1202147041/10000000000 : ℝ)^73 ≤ (265313937519/4000000000000 : ℝ)^57 := by
    have hnat : (1202147041 : ℕ)^73*4000000000000^57 ≤ 265313937519^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202147041 10000000000 265313937519 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1768735813/10000000000 : ℝ)^73 ≤ (10876286648071/100000000000000 : ℝ)^57 := by
    have hnat : (1768735813 : ℕ)^73*100000000000000^57 ≤ 10876286648071^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768735813 10000000000 10876286648071 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302272013/5000000000 : ℝ)^73 ≤ (82490864900539/100000000000000 : ℝ)^57 := by
    have hnat : (4302272013 : ℕ)^73*100000000000000^57 ≤ 82490864900539^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302272013 5000000000 82490864900539 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1202147041/10000000000 : ℝ), (1768735813/10000000000 : ℝ), (-4302272013/5000000000 : ℝ)] ![(265313937519/4000000000000 : ℝ), (10876286648071/100000000000000 : ℝ), (82490864900539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1202147041/10000000000 : ℝ)|^73 ≤ (265313937519/4000000000000 : ℝ)^57
        have hw : |(-1202147041/10000000000 : ℝ)|=(1202147041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1768735813/10000000000 : ℝ)|^73 ≤ (10876286648071/100000000000000 : ℝ)^57
        have hw : |(1768735813/10000000000 : ℝ)|=(1768735813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4302272013/5000000000 : ℝ)|^73 ≤ (82490864900539/100000000000000 : ℝ)^57
        have hw : |(-4302272013/5000000000 : ℝ)|=(4302272013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (300536767/2500000000 : ℝ)*x 0 + (-884367927/5000000000 : ℝ)*x 1 + (-537783999/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (300536767/2500000000 : ℝ)^73 ≤ (1658212157191/25000000000000 : ℝ)^57 := by
    have hnat : (300536767 : ℕ)^73*25000000000000^57 ≤ 1658212157191^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300536767 2500000000 1658212157191 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884367927/5000000000 : ℝ)^73 ≤ (10876286970957/100000000000000 : ℝ)^57 := by
    have hnat : (884367927 : ℕ)^73*100000000000000^57 ≤ 10876286970957^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884367927 5000000000 10876286970957 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537783999/625000000 : ℝ)^73 ≤ (16498172876973/20000000000000 : ℝ)^57 := by
    have hnat : (537783999 : ℕ)^73*20000000000000^57 ≤ 16498172876973^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537783999 625000000 16498172876973 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(300536767/2500000000 : ℝ), (-884367927/5000000000 : ℝ), (-537783999/625000000 : ℝ)] ![(1658212157191/25000000000000 : ℝ), (10876286970957/100000000000000 : ℝ), (16498172876973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(300536767/2500000000 : ℝ)|^73 ≤ (1658212157191/25000000000000 : ℝ)^57
        have hw : |(300536767/2500000000 : ℝ)|=(300536767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884367927/5000000000 : ℝ)|^73 ≤ (10876286970957/100000000000000 : ℝ)^57
        have hw : |(-884367927/5000000000 : ℝ)|=(884367927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537783999/625000000 : ℝ)|^73 ≤ (16498172876973/20000000000000 : ℝ)^57
        have hw : |(-537783999/625000000 : ℝ)|=(537783999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (778275307/1000000000 : ℝ)*x 0 + (388266497/1250000000 : ℝ)*x 1 + (977572211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778275307/1000000000 : ℝ)^73 ≤ (4533714640807/6250000000000 : ℝ)^57 := by
    have hnat : (778275307 : ℕ)^73*6250000000000^57 ≤ 4533714640807^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778275307 1000000000 4533714640807 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388266497/1250000000 : ℝ)^73 ≤ (4474197352233/20000000000000 : ℝ)^57 := by
    have hnat : (388266497 : ℕ)^73*20000000000000^57 ≤ 4474197352233^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388266497 1250000000 4474197352233 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977572211/10000000000 : ℝ)^73 ≤ (5089578971829/100000000000000 : ℝ)^57 := by
    have hnat : (977572211 : ℕ)^73*100000000000000^57 ≤ 5089578971829^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977572211 10000000000 5089578971829 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(778275307/1000000000 : ℝ), (388266497/1250000000 : ℝ), (977572211/10000000000 : ℝ)] ![(4533714640807/6250000000000 : ℝ), (4474197352233/20000000000000 : ℝ), (5089578971829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(778275307/1000000000 : ℝ)|^73 ≤ (4533714640807/6250000000000 : ℝ)^57
        have hw : |(778275307/1000000000 : ℝ)|=(778275307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388266497/1250000000 : ℝ)|^73 ≤ (4474197352233/20000000000000 : ℝ)^57
        have hw : |(388266497/1250000000 : ℝ)|=(388266497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(977572211/10000000000 : ℝ)|^73 ≤ (5089578971829/100000000000000 : ℝ)^57
        have hw : |(977572211/10000000000 : ℝ)|=(977572211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1496997323/2500000000 : ℝ)*x 0 + (569975229/2500000000 : ℝ)*x 1 + (-4216980941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1496997323/2500000000 : ℝ)^73 ≤ (5185174842337/10000000000000 : ℝ)^57 := by
    have hnat : (1496997323 : ℕ)^73*10000000000000^57 ≤ 5185174842337^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496997323 2500000000 5185174842337 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569975229/2500000000 : ℝ)^73 ≤ (3763759536419/25000000000000 : ℝ)^57 := by
    have hnat : (569975229 : ℕ)^73*25000000000000^57 ≤ 3763759536419^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569975229 2500000000 3763759536419 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216980941/10000000000 : ℝ)^73 ≤ (3309321342227/10000000000000 : ℝ)^57 := by
    have hnat : (4216980941 : ℕ)^73*10000000000000^57 ≤ 3309321342227^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216980941 10000000000 3309321342227 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1496997323/2500000000 : ℝ), (569975229/2500000000 : ℝ), (-4216980941/10000000000 : ℝ)] ![(5185174842337/10000000000000 : ℝ), (3763759536419/25000000000000 : ℝ), (3309321342227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1496997323/2500000000 : ℝ)|^73 ≤ (5185174842337/10000000000000 : ℝ)^57
        have hw : |(-1496997323/2500000000 : ℝ)|=(1496997323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569975229/2500000000 : ℝ)|^73 ≤ (3763759536419/25000000000000 : ℝ)^57
        have hw : |(569975229/2500000000 : ℝ)|=(569975229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4216980941/10000000000 : ℝ)|^73 ≤ (3309321342227/10000000000000 : ℝ)^57
        have hw : |(-4216980941/10000000000 : ℝ)|=(4216980941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (411342867/10000000000 : ℝ)*x 0 + (-109777589/2000000000 : ℝ)*x 1 + (-4838810717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411342867/10000000000 : ℝ)^73 ≤ (1679610550747/100000000000000 : ℝ)^57 := by
    have hnat : (411342867 : ℕ)^73*100000000000000^57 ≤ 1679610550747^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411342867 10000000000 1679610550747 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109777589/2000000000 : ℝ)^73 ≤ (2430270156079/100000000000000 : ℝ)^57 := by
    have hnat : (109777589 : ℕ)^73*100000000000000^57 ≤ 2430270156079^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109777589 2000000000 2430270156079 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838810717/5000000000 : ℝ)^73 ≤ (95890119279433/100000000000000 : ℝ)^57 := by
    have hnat : (4838810717 : ℕ)^73*100000000000000^57 ≤ 95890119279433^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838810717 5000000000 95890119279433 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(411342867/10000000000 : ℝ), (-109777589/2000000000 : ℝ), (-4838810717/5000000000 : ℝ)] ![(1679610550747/100000000000000 : ℝ), (2430270156079/100000000000000 : ℝ), (95890119279433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(411342867/10000000000 : ℝ)|^73 ≤ (1679610550747/100000000000000 : ℝ)^57
        have hw : |(411342867/10000000000 : ℝ)|=(411342867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109777589/2000000000 : ℝ)|^73 ≤ (2430270156079/100000000000000 : ℝ)^57
        have hw : |(-109777589/2000000000 : ℝ)|=(109777589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4838810717/5000000000 : ℝ)|^73 ≤ (95890119279433/100000000000000 : ℝ)^57
        have hw : |(-4838810717/5000000000 : ℝ)|=(4838810717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (787246249/1000000000 : ℝ)*x 0 + (2770290719/10000000000 : ℝ)*x 1 + (315771069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787246249/1000000000 : ℝ)^73 ≤ (3680600387667/5000000000000 : ℝ)^57 := by
    have hnat : (787246249 : ℕ)^73*5000000000000^57 ≤ 3680600387667^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787246249 1000000000 3680600387667 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770290719/10000000000 : ℝ)^73 ≤ (9660758779113/50000000000000 : ℝ)^57 := by
    have hnat : (2770290719 : ℕ)^73*50000000000000^57 ≤ 9660758779113^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770290719 10000000000 9660758779113 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315771069/2500000000 : ℝ)^73 ≤ (7066474675871/100000000000000 : ℝ)^57 := by
    have hnat : (315771069 : ℕ)^73*100000000000000^57 ≤ 7066474675871^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315771069 2500000000 7066474675871 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(787246249/1000000000 : ℝ), (2770290719/10000000000 : ℝ), (315771069/2500000000 : ℝ)] ![(3680600387667/5000000000000 : ℝ), (9660758779113/50000000000000 : ℝ), (7066474675871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(787246249/1000000000 : ℝ)|^73 ≤ (3680600387667/5000000000000 : ℝ)^57
        have hw : |(787246249/1000000000 : ℝ)|=(787246249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770290719/10000000000 : ℝ)|^73 ≤ (9660758779113/50000000000000 : ℝ)^57
        have hw : |(2770290719/10000000000 : ℝ)|=(2770290719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315771069/2500000000 : ℝ)|^73 ≤ (7066474675871/100000000000000 : ℝ)^57
        have hw : |(315771069/2500000000 : ℝ)|=(315771069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312058_s0_s0_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1037233683/10000000000 : ℝ)*x 0 + (4784315631/5000000000 : ℝ)*x 1 + (-73/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037233683/10000000000 : ℝ)^73 ≤ (2745373606989/50000000000000 : ℝ)^57 := by
    have hnat : (1037233683 : ℕ)^73*50000000000000^57 ≤ 2745373606989^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037233683 10000000000 2745373606989 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4784315631/5000000000 : ℝ)^73 ≤ (94509252764449/100000000000000 : ℝ)^57 := by
    have hnat : (4784315631 : ℕ)^73*100000000000000^57 ≤ 94509252764449^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784315631 5000000000 94509252764449 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73/5000000000 : ℝ)^73 ≤ (1153/12500000000000 : ℝ)^57 := by
    have hnat : (73 : ℕ)^73*12500000000000^57 ≤ 1153^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73 5000000000 1153 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037233683/10000000000 : ℝ), (4784315631/5000000000 : ℝ), (-73/5000000000 : ℝ)] ![(2745373606989/50000000000000 : ℝ), (94509252764449/100000000000000 : ℝ), (1153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037233683/10000000000 : ℝ)|^73 ≤ (2745373606989/50000000000000 : ℝ)^57
        have hw : |(1037233683/10000000000 : ℝ)|=(1037233683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4784315631/5000000000 : ℝ)|^73 ≤ (94509252764449/100000000000000 : ℝ)^57
        have hw : |(4784315631/5000000000 : ℝ)|=(4784315631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73/5000000000 : ℝ)|^73 ≤ (1153/12500000000000 : ℝ)^57
        have hw : |(-73/5000000000 : ℝ)|=(73/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312058_s0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]]) : (0 : ℝ) ≤ ((43133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79957/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79957/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14341/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14341/20000 : ℝ)*X 1 2) := by
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
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3015618611/10000000000 : ℝ)*X 0 0+(603123891/2000000000 : ℝ)*X 0 1+(-3220185429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((60312417/200000000 : ℝ)*X 1 0+(-1507811183/5000000000 : ℝ)*X 1 1+(-805045837/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1025469579/5000000000 : ℝ)*X 0 0+(423984021/5000000000 : ℝ)*X 0 1+(-8614349169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((9935617/62500000 : ℝ)*X 1 0+(-172279403/1250000000 : ℝ)*X 1 1+(-1722869807/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3282851799/10000000000 : ℝ)*X 2 0+(7083723477/10000000000 : ℝ)*X 2 1+(1870406861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1705224923/10000000000 : ℝ)*X 0 0+(4589990123/5000000000 : ℝ)*X 0 1+(-38009/10000000000 : ℝ)*X 0 2+(1705224923/10000000000 : ℝ)*X 1 0+(4589990123/5000000000 : ℝ)*X 1 1+(-38009/10000000000 : ℝ)*X 1 2+(1705224923/10000000000 : ℝ)*X 2 0+(4589990123/5000000000 : ℝ)*X 2 1+(-38009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1202147041/10000000000 : ℝ)*X 0 0+(1768735813/10000000000 : ℝ)*X 0 1+(-4302272013/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((300536767/2500000000 : ℝ)*X 1 0+(-884367927/5000000000 : ℝ)*X 1 1+(-537783999/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((778275307/1000000000 : ℝ)*X 2 0+(388266497/1250000000 : ℝ)*X 2 1+(977572211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1496997323/2500000000 : ℝ)*X 0 0+(569975229/2500000000 : ℝ)*X 0 1+(-4216980941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((411342867/10000000000 : ℝ)*X 1 0+(-109777589/2000000000 : ℝ)*X 1 1+(-4838810717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((787246249/1000000000 : ℝ)*X 2 0+(2770290719/10000000000 : ℝ)*X 2 1+(315771069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1037233683/10000000000 : ℝ)*X 0 0+(4784315631/5000000000 : ℝ)*X 0 1+(-73/5000000000 : ℝ)*X 0 2+(1037233683/10000000000 : ℝ)*X 1 0+(4784315631/5000000000 : ℝ)*X 1 1+(-73/5000000000 : ℝ)*X 1 2+(1037233683/10000000000 : ℝ)*X 2 0+(4784315631/5000000000 : ℝ)*X 2 1+(-73/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312058_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((43133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3007973295239597926131/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282934453653/1000000000000 : ℝ)*(base5) + (51399504533/50000000000 : ℝ)*(base7) + (41247/1000000000000 : ℝ)*(base44) + (57772477721/125000000000 : ℝ)*(base53) + (729587351559/500000000000 : ℝ)*(major_s0_0) + (1459174661871/1000000000000 : ℝ)*(major_s0_1) + (996994881349/1000000000000 : ℝ)*(major_s0_2) + (485501035629/500000000000 : ℝ)*(sp_s0_7) + (485523455683/500000000000 : ℝ)*(sp_s0_8) + (429040860657/250000000000 : ℝ)*(sp_s0_9) + (1619222852941/1000000000000 : ℝ)*(sp_s0_13) + (47095949/1000000000000 : ℝ)*(sp_s0_14) + (1107297/500000000000 : ℝ)*(sp_s0_15) + (22739133/500000000000 : ℝ)*(sp_s0_27) + (109276591931/125000000000 : ℝ)*(f.failure) + (57329159559/40000000000 : ℝ)*(f.sum) + (166374115702163/2500000000000000000000000000 : ℝ)*base63 + (4709428116737599/10000000000000000000000000000 : ℝ)*base65 + (1012582554430621/10000000000000000000000000000 : ℝ)*base67 + (2401403577553533/5000000000000000000000000000 : ℝ)*base69 + (1836819433253187/10000000000000000000000000000 : ℝ)*base71 + (86760637229691/5000000000000000000000000000 : ℝ)*base72 + (3481699864850793/5000000000000000000000000000 : ℝ)*base75 + (2254447737378897/2500000000000000000000000000 : ℝ)*base77 + (1830559684971239/10000000000000000000000000000 : ℝ)*base79 + (4003/12500000000000000 : ℝ)*base87 + (4003/12500000000000000 : ℝ)*base89 + (16503/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79957/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79957/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3911243530281646034739/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415846073907/200000000000 : ℝ)*(base5) + (210943962031/200000000000 : ℝ)*(base7) + (85385550981/200000000000 : ℝ)*(base59) + (606316910751/500000000000 : ℝ)*(base60) + (855020654989/500000000000 : ℝ)*(major_s0_0) + (855020654989/500000000000 : ℝ)*(major_s0_1) + (855020654989/500000000000 : ℝ)*(major_s0_2) + (359633/250000000000 : ℝ)*(sp_s0_0) + (824101/500000000000 : ℝ)*(sp_s0_1) + (26927887/500000000000 : ℝ)*(sp_s0_8) + (55274381077/31250000000 : ℝ)*(sp_s0_14) + (1768726129019/1000000000000 : ℝ)*(sp_s0_15) + (1923999070241/500000000000 : ℝ)*(sp_s0_16) + (433189/31250000000 : ℝ)*(sp_s0_23) + (51225527969/50000000000 : ℝ)*(f.failure) + (353756326599/200000000000 : ℝ)*(f.sum) + (456524981/2500000000000000000000 : ℝ)*base62 + (1989359074238761/5000000000000000000000000000 : ℝ)*base64 + (3294416831761239/5000000000000000000000000000 : ℝ)*base67 + (923888083178587/2500000000000000000000000000 : ℝ)*base68 + (1006378630881587/5000000000000000000000000000 : ℝ)*base70 + (606154239238761/5000000000000000000000000000 : ℝ)*base72 + (571248549821413/2500000000000000000000000000 : ℝ)*base74 + (348654970821413/2500000000000000000000000000 : ℝ)*base76 + (90695165738761/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (303/5000000000000000 : ℝ)*base86 + (303/5000000000000000 : ℝ)*base88 + (303/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14341/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14341/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40499930385963925135527/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11863478879/125000000000 : ℝ)*(base5) + (124304169567/250000000000 : ℝ)*(base7) + (287587733141/1000000000000 : ℝ)*(base33) + (91586851119/100000000000 : ℝ)*(base44) + (1055941/1000000000000 : ℝ)*(base50) + (1355492355143/1000000000000 : ℝ)*(major_s0_0) + (363605788547/500000000000 : ℝ)*(major_s0_1) + (410770022071/250000000000 : ℝ)*(major_s0_2) + (22823863/500000000000 : ℝ)*(sp_s0_8) + (93904863/1000000000000 : ℝ)*(sp_s0_13) + (401256680247/200000000000 : ℝ)*(sp_s0_21) + (401390754589/500000000000 : ℝ)*(sp_s0_22) + (1813603499127/1000000000000 : ℝ)*(sp_s0_23) + (235369775561/500000000000 : ℝ)*(sp_s0_27) + (984393119939/1000000000000 : ℝ)*(f.failure) + (401256680247/200000000000 : ℝ)*(f.sum) + (45862075327623/500000000000000000000000000 : ℝ)*base63 + (394960445459179/2500000000000000000000000000 : ℝ)*base64 + (154823403017703/5000000000000000000000000000 : ℝ)*base66 + (503714697472393/1250000000000000000000000000 : ℝ)*base68 + (1203302604029989/5000000000000000000000000000 : ℝ)*base70 + (1762341243526107/10000000000000000000000000000 : ℝ)*base72 + (1475912421167099/2500000000000000000000000000 : ℝ)*base74 + (1645484547611631/5000000000000000000000000000 : ℝ)*base76 + (2119244477561513/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (21693/100000000000000000 : ℝ)*base86 + (21693/100000000000000000 : ℝ)*base88 + (21693/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]]) : (0 : ℝ) ≤ ((43133/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43133/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79957/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79957/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14341/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14341/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312058_s0 p hpa hpb X hX

#print axioms solution

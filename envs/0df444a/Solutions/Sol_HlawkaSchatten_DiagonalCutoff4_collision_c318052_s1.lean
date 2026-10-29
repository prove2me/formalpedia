-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318052_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:22:49.142885+00:00
-- url     : https://prove2.me/submissions/97858bfa-7d34-4a6b-9b37-382110a30762

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
theorem collision_support_c318052_s1_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-382905769/2000000000 : ℝ)*x 0 + (709050219/2000000000 : ℝ)*x 1 + (-415223423/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382905769/2000000000 : ℝ)^5 ≤ (1583023658413/12500000000000 : ℝ)^4 := by
    have hnat : (382905769 : ℕ)^5*12500000000000^4 ≤ 1583023658413^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382905769 2000000000 1583023658413 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709050219/2000000000 : ℝ)^5 ≤ (136781938431/500000000000 : ℝ)^4 := by
    have hnat : (709050219 : ℕ)^5*500000000000^4 ≤ 136781938431^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709050219 2000000000 136781938431 500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415223423/625000000 : ℝ)^5 ≤ (59979423027741/100000000000000 : ℝ)^4 := by
    have hnat : (415223423 : ℕ)^5*100000000000000^4 ≤ 59979423027741^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415223423 625000000 59979423027741 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382905769/2000000000 : ℝ), (709050219/2000000000 : ℝ), (-415223423/625000000 : ℝ)] ![(1583023658413/12500000000000 : ℝ), (136781938431/500000000000 : ℝ), (59979423027741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382905769/2000000000 : ℝ)|^5 ≤ (1583023658413/12500000000000 : ℝ)^4
        have hw : |(-382905769/2000000000 : ℝ)|=(382905769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709050219/2000000000 : ℝ)|^5 ≤ (136781938431/500000000000 : ℝ)^4
        have hw : |(709050219/2000000000 : ℝ)|=(709050219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415223423/625000000 : ℝ)|^5 ≤ (59979423027741/100000000000000 : ℝ)^4
        have hw : |(-415223423/625000000 : ℝ)|=(415223423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (595674791/1250000000 : ℝ)*x 0 + (2839163957/5000000000 : ℝ)*x 1 + (172470429/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (595674791/1250000000 : ℝ)^5 ≤ (39593510554313/100000000000000 : ℝ)^4 := by
    have hnat : (595674791 : ℕ)^5*100000000000000^4 ≤ 39593510554313^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595674791 1250000000 39593510554313 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2839163957/5000000000 : ℝ)^5 ≤ (12322975769803/25000000000000 : ℝ)^4 := by
    have hnat : (2839163957 : ℕ)^5*25000000000000^4 ≤ 12322975769803^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839163957 5000000000 12322975769803 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172470429/1000000000 : ℝ)^5 ≤ (444583454277/4000000000000 : ℝ)^4 := by
    have hnat : (172470429 : ℕ)^5*4000000000000^4 ≤ 444583454277^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172470429 1000000000 444583454277 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(595674791/1250000000 : ℝ), (2839163957/5000000000 : ℝ), (172470429/1000000000 : ℝ)] ![(39593510554313/100000000000000 : ℝ), (12322975769803/25000000000000 : ℝ), (444583454277/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(595674791/1250000000 : ℝ)|^5 ≤ (39593510554313/100000000000000 : ℝ)^4
        have hw : |(595674791/1250000000 : ℝ)|=(595674791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2839163957/5000000000 : ℝ)|^5 ≤ (12322975769803/25000000000000 : ℝ)^4
        have hw : |(2839163957/5000000000 : ℝ)|=(2839163957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172470429/1000000000 : ℝ)|^5 ≤ (444583454277/4000000000000 : ℝ)^4
        have hw : |(172470429/1000000000 : ℝ)|=(172470429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1307512153/2000000000 : ℝ)*x 0 + (4063239121/10000000000 : ℝ)*x 1 + (-1427421807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307512153/2000000000 : ℝ)^5 ≤ (58785426466587/100000000000000 : ℝ)^4 := by
    have hnat : (1307512153 : ℕ)^5*100000000000000^4 ≤ 58785426466587^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307512153 2000000000 58785426466587 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4063239121/10000000000 : ℝ)^5 ≤ (32440719404831/100000000000000 : ℝ)^4 := by
    have hnat : (4063239121 : ℕ)^5*100000000000000^4 ≤ 32440719404831^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4063239121 10000000000 32440719404831 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1427421807/10000000000 : ℝ)^5 ≤ (1096731764581/12500000000000 : ℝ)^4 := by
    have hnat : (1427421807 : ℕ)^5*12500000000000^4 ≤ 1096731764581^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427421807 10000000000 1096731764581 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307512153/2000000000 : ℝ), (4063239121/10000000000 : ℝ), (-1427421807/10000000000 : ℝ)] ![(58785426466587/100000000000000 : ℝ), (32440719404831/100000000000000 : ℝ), (1096731764581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307512153/2000000000 : ℝ)|^5 ≤ (58785426466587/100000000000000 : ℝ)^4
        have hw : |(1307512153/2000000000 : ℝ)|=(1307512153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4063239121/10000000000 : ℝ)|^5 ≤ (32440719404831/100000000000000 : ℝ)^4
        have hw : |(4063239121/10000000000 : ℝ)|=(4063239121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1427421807/10000000000 : ℝ)|^5 ≤ (1096731764581/12500000000000 : ℝ)^4
        have hw : |(-1427421807/10000000000 : ℝ)|=(1427421807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-914014993/5000000000 : ℝ)*x 0 + (316783837/1000000000 : ℝ)*x 1 + (-7022091043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914014993/5000000000 : ℝ)^5 ≤ (239061224617/2000000000000 : ℝ)^4 := by
    have hnat : (914014993 : ℕ)^5*2000000000000^4 ≤ 239061224617^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914014993 5000000000 239061224617 2000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316783837/1000000000 : ℝ)^5 ≤ (11882936405059/50000000000000 : ℝ)^4 := by
    have hnat : (316783837 : ℕ)^5*50000000000000^4 ≤ 11882936405059^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316783837 1000000000 11882936405059 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7022091043/10000000000 : ℝ)^5 ≤ (12856213188921/20000000000000 : ℝ)^4 := by
    have hnat : (7022091043 : ℕ)^5*20000000000000^4 ≤ 12856213188921^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7022091043 10000000000 12856213188921 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914014993/5000000000 : ℝ), (316783837/1000000000 : ℝ), (-7022091043/10000000000 : ℝ)] ![(239061224617/2000000000000 : ℝ), (11882936405059/50000000000000 : ℝ), (12856213188921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914014993/5000000000 : ℝ)|^5 ≤ (239061224617/2000000000000 : ℝ)^4
        have hw : |(-914014993/5000000000 : ℝ)|=(914014993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316783837/1000000000 : ℝ)|^5 ≤ (11882936405059/50000000000000 : ℝ)^4
        have hw : |(316783837/1000000000 : ℝ)|=(316783837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7022091043/10000000000 : ℝ)|^5 ≤ (12856213188921/20000000000000 : ℝ)^4
        have hw : |(-7022091043/10000000000 : ℝ)|=(7022091043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (860806/1953125 : ℝ)*x 0 + (-491419269/2000000000 : ℝ)*x 1 + (-2723300911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860806/1953125 : ℝ)^5 ≤ (8977575511403/25000000000000 : ℝ)^4 := by
    have hnat : (860806 : ℕ)^5*25000000000000^4 ≤ 8977575511403^4*1953125^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860806 1953125 8977575511403 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491419269/2000000000 : ℝ)^5 ≤ (864963411077/5000000000000 : ℝ)^4 := by
    have hnat : (491419269 : ℕ)^5*5000000000000^4 ≤ 864963411077^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491419269 2000000000 864963411077 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723300911/5000000000 : ℝ)^5 ≤ (46790429721407/100000000000000 : ℝ)^4 := by
    have hnat : (2723300911 : ℕ)^5*100000000000000^4 ≤ 46790429721407^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723300911 5000000000 46790429721407 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860806/1953125 : ℝ), (-491419269/2000000000 : ℝ), (-2723300911/5000000000 : ℝ)] ![(8977575511403/25000000000000 : ℝ), (864963411077/5000000000000 : ℝ), (46790429721407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860806/1953125 : ℝ)|^5 ≤ (8977575511403/25000000000000 : ℝ)^4
        have hw : |(860806/1953125 : ℝ)|=(860806/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491419269/2000000000 : ℝ)|^5 ≤ (864963411077/5000000000000 : ℝ)^4
        have hw : |(-491419269/2000000000 : ℝ)|=(491419269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2723300911/5000000000 : ℝ)|^5 ≤ (46790429721407/100000000000000 : ℝ)^4
        have hw : |(-2723300911/5000000000 : ℝ)|=(2723300911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4582538779/10000000000 : ℝ)*x 0 + (6339097747/10000000000 : ℝ)*x 1 + (507791819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4582538779/10000000000 : ℝ)^5 ≤ (37703588425691/100000000000000 : ℝ)^4 := by
    have hnat : (4582538779 : ℕ)^5*100000000000000^4 ≤ 37703588425691^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582538779 10000000000 37703588425691 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6339097747/10000000000 : ℝ)^5 ≤ (56563244208421/100000000000000 : ℝ)^4 := by
    have hnat : (6339097747 : ℕ)^5*100000000000000^4 ≤ 56563244208421^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6339097747 10000000000 56563244208421 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507791819/5000000000 : ℝ)^5 ≤ (5733167353733/100000000000000 : ℝ)^4 := by
    have hnat : (507791819 : ℕ)^5*100000000000000^4 ≤ 5733167353733^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507791819 5000000000 5733167353733 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4582538779/10000000000 : ℝ), (6339097747/10000000000 : ℝ), (507791819/5000000000 : ℝ)] ![(37703588425691/100000000000000 : ℝ), (56563244208421/100000000000000 : ℝ), (5733167353733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4582538779/10000000000 : ℝ)|^5 ≤ (37703588425691/100000000000000 : ℝ)^4
        have hw : |(4582538779/10000000000 : ℝ)|=(4582538779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6339097747/10000000000 : ℝ)|^5 ≤ (56563244208421/100000000000000 : ℝ)^4
        have hw : |(6339097747/10000000000 : ℝ)|=(6339097747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507791819/5000000000 : ℝ)|^5 ≤ (5733167353733/100000000000000 : ℝ)^4
        have hw : |(507791819/5000000000 : ℝ)|=(507791819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6292110521/10000000000 : ℝ)*x 0 + (4796295397/10000000000 : ℝ)*x 1 + (-153682411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6292110521/10000000000 : ℝ)^5 ≤ (2241586071257/4000000000000 : ℝ)^4 := by
    have hnat : (6292110521 : ℕ)^5*4000000000000^4 ≤ 2241586071257^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6292110521 10000000000 2241586071257 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4796295397/10000000000 : ℝ)^5 ≤ (39914657179291/100000000000000 : ℝ)^4 := by
    have hnat : (4796295397 : ℕ)^5*100000000000000^4 ≤ 39914657179291^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796295397 10000000000 39914657179291 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153682411/2000000000 : ℝ)^5 ≤ (2022845512001/50000000000000 : ℝ)^4 := by
    have hnat : (153682411 : ℕ)^5*50000000000000^4 ≤ 2022845512001^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153682411 2000000000 2022845512001 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6292110521/10000000000 : ℝ), (4796295397/10000000000 : ℝ), (-153682411/2000000000 : ℝ)] ![(2241586071257/4000000000000 : ℝ), (39914657179291/100000000000000 : ℝ), (2022845512001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6292110521/10000000000 : ℝ)|^5 ≤ (2241586071257/4000000000000 : ℝ)^4
        have hw : |(6292110521/10000000000 : ℝ)|=(6292110521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4796295397/10000000000 : ℝ)|^5 ≤ (39914657179291/100000000000000 : ℝ)^4
        have hw : |(4796295397/10000000000 : ℝ)|=(4796295397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153682411/2000000000 : ℝ)|^5 ≤ (2022845512001/50000000000000 : ℝ)^4
        have hw : |(-153682411/2000000000 : ℝ)|=(153682411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1313772583/10000000000 : ℝ)*x 0 + (3541637323/10000000000 : ℝ)*x 1 + (-7064695427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313772583/10000000000 : ℝ)^5 ≤ (1581904416783/20000000000000 : ℝ)^4 := by
    have hnat : (1313772583 : ℕ)^5*20000000000000^4 ≤ 1581904416783^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313772583 10000000000 1581904416783 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3541637323/10000000000 : ℝ)^5 ≤ (5464307146027/20000000000000 : ℝ)^4 := by
    have hnat : (3541637323 : ℕ)^5*20000000000000^4 ≤ 5464307146027^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3541637323 10000000000 5464307146027 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7064695427/10000000000 : ℝ)^5 ≤ (64768942179127/100000000000000 : ℝ)^4 := by
    have hnat : (7064695427 : ℕ)^5*100000000000000^4 ≤ 64768942179127^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7064695427 10000000000 64768942179127 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1313772583/10000000000 : ℝ), (3541637323/10000000000 : ℝ), (-7064695427/10000000000 : ℝ)] ![(1581904416783/20000000000000 : ℝ), (5464307146027/20000000000000 : ℝ), (64768942179127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1313772583/10000000000 : ℝ)|^5 ≤ (1581904416783/20000000000000 : ℝ)^4
        have hw : |(-1313772583/10000000000 : ℝ)|=(1313772583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3541637323/10000000000 : ℝ)|^5 ≤ (5464307146027/20000000000000 : ℝ)^4
        have hw : |(3541637323/10000000000 : ℝ)|=(3541637323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7064695427/10000000000 : ℝ)|^5 ≤ (64768942179127/100000000000000 : ℝ)^4
        have hw : |(-7064695427/10000000000 : ℝ)|=(7064695427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4312893007/10000000000 : ℝ)*x 0 + (-2681786911/10000000000 : ℝ)*x 1 + (-5349505327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312893007/10000000000 : ℝ)^5 ≤ (34951100554197/100000000000000 : ℝ)^4 := by
    have hnat : (4312893007 : ℕ)^5*100000000000000^4 ≤ 34951100554197^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312893007 10000000000 34951100554197 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2681786911/10000000000 : ℝ)^5 ≤ (1206175077981/6250000000000 : ℝ)^4 := by
    have hnat : (2681786911 : ℕ)^5*6250000000000^4 ≤ 1206175077981^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681786911 10000000000 1206175077981 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5349505327/10000000000 : ℝ)^5 ≤ (22875049090067/50000000000000 : ℝ)^4 := by
    have hnat : (5349505327 : ℕ)^5*50000000000000^4 ≤ 22875049090067^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349505327 10000000000 22875049090067 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312893007/10000000000 : ℝ), (-2681786911/10000000000 : ℝ), (-5349505327/10000000000 : ℝ)] ![(34951100554197/100000000000000 : ℝ), (1206175077981/6250000000000 : ℝ), (22875049090067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312893007/10000000000 : ℝ)|^5 ≤ (34951100554197/100000000000000 : ℝ)^4
        have hw : |(4312893007/10000000000 : ℝ)|=(4312893007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2681786911/10000000000 : ℝ)|^5 ≤ (1206175077981/6250000000000 : ℝ)^4
        have hw : |(-2681786911/10000000000 : ℝ)|=(2681786911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5349505327/10000000000 : ℝ)|^5 ≤ (22875049090067/50000000000000 : ℝ)^4
        have hw : |(-5349505327/10000000000 : ℝ)|=(5349505327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5387582207/10000000000 : ℝ)*x 0 + (110439321/200000000 : ℝ)*x 1 + (21739717/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387582207/10000000000 : ℝ)^5 ≤ (23078755796217/50000000000000 : ℝ)^4 := by
    have hnat : (5387582207 : ℕ)^5*50000000000000^4 ≤ 23078755796217^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387582207 10000000000 23078755796217 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110439321/200000000 : ℝ)^5 ≤ (11900279834183/25000000000000 : ℝ)^4 := by
    have hnat : (110439321 : ℕ)^5*25000000000000^4 ≤ 11900279834183^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110439321 200000000 11900279834183 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21739717/200000000 : ℝ)^5 ≤ (6241369053801/100000000000000 : ℝ)^4 := by
    have hnat : (21739717 : ℕ)^5*100000000000000^4 ≤ 6241369053801^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21739717 200000000 6241369053801 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387582207/10000000000 : ℝ), (110439321/200000000 : ℝ), (21739717/200000000 : ℝ)] ![(23078755796217/50000000000000 : ℝ), (11900279834183/25000000000000 : ℝ), (6241369053801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387582207/10000000000 : ℝ)|^5 ≤ (23078755796217/50000000000000 : ℝ)^4
        have hw : |(5387582207/10000000000 : ℝ)|=(5387582207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110439321/200000000 : ℝ)|^5 ≤ (11900279834183/25000000000000 : ℝ)^4
        have hw : |(110439321/200000000 : ℝ)|=(110439321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21739717/200000000 : ℝ)|^5 ≤ (6241369053801/100000000000000 : ℝ)^4
        have hw : |(21739717/200000000 : ℝ)|=(21739717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7312749807/10000000000 : ℝ)*x 0 + (3675971397/10000000000 : ℝ)*x 1 + (-180901551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7312749807/10000000000 : ℝ)^5 ≤ (422650036829/625000000000 : ℝ)^4 := by
    have hnat : (7312749807 : ℕ)^5*625000000000^4 ≤ 422650036829^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7312749807 10000000000 422650036829 625000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3675971397/10000000000 : ℝ)^5 ≤ (1431150012339/5000000000000 : ℝ)^4 := by
    have hnat : (3675971397 : ℕ)^5*5000000000000^4 ≤ 1431150012339^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3675971397 10000000000 1431150012339 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180901551/2500000000 : ℝ)^5 ≤ (938248461241/25000000000000 : ℝ)^4 := by
    have hnat : (180901551 : ℕ)^5*25000000000000^4 ≤ 938248461241^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180901551 2500000000 938248461241 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7312749807/10000000000 : ℝ), (3675971397/10000000000 : ℝ), (-180901551/2500000000 : ℝ)] ![(422650036829/625000000000 : ℝ), (1431150012339/5000000000000 : ℝ), (938248461241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7312749807/10000000000 : ℝ)|^5 ≤ (422650036829/625000000000 : ℝ)^4
        have hw : |(7312749807/10000000000 : ℝ)|=(7312749807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3675971397/10000000000 : ℝ)|^5 ≤ (1431150012339/5000000000000 : ℝ)^4
        have hw : |(3675971397/10000000000 : ℝ)|=(3675971397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180901551/2500000000 : ℝ)|^5 ≤ (938248461241/25000000000000 : ℝ)^4
        have hw : |(-180901551/2500000000 : ℝ)|=(180901551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-272504221/2500000000 : ℝ)*x 0 + (499771071/1250000000 : ℝ)*x 1 + (-681711731/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272504221/2500000000 : ℝ)^5 ≤ (6263131516483/100000000000000 : ℝ)^4 := by
    have hnat : (272504221 : ℕ)^5*100000000000000^4 ≤ 6263131516483^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272504221 2500000000 6263131516483 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499771071/1250000000 : ℝ)^5 ≤ (31792624139509/100000000000000 : ℝ)^4 := by
    have hnat : (499771071 : ℕ)^5*100000000000000^4 ≤ 31792624139509^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499771071 1250000000 31792624139509 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681711731/1000000000 : ℝ)^5 ≤ (61944244339437/100000000000000 : ℝ)^4 := by
    have hnat : (681711731 : ℕ)^5*100000000000000^4 ≤ 61944244339437^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681711731 1000000000 61944244339437 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272504221/2500000000 : ℝ), (499771071/1250000000 : ℝ), (-681711731/1000000000 : ℝ)] ![(6263131516483/100000000000000 : ℝ), (31792624139509/100000000000000 : ℝ), (61944244339437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272504221/2500000000 : ℝ)|^5 ≤ (6263131516483/100000000000000 : ℝ)^4
        have hw : |(-272504221/2500000000 : ℝ)|=(272504221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499771071/1250000000 : ℝ)|^5 ≤ (31792624139509/100000000000000 : ℝ)^4
        have hw : |(499771071/1250000000 : ℝ)|=(499771071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-681711731/1000000000 : ℝ)|^5 ≤ (61944244339437/100000000000000 : ℝ)^4
        have hw : |(-681711731/1000000000 : ℝ)|=(681711731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1087225247/2000000000 : ℝ)*x 0 + (-509199671/2000000000 : ℝ)*x 1 + (-4341079963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087225247/2000000000 : ℝ)^5 ≤ (23338982629219/50000000000000 : ℝ)^4 := by
    have hnat : (1087225247 : ℕ)^5*50000000000000^4 ≤ 23338982629219^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087225247 2000000000 23338982629219 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509199671/2000000000 : ℝ)^5 ≤ (9042586101927/50000000000000 : ℝ)^4 := by
    have hnat : (509199671 : ℕ)^5*50000000000000^4 ≤ 9042586101927^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509199671 2000000000 9042586101927 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4341079963/10000000000 : ℝ)^5 ≤ (17618431262123/50000000000000 : ℝ)^4 := by
    have hnat : (4341079963 : ℕ)^5*50000000000000^4 ≤ 17618431262123^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341079963 10000000000 17618431262123 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087225247/2000000000 : ℝ), (-509199671/2000000000 : ℝ), (-4341079963/10000000000 : ℝ)] ![(23338982629219/50000000000000 : ℝ), (9042586101927/50000000000000 : ℝ), (17618431262123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087225247/2000000000 : ℝ)|^5 ≤ (23338982629219/50000000000000 : ℝ)^4
        have hw : |(1087225247/2000000000 : ℝ)|=(1087225247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509199671/2000000000 : ℝ)|^5 ≤ (9042586101927/50000000000000 : ℝ)^4
        have hw : |(-509199671/2000000000 : ℝ)|=(509199671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4341079963/10000000000 : ℝ)|^5 ≤ (17618431262123/50000000000000 : ℝ)^4
        have hw : |(-4341079963/10000000000 : ℝ)|=(4341079963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4395197209/10000000000 : ℝ)*x 0 + (751459249/1250000000 : ℝ)*x 1 + (218120513/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4395197209/10000000000 : ℝ)^5 ≤ (2236675472161/6250000000000 : ℝ)^4 := by
    have hnat : (4395197209 : ℕ)^5*6250000000000^4 ≤ 2236675472161^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395197209 10000000000 2236675472161 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751459249/1250000000 : ℝ)^5 ≤ (26467582822441/50000000000000 : ℝ)^4 := by
    have hnat : (751459249 : ℕ)^5*50000000000000^4 ≤ 26467582822441^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751459249 1250000000 26467582822441 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218120513/1250000000 : ℝ)^5 ≤ (704876674219/6250000000000 : ℝ)^4 := by
    have hnat : (218120513 : ℕ)^5*6250000000000^4 ≤ 704876674219^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218120513 1250000000 704876674219 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4395197209/10000000000 : ℝ), (751459249/1250000000 : ℝ), (218120513/1250000000 : ℝ)] ![(2236675472161/6250000000000 : ℝ), (26467582822441/50000000000000 : ℝ), (704876674219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4395197209/10000000000 : ℝ)|^5 ≤ (2236675472161/6250000000000 : ℝ)^4
        have hw : |(4395197209/10000000000 : ℝ)|=(4395197209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(751459249/1250000000 : ℝ)|^5 ≤ (26467582822441/50000000000000 : ℝ)^4
        have hw : |(751459249/1250000000 : ℝ)|=(751459249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218120513/1250000000 : ℝ)|^5 ≤ (704876674219/6250000000000 : ℝ)^4
        have hw : |(218120513/1250000000 : ℝ)|=(218120513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318052_s1_s1_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3779454489/5000000000 : ℝ)*x 0 + (3228299469/10000000000 : ℝ)*x 1 + (-937054587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3779454489/5000000000 : ℝ)^5 ≤ (70481298182349/100000000000000 : ℝ)^4 := by
    have hnat : (3779454489 : ℕ)^5*100000000000000^4 ≤ 70481298182349^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3779454489 5000000000 70481298182349 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3228299469/10000000000 : ℝ)^5 ≤ (760444091799/3125000000000 : ℝ)^4 := by
    have hnat : (3228299469 : ℕ)^5*3125000000000^4 ≤ 760444091799^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3228299469 10000000000 760444091799 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937054587/10000000000 : ℝ)^5 ≤ (518449086587/10000000000000 : ℝ)^4 := by
    have hnat : (937054587 : ℕ)^5*10000000000000^4 ≤ 518449086587^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937054587 10000000000 518449086587 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3779454489/5000000000 : ℝ), (3228299469/10000000000 : ℝ), (-937054587/10000000000 : ℝ)] ![(70481298182349/100000000000000 : ℝ), (760444091799/3125000000000 : ℝ), (518449086587/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3779454489/5000000000 : ℝ)|^5 ≤ (70481298182349/100000000000000 : ℝ)^4
        have hw : |(3779454489/5000000000 : ℝ)|=(3779454489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3228299469/10000000000 : ℝ)|^5 ≤ (760444091799/3125000000000 : ℝ)^4
        have hw : |(3228299469/10000000000 : ℝ)|=(3228299469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937054587/10000000000 : ℝ)|^5 ≤ (518449086587/10000000000000 : ℝ)^4
        have hw : |(-937054587/10000000000 : ℝ)|=(937054587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318052_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((17657/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17657/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71653/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71653/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29861/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29861/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15817/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15817/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1783/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1783/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5319/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5319/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (17657/25000 : ℝ) ^ (39/8 : ℝ) ≤ (18355339777047515503/100000000000000000000 : ℝ) := by
    have hpowers : (17657/25000 : ℝ)^39 ≤ (18355339777047515503/100000000000000000000 : ℝ)^8 := by
      have hnat : (17657 : ℕ)^39*100000000000000000000^8 ≤ 18355339777047515503^8*25000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17657 25000 18355339777047515503 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17657/25000 : ℝ)) (X := (18355339777047515503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (118355339777047515503/100000000000000000000 : ℝ) ≤ (517586449595061/500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (118355339777047515503/100000000000000000000 : ℝ)^8 ≤ (517586449595061/500000000000000 : ℝ)^39 := by
      have hnat : (118355339777047515503 : ℕ)^8*500000000000000^39 ≤ 517586449595061^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118355339777047515503 100000000000000000000 517586449595061 500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (517586449595061/500000000000000 : ℝ)) (X := (118355339777047515503/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (68355339777047515503/50000000000000000000 : ℝ) ≤ (5331223816325561/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (68355339777047515503/50000000000000000000 : ℝ)^8 ≤ (5331223816325561/5000000000000000 : ℝ)^39 := by
      have hnat : (68355339777047515503 : ℕ)^8*5000000000000000^39 ≤ 5331223816325561^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68355339777047515503 50000000000000000000 5331223816325561 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5331223816325561/5000000000000000 : ℝ)) (X := (68355339777047515503/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(17586449595061/353140000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(155359320374951/3531400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (17657/25000 : ℝ)) (alpha := (17586449595061/353140000000000 : ℝ)) (beta := (155359320374951/3531400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17657/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(17586449595061/353140000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(155359320374951/3531400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (71653/100000 : ℝ) ^ (39/8 : ℝ) ≤ (19690991942113943963/100000000000000000000 : ℝ) := by
    have hpowers : (71653/100000 : ℝ)^39 ≤ (19690991942113943963/100000000000000000000 : ℝ)^8 := by
      have hnat : (71653 : ℕ)^39*100000000000000000000^8 ≤ 19690991942113943963^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71653 100000 19690991942113943963 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71653/100000 : ℝ)) (X := (19690991942113943963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (119690991942113943963/100000000000000000000 : ℝ) ≤ (2593896344558697/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (119690991942113943963/100000000000000000000 : ℝ)^8 ≤ (2593896344558697/2500000000000000 : ℝ)^39 := by
      have hnat : (119690991942113943963 : ℕ)^8*2500000000000000^39 ≤ 2593896344558697^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119690991942113943963 100000000000000000000 2593896344558697 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2593896344558697/2500000000000000 : ℝ)) (X := (119690991942113943963/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (69690991942113943963/50000000000000000000 : ℝ) ≤ (10704856492367509/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (69690991942113943963/50000000000000000000 : ℝ)^8 ≤ (10704856492367509/10000000000000000 : ℝ)^39 := by
      have hnat : (69690991942113943963 : ℕ)^8*10000000000000000^39 ≤ 10704856492367509^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69690991942113943963 50000000000000000000 10704856492367509 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10704856492367509/10000000000000000 : ℝ)) (X := (69690991942113943963/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(93896344558697/1791325000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(329271114132721/7165300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (71653/100000 : ℝ)) (alpha := (93896344558697/1791325000000000 : ℝ)) (beta := (329271114132721/7165300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (71653/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(93896344558697/1791325000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(329271114132721/7165300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (29861/50000 : ℝ) ^ (39/8 : ℝ) ≤ (8103169490146936229/100000000000000000000 : ℝ) := by
    have hpowers : (29861/50000 : ℝ)^39 ≤ (8103169490146936229/100000000000000000000 : ℝ)^8 := by
      have hnat : (29861 : ℕ)^39*100000000000000000000^8 ≤ 8103169490146936229^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29861 50000 8103169490146936229 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29861/50000 : ℝ)) (X := (8103169490146936229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (108103169490146936229/100000000000000000000 : ℝ) ≤ (10161111473243499/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (108103169490146936229/100000000000000000000 : ℝ)^8 ≤ (10161111473243499/10000000000000000 : ℝ)^39 := by
      have hnat : (108103169490146936229 : ℕ)^8*10000000000000000^39 ≤ 10161111473243499^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108103169490146936229 100000000000000000000 10161111473243499 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10161111473243499/10000000000000000 : ℝ)) (X := (108103169490146936229/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (58103169490146936229/50000000000000000000 : ℝ) ≤ (10312892143213763/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (58103169490146936229/50000000000000000000 : ℝ)^8 ≤ (10312892143213763/10000000000000000 : ℝ)^39 := by
      have hnat : (58103169490146936229 : ℕ)^8*10000000000000000^39 ≤ 10312892143213763^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58103169490146936229 50000000000000000000 10312892143213763 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10312892143213763/10000000000000000 : ℝ)) (X := (58103169490146936229/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(161111473243499/5972200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(18972583746283/746525000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (29861/50000 : ℝ)) (alpha := (161111473243499/5972200000000000 : ℝ)) (beta := (18972583746283/746525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29861/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(161111473243499/5972200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(18972583746283/746525000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-382905769/2000000000 : ℝ)*X 0 0+(709050219/2000000000 : ℝ)*X 0 1+(-415223423/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((595674791/1250000000 : ℝ)*X 2 0+(2839163957/5000000000 : ℝ)*X 2 1+(172470429/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1307512153/2000000000 : ℝ)*X 0 0+(4063239121/10000000000 : ℝ)*X 0 1+(-1427421807/10000000000 : ℝ)*X 0 2+(1307512153/2000000000 : ℝ)*X 1 0+(4063239121/10000000000 : ℝ)*X 1 1+(-1427421807/10000000000 : ℝ)*X 1 2+(1307512153/2000000000 : ℝ)*X 2 0+(4063239121/10000000000 : ℝ)*X 2 1+(-1427421807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-914014993/5000000000 : ℝ)*X 0 0+(316783837/1000000000 : ℝ)*X 0 1+(-7022091043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((860806/1953125 : ℝ)*X 1 0+(-491419269/2000000000 : ℝ)*X 1 1+(-2723300911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4582538779/10000000000 : ℝ)*X 2 0+(6339097747/10000000000 : ℝ)*X 2 1+(507791819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6292110521/10000000000 : ℝ)*X 0 0+(4796295397/10000000000 : ℝ)*X 0 1+(-153682411/2000000000 : ℝ)*X 0 2+(6292110521/10000000000 : ℝ)*X 1 0+(4796295397/10000000000 : ℝ)*X 1 1+(-153682411/2000000000 : ℝ)*X 1 2+(6292110521/10000000000 : ℝ)*X 2 0+(4796295397/10000000000 : ℝ)*X 2 1+(-153682411/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1313772583/10000000000 : ℝ)*X 0 0+(3541637323/10000000000 : ℝ)*X 0 1+(-7064695427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4312893007/10000000000 : ℝ)*X 1 0+(-2681786911/10000000000 : ℝ)*X 1 1+(-5349505327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5387582207/10000000000 : ℝ)*X 2 0+(110439321/200000000 : ℝ)*X 2 1+(21739717/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7312749807/10000000000 : ℝ)*X 0 0+(3675971397/10000000000 : ℝ)*X 0 1+(-180901551/2500000000 : ℝ)*X 0 2+(7312749807/10000000000 : ℝ)*X 1 0+(3675971397/10000000000 : ℝ)*X 1 1+(-180901551/2500000000 : ℝ)*X 1 2+(7312749807/10000000000 : ℝ)*X 2 0+(3675971397/10000000000 : ℝ)*X 2 1+(-180901551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-272504221/2500000000 : ℝ)*X 0 0+(499771071/1250000000 : ℝ)*X 0 1+(-681711731/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1087225247/2000000000 : ℝ)*X 1 0+(-509199671/2000000000 : ℝ)*X 1 1+(-4341079963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4395197209/10000000000 : ℝ)*X 2 0+(751459249/1250000000 : ℝ)*X 2 1+(218120513/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3779454489/5000000000 : ℝ)*X 0 0+(3228299469/10000000000 : ℝ)*X 0 1+(-937054587/10000000000 : ℝ)*X 0 2+(3779454489/5000000000 : ℝ)*X 1 0+(3228299469/10000000000 : ℝ)*X 1 1+(-937054587/10000000000 : ℝ)*X 1 2+(3779454489/5000000000 : ℝ)*X 2 0+(3228299469/10000000000 : ℝ)*X 2 1+(-937054587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318052_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((15817/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15817/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14520366575271567736566665731563/1888972551204050000000000000000000000 : ℝ) := by norm_num
    linear_combination (115251164179/125000000000 : ℝ)*(base39) + (118001521943/1000000000000 : ℝ)*(base49) + (235797073067/125000000000 : ℝ)*(base59) + (7492320432513/1000000000000 : ℝ)*(major_s1_0) + (7492320432513/1000000000000 : ℝ)*(major_s1_1) + (7492320432513/1000000000000 : ℝ)*(major_s1_2) + (88988317/1000000000000 : ℝ)*(sp_s1_0) + (10878600587517/1000000000000 : ℝ)*(sp_s1_7) + (5439283305469/500000000000 : ℝ)*(sp_s1_8) + (10878599392113/1000000000000 : ℝ)*(sp_s1_9) + (4105943516927/1000000000000 : ℝ)*(sp_s1_13) + (1041991/200000000000 : ℝ)*(sp_s1_14) + (2563497/20000000000 : ℝ)*(sp_s1_15) + (3815747/40000000000 : ℝ)*(sp_s1_23) + (4105943516927/1000000000000 : ℝ)*(f.failure) + (2719673696447/250000000000 : ℝ)*(f.sum) + (142229031473607964179/427926046600000000000000000000000 : ℝ)*base63 + (12951113774497/1493050000000000000000000000 : ℝ)*base65 + (7787982291676337/7165300000000000000000000000 : ℝ)*base67 + (666828948333047/5972200000000000000000000000 : ℝ)*base69 + (22969494156504822523/52725567700000000000000000000000 : ℝ)*base71 + (1868105110340803/3531400000000000000000000000 : ℝ)*base73 + (393355545830837/3582650000000000000000000000 : ℝ)*base75 + (39335619088873/353140000000000000000000000 : ℝ)*base77 + (214825500741989032637/253035404200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1827/4000000000000000 : ℝ)*base86 + (1827/4000000000000000 : ℝ)*base88 + (1827/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1783/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1783/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4198050547164527918300824599/213963023300000000000000000000000 : ℝ) := by norm_num
    linear_combination (534498491919/500000000000 : ℝ)*(base39) + (1193321413/8000000000 : ℝ)*(base49) + (812871020331/500000000000 : ℝ)*(base59) + (7656849686121/1000000000000 : ℝ)*(major_s1_0) + (7656849686121/1000000000000 : ℝ)*(major_s1_1) + (7656849686121/1000000000000 : ℝ)*(major_s1_2) + (43156661/1000000000000 : ℝ)*(sp_s1_6) + (80380717/1000000000000 : ℝ)*(sp_s1_7) + (94410911/500000000000 : ℝ)*(sp_s1_8) + (2779375891837/250000000000 : ℝ)*(sp_s1_14) + (2779348781561/250000000000 : ℝ)*(sp_s1_15) + (5558791974033/500000000000 : ℝ)*(sp_s1_16) + (131120824559/31250000000 : ℝ)*(sp_s1_20) + (99670737/500000000000 : ℝ)*(sp_s1_27) + (4196108884023/1000000000000 : ℝ)*(f.failure) + (5558791974033/500000000000 : ℝ)*(f.sum) + (36838999021703297877/427926046600000000000000000000000 : ℝ)*base62 + (142116626042829/1493050000000000000000000000 : ℝ)*base65 + (5673738562871921/7165300000000000000000000000 : ℝ)*base66 + (1095679274947841/5972200000000000000000000000 : ℝ)*base68 + (476122963371443871/52725567700000000000000000000000 : ℝ)*base71 + (313493168932531/3531400000000000000000000000 : ℝ)*base73 + (790276824177801/3582650000000000000000000000 : ℝ)*base74 + (77190860433241/353140000000000000000000000 : ℝ)*base76 + (138508639406454137171/253035404200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (123/4000000000000000 : ℝ)*base86 + (123/4000000000000000 : ℝ)*base88 + (123/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5319/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5319/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7532634284191073213692932101133/472243137801012500000000000000000000 : ℝ) := by norm_num
    linear_combination (2516133/250000000000 : ℝ)*(base11) + (1340854440957/1000000000000 : ℝ)*(base39) + (185738417811/1000000000000 : ℝ)*(base49) + (1229703904389/1000000000000 : ℝ)*(base59) + (5663135303809/1000000000000 : ℝ)*(major_s1_0) + (5663135303809/1000000000000 : ℝ)*(major_s1_1) + (5663135303809/1000000000000 : ℝ)*(major_s1_2) + (3436491/62500000000 : ℝ)*(sp_s1_0) + (1862283/200000000000 : ℝ)*(sp_s1_2) + (105193371/1000000000000 : ℝ)*(sp_s1_9) + (2055671816459/250000000000 : ℝ)*(sp_s1_21) + (513922019639/62500000000 : ℝ)*(sp_s1_22) + (8222637809439/1000000000000 : ℝ)*(sp_s1_23) + (3103512976467/1000000000000 : ℝ)*(sp_s1_27) + (3103512976467/1000000000000 : ℝ)*(f.failure) + (513922019639/62500000000 : ℝ)*(f.sum) + (143077065570390940327/427926046600000000000000000000000 : ℝ)*base63 + (1148560953393851/1493050000000000000000000000 : ℝ)*base65 + (1218849631312879/7165300000000000000000000000 : ℝ)*base66 + (4028997842465171/5972200000000000000000000000 : ℝ)*base69 + (4412028415227974419/52725567700000000000000000000000 : ℝ)*base71 + (2913179845940901/3531400000000000000000000000 : ℝ)*base72 + (155867950721289/895662500000000000000000000 : ℝ)*base75 + (27635730549463/353140000000000000000000000 : ℝ)*base76 + (143111342267984375819/253035404200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (3367/4000000000000000 : ℝ)*base86 + (3367/4000000000000000 : ℝ)*base88 + (3367/4000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((17657/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17657/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71653/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71653/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29861/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29861/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15817/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15817/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1783/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1783/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5319/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5319/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318052_s1 p hpa hpb X hX hprev0

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307075_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:16:25.764663+00:00
-- url     : https://prove2.me/submissions/d140ba40-43e0-4c8f-899d-eaf14784c194

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
theorem collision_support_c307075_s1_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2339909619/10000000000 : ℝ)*x 0 + (-248629461/1250000000 : ℝ)*x 1 + (7855515747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2339909619/10000000000 : ℝ)^17 ≤ (14966025911799/100000000000000 : ℝ)^13 := by
    have hnat : (2339909619 : ℕ)^17*100000000000000^13 ≤ 14966025911799^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339909619 10000000000 14966025911799 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248629461/1250000000 : ℝ)^17 ≤ (605076512851/5000000000000 : ℝ)^13 := by
    have hnat : (248629461 : ℕ)^17*5000000000000^13 ≤ 605076512851^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248629461 1250000000 605076512851 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7855515747/10000000000 : ℝ)^17 ≤ (72932443822937/100000000000000 : ℝ)^13 := by
    have hnat : (7855515747 : ℕ)^17*100000000000000^13 ≤ 72932443822937^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7855515747 10000000000 72932443822937 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2339909619/10000000000 : ℝ), (-248629461/1250000000 : ℝ), (7855515747/10000000000 : ℝ)] ![(14966025911799/100000000000000 : ℝ), (605076512851/5000000000000 : ℝ), (72932443822937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2339909619/10000000000 : ℝ)|^17 ≤ (14966025911799/100000000000000 : ℝ)^13
        have hw : |(2339909619/10000000000 : ℝ)|=(2339909619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248629461/1250000000 : ℝ)|^17 ≤ (605076512851/5000000000000 : ℝ)^13
        have hw : |(-248629461/1250000000 : ℝ)|=(248629461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7855515747/10000000000 : ℝ)|^17 ≤ (72932443822937/100000000000000 : ℝ)^13
        have hw : |(7855515747/10000000000 : ℝ)|=(7855515747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-36332229/1250000000 : ℝ)*x 0 + (-1946927211/2500000000 : ℝ)*x 1 + (3664932771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36332229/1250000000 : ℝ)^17 ≤ (9785353077/1000000000000 : ℝ)^13 := by
    have hnat : (36332229 : ℕ)^17*1000000000000^13 ≤ 9785353077^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36332229 1250000000 9785353077 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946927211/2500000000 : ℝ)^17 ≤ (7211030098847/10000000000000 : ℝ)^13 := by
    have hnat : (1946927211 : ℕ)^17*10000000000000^13 ≤ 7211030098847^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946927211 2500000000 7211030098847 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3664932771/10000000000 : ℝ)^17 ≤ (13455581841351/50000000000000 : ℝ)^13 := by
    have hnat : (3664932771 : ℕ)^17*50000000000000^13 ≤ 13455581841351^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3664932771 10000000000 13455581841351 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36332229/1250000000 : ℝ), (-1946927211/2500000000 : ℝ), (3664932771/10000000000 : ℝ)] ![(9785353077/1000000000000 : ℝ), (7211030098847/10000000000000 : ℝ), (13455581841351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36332229/1250000000 : ℝ)|^17 ≤ (9785353077/1000000000000 : ℝ)^13
        have hw : |(-36332229/1250000000 : ℝ)|=(36332229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1946927211/2500000000 : ℝ)|^17 ≤ (7211030098847/10000000000000 : ℝ)^13
        have hw : |(-1946927211/2500000000 : ℝ)|=(1946927211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3664932771/10000000000 : ℝ)|^17 ≤ (13455581841351/50000000000000 : ℝ)^13
        have hw : |(3664932771/10000000000 : ℝ)|=(3664932771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6149427433/10000000000 : ℝ)*x 0 + (357964217/1000000000 : ℝ)*x 1 + (605372503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6149427433/10000000000 : ℝ)^17 ≤ (26474681308159/50000000000000 : ℝ)^13 := by
    have hnat : (6149427433 : ℕ)^17*50000000000000^13 ≤ 26474681308159^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6149427433 10000000000 26474681308159 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357964217/1000000000 : ℝ)^17 ≤ (26095131960859/100000000000000 : ℝ)^13 := by
    have hnat : (357964217 : ℕ)^17*100000000000000^13 ≤ 26095131960859^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357964217 1000000000 26095131960859 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605372503/2000000000 : ℝ)^17 ≤ (10477752703993/50000000000000 : ℝ)^13 := by
    have hnat : (605372503 : ℕ)^17*50000000000000^13 ≤ 10477752703993^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605372503 2000000000 10477752703993 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6149427433/10000000000 : ℝ), (357964217/1000000000 : ℝ), (605372503/2000000000 : ℝ)] ![(26474681308159/50000000000000 : ℝ), (26095131960859/100000000000000 : ℝ), (10477752703993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6149427433/10000000000 : ℝ)|^17 ≤ (26474681308159/50000000000000 : ℝ)^13
        have hw : |(6149427433/10000000000 : ℝ)|=(6149427433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(357964217/1000000000 : ℝ)|^17 ≤ (26095131960859/100000000000000 : ℝ)^13
        have hw : |(357964217/1000000000 : ℝ)|=(357964217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(605372503/2000000000 : ℝ)|^17 ≤ (10477752703993/50000000000000 : ℝ)^13
        have hw : |(605372503/2000000000 : ℝ)|=(605372503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6763702123/10000000000 : ℝ)*x 0 + (-3909456497/10000000000 : ℝ)*x 1 + (-363291839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6763702123/10000000000 : ℝ)^17 ≤ (11993985984337/20000000000000 : ℝ)^13 := by
    have hnat : (6763702123 : ℕ)^17*20000000000000^13 ≤ 11993985984337^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6763702123 10000000000 11993985984337 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3909456497/10000000000 : ℝ)^17 ≤ (14641438187023/50000000000000 : ℝ)^13 := by
    have hnat : (3909456497 : ℕ)^17*50000000000000^13 ≤ 14641438187023^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909456497 10000000000 14641438187023 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363291839/2000000000 : ℝ)^17 ≤ (5373596844589/50000000000000 : ℝ)^13 := by
    have hnat : (363291839 : ℕ)^17*50000000000000^13 ≤ 5373596844589^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363291839 2000000000 5373596844589 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6763702123/10000000000 : ℝ), (-3909456497/10000000000 : ℝ), (-363291839/2000000000 : ℝ)] ![(11993985984337/20000000000000 : ℝ), (14641438187023/50000000000000 : ℝ), (5373596844589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6763702123/10000000000 : ℝ)|^17 ≤ (11993985984337/20000000000000 : ℝ)^13
        have hw : |(6763702123/10000000000 : ℝ)|=(6763702123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3909456497/10000000000 : ℝ)|^17 ≤ (14641438187023/50000000000000 : ℝ)^13
        have hw : |(-3909456497/10000000000 : ℝ)|=(3909456497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-363291839/2000000000 : ℝ)|^17 ≤ (5373596844589/50000000000000 : ℝ)^13
        have hw : |(-363291839/2000000000 : ℝ)|=(363291839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (82620081/1250000000 : ℝ)*x 0 + (-76755789/2500000000 : ℝ)*x 1 + (9699109069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82620081/1250000000 : ℝ)^17 ≤ (286518528571/10000000000000 : ℝ)^13 := by
    have hnat : (82620081 : ℕ)^17*10000000000000^13 ≤ 286518528571^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82620081 1250000000 286518528571 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76755789/2500000000 : ℝ)^17 ≤ (525599968271/50000000000000 : ℝ)^13 := by
    have hnat : (76755789 : ℕ)^17*50000000000000^13 ≤ 525599968271^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76755789 2500000000 525599968271 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9699109069/10000000000 : ℝ)^17 ≤ (12010451845391/12500000000000 : ℝ)^13 := by
    have hnat : (9699109069 : ℕ)^17*12500000000000^13 ≤ 12010451845391^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9699109069 10000000000 12010451845391 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82620081/1250000000 : ℝ), (-76755789/2500000000 : ℝ), (9699109069/10000000000 : ℝ)] ![(286518528571/10000000000000 : ℝ), (525599968271/50000000000000 : ℝ), (12010451845391/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82620081/1250000000 : ℝ)|^17 ≤ (286518528571/10000000000000 : ℝ)^13
        have hw : |(82620081/1250000000 : ℝ)|=(82620081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76755789/2500000000 : ℝ)|^17 ≤ (525599968271/50000000000000 : ℝ)^13
        have hw : |(-76755789/2500000000 : ℝ)|=(76755789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9699109069/10000000000 : ℝ)|^17 ≤ (12010451845391/12500000000000 : ℝ)^13
        have hw : |(9699109069/10000000000 : ℝ)|=(9699109069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-246842453/10000000000 : ℝ)*x 0 + (-5383653181/10000000000 : ℝ)*x 1 + (6305420949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246842453/10000000000 : ℝ)^17 ≤ (79027784793/10000000000000 : ℝ)^13 := by
    have hnat : (246842453 : ℕ)^17*10000000000000^13 ≤ 79027784793^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246842453 10000000000 79027784793 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5383653181/10000000000 : ℝ)^17 ≤ (4449708476349/10000000000000 : ℝ)^13 := by
    have hnat : (5383653181 : ℕ)^17*10000000000000^13 ≤ 4449708476349^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383653181 10000000000 4449708476349 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6305420949/10000000000 : ℝ)^17 ≤ (54712637369641/100000000000000 : ℝ)^13 := by
    have hnat : (6305420949 : ℕ)^17*100000000000000^13 ≤ 54712637369641^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6305420949 10000000000 54712637369641 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246842453/10000000000 : ℝ), (-5383653181/10000000000 : ℝ), (6305420949/10000000000 : ℝ)] ![(79027784793/10000000000000 : ℝ), (4449708476349/10000000000000 : ℝ), (54712637369641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246842453/10000000000 : ℝ)|^17 ≤ (79027784793/10000000000000 : ℝ)^13
        have hw : |(-246842453/10000000000 : ℝ)|=(246842453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5383653181/10000000000 : ℝ)|^17 ≤ (4449708476349/10000000000000 : ℝ)^13
        have hw : |(-5383653181/10000000000 : ℝ)|=(5383653181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6305420949/10000000000 : ℝ)|^17 ≤ (54712637369641/100000000000000 : ℝ)^13
        have hw : |(6305420949/10000000000 : ℝ)|=(6305420949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8630921357/10000000000 : ℝ)*x 0 + (1676458093/10000000000 : ℝ)*x 1 + (356671869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8630921357/10000000000 : ℝ)^17 ≤ (3299456679199/4000000000000 : ℝ)^13 := by
    have hnat : (8630921357 : ℕ)^17*4000000000000^13 ≤ 3299456679199^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8630921357 10000000000 3299456679199 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1676458093/10000000000 : ℝ)^17 ≤ (9677079350559/100000000000000 : ℝ)^13 := by
    have hnat : (1676458093 : ℕ)^17*100000000000000^13 ≤ 9677079350559^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676458093 10000000000 9677079350559 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356671869/2500000000 : ℝ)^17 ≤ (7836503660913/100000000000000 : ℝ)^13 := by
    have hnat : (356671869 : ℕ)^17*100000000000000^13 ≤ 7836503660913^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356671869 2500000000 7836503660913 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8630921357/10000000000 : ℝ), (1676458093/10000000000 : ℝ), (356671869/2500000000 : ℝ)] ![(3299456679199/4000000000000 : ℝ), (9677079350559/100000000000000 : ℝ), (7836503660913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8630921357/10000000000 : ℝ)|^17 ≤ (3299456679199/4000000000000 : ℝ)^13
        have hw : |(8630921357/10000000000 : ℝ)|=(8630921357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1676458093/10000000000 : ℝ)|^17 ≤ (9677079350559/100000000000000 : ℝ)^13
        have hw : |(1676458093/10000000000 : ℝ)|=(1676458093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356671869/2500000000 : ℝ)|^17 ≤ (7836503660913/100000000000000 : ℝ)^13
        have hw : |(356671869/2500000000 : ℝ)|=(356671869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3232085873/5000000000 : ℝ)*x 0 + (-3917959031/10000000000 : ℝ)*x 1 + (-2237209217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3232085873/5000000000 : ℝ)^17 ≤ (28260455910369/50000000000000 : ℝ)^13 := by
    have hnat : (3232085873 : ℕ)^17*50000000000000^13 ≤ 28260455910369^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3232085873 5000000000 28260455910369 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3917959031/10000000000 : ℝ)^17 ≤ (1468309312721/5000000000000 : ℝ)^13 := by
    have hnat : (3917959031 : ℕ)^17*5000000000000^13 ≤ 1468309312721^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3917959031 10000000000 1468309312721 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237209217/10000000000 : ℝ)^17 ≤ (14112901906949/100000000000000 : ℝ)^13 := by
    have hnat : (2237209217 : ℕ)^17*100000000000000^13 ≤ 14112901906949^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237209217 10000000000 14112901906949 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3232085873/5000000000 : ℝ), (-3917959031/10000000000 : ℝ), (-2237209217/10000000000 : ℝ)] ![(28260455910369/50000000000000 : ℝ), (1468309312721/5000000000000 : ℝ), (14112901906949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3232085873/5000000000 : ℝ)|^17 ≤ (28260455910369/50000000000000 : ℝ)^13
        have hw : |(3232085873/5000000000 : ℝ)|=(3232085873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3917959031/10000000000 : ℝ)|^17 ≤ (1468309312721/5000000000000 : ℝ)^13
        have hw : |(-3917959031/10000000000 : ℝ)|=(3917959031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237209217/10000000000 : ℝ)|^17 ≤ (14112901906949/100000000000000 : ℝ)^13
        have hw : |(-2237209217/10000000000 : ℝ)|=(2237209217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (50877181/625000000 : ℝ)*x 0 + (-142541941/2000000000 : ℝ)*x 1 + (9466050863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50877181/625000000 : ℝ)^17 ≤ (3762324583587/100000000000000 : ℝ)^13 := by
    have hnat : (50877181 : ℕ)^17*100000000000000^13 ≤ 3762324583587^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50877181 625000000 3762324583587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142541941/2000000000 : ℝ)^17 ≤ (3162006262709/100000000000000 : ℝ)^13 := by
    have hnat : (142541941 : ℕ)^17*100000000000000^13 ≤ 3162006262709^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142541941 2000000000 3162006262709 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9466050863/10000000000 : ℝ)^17 ≤ (23268917284987/25000000000000 : ℝ)^13 := by
    have hnat : (9466050863 : ℕ)^17*25000000000000^13 ≤ 23268917284987^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9466050863 10000000000 23268917284987 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50877181/625000000 : ℝ), (-142541941/2000000000 : ℝ), (9466050863/10000000000 : ℝ)] ![(3762324583587/100000000000000 : ℝ), (3162006262709/100000000000000 : ℝ), (23268917284987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50877181/625000000 : ℝ)|^17 ≤ (3762324583587/100000000000000 : ℝ)^13
        have hw : |(50877181/625000000 : ℝ)|=(50877181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142541941/2000000000 : ℝ)|^17 ≤ (3162006262709/100000000000000 : ℝ)^13
        have hw : |(-142541941/2000000000 : ℝ)|=(142541941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9466050863/10000000000 : ℝ)|^17 ≤ (23268917284987/25000000000000 : ℝ)^13
        have hw : |(9466050863/10000000000 : ℝ)|=(9466050863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-25148211/10000000000 : ℝ)*x 0 + (-7821098047/10000000000 : ℝ)*x 1 + (1860213307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25148211/10000000000 : ℝ)^17 ≤ (19935775267/50000000000000 : ℝ)^13 := by
    have hnat : (25148211 : ℕ)^17*50000000000000^13 ≤ 19935775267^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25148211 10000000000 19935775267 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7821098047/10000000000 : ℝ)^17 ≤ (36257431597173/50000000000000 : ℝ)^13 := by
    have hnat : (7821098047 : ℕ)^17*50000000000000^13 ≤ 36257431597173^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7821098047 10000000000 36257431597173 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1860213307/5000000000 : ℝ)^17 ≤ (548905304937/2000000000000 : ℝ)^13 := by
    have hnat : (1860213307 : ℕ)^17*2000000000000^13 ≤ 548905304937^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860213307 5000000000 548905304937 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25148211/10000000000 : ℝ), (-7821098047/10000000000 : ℝ), (1860213307/5000000000 : ℝ)] ![(19935775267/50000000000000 : ℝ), (36257431597173/50000000000000 : ℝ), (548905304937/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25148211/10000000000 : ℝ)|^17 ≤ (19935775267/50000000000000 : ℝ)^13
        have hw : |(-25148211/10000000000 : ℝ)|=(25148211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7821098047/10000000000 : ℝ)|^17 ≤ (36257431597173/50000000000000 : ℝ)^13
        have hw : |(-7821098047/10000000000 : ℝ)|=(7821098047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1860213307/5000000000 : ℝ)|^17 ≤ (548905304937/2000000000000 : ℝ)^13
        have hw : |(1860213307/5000000000 : ℝ)|=(1860213307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4180410213/5000000000 : ℝ)*x 0 + (925947641/5000000000 : ℝ)*x 1 + (1699407429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180410213/5000000000 : ℝ)^17 ≤ (79127141882349/100000000000000 : ℝ)^13 := by
    have hnat : (4180410213 : ℕ)^17*100000000000000^13 ≤ 79127141882349^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180410213 5000000000 79127141882349 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925947641/5000000000 : ℝ)^17 ≤ (5511091699667/50000000000000 : ℝ)^13 := by
    have hnat : (925947641 : ℕ)^17*50000000000000^13 ≤ 5511091699667^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925947641 5000000000 5511091699667 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1699407429/10000000000 : ℝ)^17 ≤ (1970134941227/20000000000000 : ℝ)^13 := by
    have hnat : (1699407429 : ℕ)^17*20000000000000^13 ≤ 1970134941227^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699407429 10000000000 1970134941227 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180410213/5000000000 : ℝ), (925947641/5000000000 : ℝ), (1699407429/10000000000 : ℝ)] ![(79127141882349/100000000000000 : ℝ), (5511091699667/50000000000000 : ℝ), (1970134941227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180410213/5000000000 : ℝ)|^17 ≤ (79127141882349/100000000000000 : ℝ)^13
        have hw : |(4180410213/5000000000 : ℝ)|=(4180410213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925947641/5000000000 : ℝ)|^17 ≤ (5511091699667/50000000000000 : ℝ)^13
        have hw : |(925947641/5000000000 : ℝ)|=(925947641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1699407429/10000000000 : ℝ)|^17 ≤ (1970134941227/20000000000000 : ℝ)^13
        have hw : |(1699407429/10000000000 : ℝ)|=(1699407429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (458680711/1000000000 : ℝ)*x 0 + (-2416022289/5000000000 : ℝ)*x 1 + (-3493906041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458680711/1000000000 : ℝ)^17 ≤ (7217550815747/20000000000000 : ℝ)^13 := by
    have hnat : (458680711 : ℕ)^17*20000000000000^13 ≤ 7217550815747^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458680711 1000000000 7217550815747 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416022289/5000000000 : ℝ)^17 ≤ (9657850057297/25000000000000 : ℝ)^13 := by
    have hnat : (2416022289 : ℕ)^17*25000000000000^13 ≤ 9657850057297^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416022289 5000000000 9657850057297 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3493906041/10000000000 : ℝ)^17 ≤ (25280845675449/100000000000000 : ℝ)^13 := by
    have hnat : (3493906041 : ℕ)^17*100000000000000^13 ≤ 25280845675449^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493906041 10000000000 25280845675449 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(458680711/1000000000 : ℝ), (-2416022289/5000000000 : ℝ), (-3493906041/10000000000 : ℝ)] ![(7217550815747/20000000000000 : ℝ), (9657850057297/25000000000000 : ℝ), (25280845675449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(458680711/1000000000 : ℝ)|^17 ≤ (7217550815747/20000000000000 : ℝ)^13
        have hw : |(458680711/1000000000 : ℝ)|=(458680711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2416022289/5000000000 : ℝ)|^17 ≤ (9657850057297/25000000000000 : ℝ)^13
        have hw : |(-2416022289/5000000000 : ℝ)|=(2416022289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3493906041/10000000000 : ℝ)|^17 ≤ (25280845675449/100000000000000 : ℝ)^13
        have hw : |(-3493906041/10000000000 : ℝ)|=(3493906041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3730534763/10000000000 : ℝ)*x 0 + (-499055603/10000000000 : ℝ)*x 1 + (7652126883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3730534763/10000000000 : ℝ)^17 ≤ (27542816594429/100000000000000 : ℝ)^13 := by
    have hnat : (3730534763 : ℕ)^17*100000000000000^13 ≤ 27542816594429^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730534763 10000000000 27542816594429 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499055603/10000000000 : ℝ)^17 ≤ (496043069621/25000000000000 : ℝ)^13 := by
    have hnat : (499055603 : ℕ)^17*25000000000000^13 ≤ 496043069621^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499055603 10000000000 496043069621 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7652126883/10000000000 : ℝ)^17 ≤ (70473011109499/100000000000000 : ℝ)^13 := by
    have hnat : (7652126883 : ℕ)^17*100000000000000^13 ≤ 70473011109499^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7652126883 10000000000 70473011109499 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3730534763/10000000000 : ℝ), (-499055603/10000000000 : ℝ), (7652126883/10000000000 : ℝ)] ![(27542816594429/100000000000000 : ℝ), (496043069621/25000000000000 : ℝ), (70473011109499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3730534763/10000000000 : ℝ)|^17 ≤ (27542816594429/100000000000000 : ℝ)^13
        have hw : |(3730534763/10000000000 : ℝ)|=(3730534763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499055603/10000000000 : ℝ)|^17 ≤ (496043069621/25000000000000 : ℝ)^13
        have hw : |(-499055603/10000000000 : ℝ)|=(499055603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7652126883/10000000000 : ℝ)|^17 ≤ (70473011109499/100000000000000 : ℝ)^13
        have hw : |(7652126883/10000000000 : ℝ)|=(7652126883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307075_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((3209/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3209/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-18397/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18397/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85663/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7893/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7893/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59121/100000 : ℝ)*X 1 2) := by
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
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (3209/4000 : ℝ) ^ (135/32 : ℝ) ≤ (3947359269586746967/10000000000000000000 : ℝ) := by
    have hpowers : (3209/4000 : ℝ)^135 ≤ (3947359269586746967/10000000000000000000 : ℝ)^32 := by
      have hnat : (3209 : ℕ)^135*10000000000000000000^32 ≤ 3947359269586746967^32*4000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3209 4000 3947359269586746967 10000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3209/4000 : ℝ)) (X := (3947359269586746967/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13947359269586746967/10000000000000000000 : ℝ) ≤ (2164113072251613/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (13947359269586746967/10000000000000000000 : ℝ)^32 ≤ (2164113072251613/2000000000000000 : ℝ)^135 := by
      have hnat : (13947359269586746967 : ℕ)^32*2000000000000000^135 ≤ 2164113072251613^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13947359269586746967 10000000000000000000 2164113072251613 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2164113072251613/2000000000000000 : ℝ)) (X := (13947359269586746967/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (8947359269586746967/5000000000000000000 : ℝ) ≤ (2869757261589903/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (8947359269586746967/5000000000000000000 : ℝ)^32 ≤ (2869757261589903/2500000000000000 : ℝ)^135 := by
      have hnat : (8947359269586746967 : ℕ)^32*2500000000000000^135 ≤ 2869757261589903^135*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8947359269586746967 5000000000000000000 2869757261589903 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2869757261589903/2500000000000000 : ℝ)) (X := (8947359269586746967/5000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(164113072251613/1604500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(658463685101547/8022500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (3209/4000 : ℝ)) (alpha := (164113072251613/1604500000000000 : ℝ)) (beta := (658463685101547/8022500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3209/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(164113072251613/1604500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(658463685101547/8022500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18397/20000 : ℝ) ^ (135/32 : ℝ) ≤ (35148043208483390669/50000000000000000000 : ℝ) := by
    have hpowers : (18397/20000 : ℝ)^135 ≤ (35148043208483390669/50000000000000000000 : ℝ)^32 := by
      have hnat : (18397 : ℕ)^135*50000000000000000000^32 ≤ 35148043208483390669^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18397 20000 35148043208483390669 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18397/20000 : ℝ)) (X := (35148043208483390669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (85148043208483390669/50000000000000000000 : ℝ) ≤ (5672494372105477/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (85148043208483390669/50000000000000000000 : ℝ)^32 ≤ (5672494372105477/5000000000000000 : ℝ)^135 := by
      have hnat : (85148043208483390669 : ℕ)^32*5000000000000000^135 ≤ 5672494372105477^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85148043208483390669 50000000000000000000 5672494372105477 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5672494372105477/5000000000000000 : ℝ)) (X := (85148043208483390669/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60148043208483390669/25000000000000000000 : ℝ) ≤ (6156697844810033/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (60148043208483390669/25000000000000000000 : ℝ)^32 ≤ (6156697844810033/5000000000000000 : ℝ)^135 := by
      have hnat : (60148043208483390669 : ℕ)^32*5000000000000000^135 ≤ 6156697844810033^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60148043208483390669 25000000000000000000 6156697844810033 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6156697844810033/5000000000000000 : ℝ)) (X := (60148043208483390669/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(672494372105477/4599250000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(121050868176139/1149812500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (18397/20000 : ℝ)) (alpha := (672494372105477/4599250000000000 : ℝ)) (beta := (121050868176139/1149812500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (18397/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(672494372105477/4599250000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(121050868176139/1149812500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (85663/100000 : ℝ) ^ (135/32 : ℝ) ≤ (52056102501524301777/100000000000000000000 : ℝ) := by
    have hpowers : (85663/100000 : ℝ)^135 ≤ (52056102501524301777/100000000000000000000 : ℝ)^32 := by
      have hnat : (85663 : ℕ)^135*100000000000000000000^32 ≤ 52056102501524301777^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85663 100000 52056102501524301777 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85663/100000 : ℝ)) (X := (52056102501524301777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (152056102501524301777/100000000000000000000 : ℝ) ≤ (2208877594777121/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (152056102501524301777/100000000000000000000 : ℝ)^32 ≤ (2208877594777121/2000000000000000 : ℝ)^135 := by
      have hnat : (152056102501524301777 : ℕ)^32*2000000000000000^135 ≤ 2208877594777121^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        152056102501524301777 100000000000000000000 2208877594777121 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2208877594777121/2000000000000000 : ℝ)) (X := (152056102501524301777/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (102056102501524301777/50000000000000000000 : ℝ) ≤ (11842691702379801/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (102056102501524301777/50000000000000000000 : ℝ)^32 ≤ (11842691702379801/10000000000000000 : ℝ)^135 := by
      have hnat : (102056102501524301777 : ℕ)^32*10000000000000000^135 ≤ 11842691702379801^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102056102501524301777 50000000000000000000 11842691702379801 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11842691702379801/10000000000000000 : ℝ)) (X := (102056102501524301777/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(208877594777121/1713260000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(199575932123549/2141575000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (85663/100000 : ℝ)) (alpha := (208877594777121/1713260000000000 : ℝ)) (beta := (199575932123549/2141575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (85663/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(208877594777121/1713260000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(199575932123549/2141575000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_6 : ((2339909619/10000000000 : ℝ)*X 0 0+(-248629461/1250000000 : ℝ)*X 0 1+(7855515747/10000000000 : ℝ)*X 0 2+(2339909619/10000000000 : ℝ)*X 1 0+(-248629461/1250000000 : ℝ)*X 1 1+(7855515747/10000000000 : ℝ)*X 1 2+(2339909619/10000000000 : ℝ)*X 2 0+(-248629461/1250000000 : ℝ)*X 2 1+(7855515747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-36332229/1250000000 : ℝ)*X 0 0+(-1946927211/2500000000 : ℝ)*X 0 1+(3664932771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((6149427433/10000000000 : ℝ)*X 1 0+(357964217/1000000000 : ℝ)*X 1 1+(605372503/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((6763702123/10000000000 : ℝ)*X 2 0+(-3909456497/10000000000 : ℝ)*X 2 1+(-363291839/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((82620081/1250000000 : ℝ)*X 0 0+(-76755789/2500000000 : ℝ)*X 0 1+(9699109069/10000000000 : ℝ)*X 0 2+(82620081/1250000000 : ℝ)*X 1 0+(-76755789/2500000000 : ℝ)*X 1 1+(9699109069/10000000000 : ℝ)*X 1 2+(82620081/1250000000 : ℝ)*X 2 0+(-76755789/2500000000 : ℝ)*X 2 1+(9699109069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-246842453/10000000000 : ℝ)*X 0 0+(-5383653181/10000000000 : ℝ)*X 0 1+(6305420949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((8630921357/10000000000 : ℝ)*X 1 0+(1676458093/10000000000 : ℝ)*X 1 1+(356671869/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3232085873/5000000000 : ℝ)*X 2 0+(-3917959031/10000000000 : ℝ)*X 2 1+(-2237209217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((50877181/625000000 : ℝ)*X 0 0+(-142541941/2000000000 : ℝ)*X 0 1+(9466050863/10000000000 : ℝ)*X 0 2+(50877181/625000000 : ℝ)*X 1 0+(-142541941/2000000000 : ℝ)*X 1 1+(9466050863/10000000000 : ℝ)*X 1 2+(50877181/625000000 : ℝ)*X 2 0+(-142541941/2000000000 : ℝ)*X 2 1+(9466050863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-25148211/10000000000 : ℝ)*X 0 0+(-7821098047/10000000000 : ℝ)*X 0 1+(1860213307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4180410213/5000000000 : ℝ)*X 1 0+(925947641/5000000000 : ℝ)*X 1 1+(1699407429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((458680711/1000000000 : ℝ)*X 2 0+(-2416022289/5000000000 : ℝ)*X 2 1+(-3493906041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3730534763/10000000000 : ℝ)*X 0 0+(-499055603/10000000000 : ℝ)*X 0 1+(7652126883/10000000000 : ℝ)*X 0 2+(3730534763/10000000000 : ℝ)*X 1 0+(-499055603/10000000000 : ℝ)*X 1 1+(7652126883/10000000000 : ℝ)*X 1 2+(3730534763/10000000000 : ℝ)*X 2 0+(-499055603/10000000000 : ℝ)*X 2 1+(7652126883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36772263025163768613365861380107/6321498193873750000000000000000000000 : ℝ) := by norm_num
    linear_combination (7229402621/62500000000 : ℝ)*(base7) + (109172668743/500000000000 : ℝ)*(base43) + (693990820433/1000000000000 : ℝ)*(base54) + (1401533/1000000000000 : ℝ)*(base60) + (2347756583957/1000000000000 : ℝ)*(major_s1_0) + (2129411246471/1000000000000 : ℝ)*(major_s1_1) + (413441440881/250000000000 : ℝ)*(major_s1_2) + (2895422961497/1000000000000 : ℝ)*(sp_s1_7) + (778454815107/250000000000 : ℝ)*(sp_s1_8) + (13758343127/6250000000 : ℝ)*(sp_s1_9) + (232993704111/250000000000 : ℝ)*(sp_s1_13) + (148202189/1000000000000 : ℝ)*(sp_s1_16) + (21170633/1000000000000 : ℝ)*(sp_s1_20) + (12740361/250000000000 : ℝ)*(sp_s1_21) + (755158182787/500000000000 : ℝ)*(f.failure) + (778454815107/250000000000 : ℝ)*(f.sum) + (105326560056472854619/196992776375000000000000000000000 : ℝ)*base62 + (4306799052825877/4283150000000000000000000000 : ℝ)*base64 + (1075349377329483/4599250000000000000000000000 : ℝ)*base66 + (11634303870921/17132600000000000000000000 : ℝ)*base68 + (74243471211937568547/137446283500000000000000000000000 : ℝ)*base70 + (4339200351922271/8022500000000000000000000000 : ℝ)*base72 + (207152590272163/2299625000000000000000000000 : ℝ)*base74 + (261649782554759/1604500000000000000000000000 : ℝ)*base76 + (2440914935736848307/147589932500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (2947/6250000000000000 : ℝ)*base87 + (2947/6250000000000000 : ℝ)*base89 + (2947/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-7893/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7893/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32659596067862758287909869201997/3160749096936875000000000000000000000 : ℝ) := by norm_num
    linear_combination (497486558161/1000000000000 : ℝ)*(base7) + (5518777061/15625000000 : ℝ)*(base33) + (222955066837/1000000000000 : ℝ)*(base40) + (6217316623/100000000000 : ℝ)*(base54) + (5565402697/100000000000 : ℝ)*(base60) + (953733655963/500000000000 : ℝ)*(major_s1_0) + (226066904383/100000000000 : ℝ)*(major_s1_1) + (2748119847/1250000000 : ℝ)*(major_s1_2) + (16828793/1000000000000 : ℝ)*(sp_s1_13) + (2760062805747/1000000000000 : ℝ)*(sp_s1_14) + (2406671532519/1000000000000 : ℝ)*(sp_s1_15) + (2344687907613/1000000000000 : ℝ)*(sp_s1_16) + (1889589345181/1000000000000 : ℝ)*(sp_s1_20) + (47385331/250000000000 : ℝ)*(sp_s1_22) + (1454292782043/1000000000000 : ℝ)*(f.failure) + (2760062805747/1000000000000 : ℝ)*(f.sum) + (35720554090071561743/78797110550000000000000000000000 : ℝ)*base62 + (25145652749/66924218750000000000000 : ℝ)*base64 + (23298506877727/919850000000000000000000000 : ℝ)*base67 + (338206852588261/856630000000000000000000000 : ℝ)*base68 + (34886052976933744853/68723141750000000000000000000000 : ℝ)*base70 + (4845753494761/4011250000000000000000000000 : ℝ)*base73 + (113731698055587/459925000000000000000000000 : ℝ)*base75 + (61635237455581/802250000000000000000000000 : ℝ)*base76 + (1417565431860041137/4612185390625000000000000000000 : ℝ)*base79 + (2533/12500000000000000 : ℝ)*base87 + (2533/12500000000000000 : ℝ)*base89 + (2533/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59121/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10545842962370009082753179248497/632149819387375000000000000000000000 : ℝ) := by norm_num
    linear_combination (36117/125000000000 : ℝ)*(base3) + (341133/1000000000000 : ℝ)*(base22) + (416141622439/500000000000 : ℝ)*(base40) + (3303249/500000000000 : ℝ)*(base43) + (128564805461/1000000000000 : ℝ)*(base49) + (4952918801/1250000000 : ℝ)*(major_s1_0) + (1981164217151/500000000000 : ℝ)*(major_s1_1) + (4952918801/1250000000 : ℝ)*(major_s1_2) + (31972687/1000000000000 : ℝ)*(sp_s1_6) + (138927249/250000000000 : ℝ)*(sp_s1_7) + (2687562192901/500000000000 : ℝ)*(sp_s1_21) + (671960873779/125000000000 : ℝ)*(sp_s1_22) + (1075135950733/200000000000 : ℝ)*(sp_s1_23) + (2548945557841/1000000000000 : ℝ)*(sp_s1_27) + (318622227433/125000000000 : ℝ)*(f.failure) + (1075137340259/200000000000 : ℝ)*(f.sum) + (44254665379109801603/196992776375000000000000000000000 : ℝ)*base62 + (420163978677631/856630000000000000000000000 : ℝ)*base65 + (990070007438873/2299625000000000000000000000 : ℝ)*base66 + (36814588577973/107078750000000000000000000 : ℝ)*base68 + (846318974373798931/2748925670000000000000000000000 : ℝ)*base70 + (1476483780881/20056250000000000000000000 : ℝ)*base72 + (500334818529231/2299625000000000000000000000 : ℝ)*base74 + (5482145779349/32090000000000000000000000 : ℝ)*base77 + (1624253250186649269/14758993250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (623/1562500000000000 : ℝ)*base87 + (623/1562500000000000 : ℝ)*base89 + (623/1562500000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((3209/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3209/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-18397/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18397/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85663/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7893/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7893/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59121/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307075_s1 p hpa hpb X hX hprev0

#print axioms solution

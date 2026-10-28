-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305058_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:30:50.866091+00:00
-- url     : https://prove2.me/submissions/21b22259-b9bc-4e71-b89e-15b5f335ba72

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
theorem collision_support_c305058_s2_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1643553799/5000000000 : ℝ)*x 0 + (1589825011/5000000000 : ℝ)*x 1 + (-6310519199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643553799/5000000000 : ℝ)^67 ≤ (2898251995093/12500000000000 : ℝ)^51 := by
    have hnat : (1643553799 : ℕ)^67*12500000000000^51 ≤ 2898251995093^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643553799 5000000000 2898251995093 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1589825011/5000000000 : ℝ)^67 ≤ (443908054083/2000000000000 : ℝ)^51 := by
    have hnat : (1589825011 : ℕ)^67*2000000000000^51 ≤ 443908054083^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589825011 5000000000 443908054083 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6310519199/10000000000 : ℝ)^67 ≤ (54618581320981/100000000000000 : ℝ)^51 := by
    have hnat : (6310519199 : ℕ)^67*100000000000000^51 ≤ 54618581320981^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6310519199 10000000000 54618581320981 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1643553799/5000000000 : ℝ), (1589825011/5000000000 : ℝ), (-6310519199/10000000000 : ℝ)] ![(2898251995093/12500000000000 : ℝ), (443908054083/2000000000000 : ℝ), (54618581320981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1643553799/5000000000 : ℝ)|^67 ≤ (2898251995093/12500000000000 : ℝ)^51
        have hw : |(-1643553799/5000000000 : ℝ)|=(1643553799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1589825011/5000000000 : ℝ)|^67 ≤ (443908054083/2000000000000 : ℝ)^51
        have hw : |(1589825011/5000000000 : ℝ)|=(1589825011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6310519199/10000000000 : ℝ)|^67 ≤ (54618581320981/100000000000000 : ℝ)^51
        have hw : |(-6310519199/10000000000 : ℝ)|=(6310519199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3277155121/10000000000 : ℝ)*x 0 + (-392653817/1250000000 : ℝ)*x 1 + (-6349515189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3277155121/10000000000 : ℝ)^67 ≤ (11546917464537/50000000000000 : ℝ)^51 := by
    have hnat : (3277155121 : ℕ)^67*50000000000000^51 ≤ 11546917464537^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3277155121 10000000000 11546917464537 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392653817/1250000000 : ℝ)^67 ≤ (21843750237563/100000000000000 : ℝ)^51 := by
    have hnat : (392653817 : ℕ)^67*100000000000000^51 ≤ 21843750237563^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392653817 1250000000 21843750237563 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6349515189/10000000000 : ℝ)^67 ≤ (6882801852829/12500000000000 : ℝ)^51 := by
    have hnat : (6349515189 : ℕ)^67*12500000000000^51 ≤ 6882801852829^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6349515189 10000000000 6882801852829 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3277155121/10000000000 : ℝ), (-392653817/1250000000 : ℝ), (-6349515189/10000000000 : ℝ)] ![(11546917464537/50000000000000 : ℝ), (21843750237563/100000000000000 : ℝ), (6882801852829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3277155121/10000000000 : ℝ)|^67 ≤ (11546917464537/50000000000000 : ℝ)^51
        have hw : |(3277155121/10000000000 : ℝ)|=(3277155121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-392653817/1250000000 : ℝ)|^67 ≤ (21843750237563/100000000000000 : ℝ)^51
        have hw : |(-392653817/1250000000 : ℝ)|=(392653817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6349515189/10000000000 : ℝ)|^67 ≤ (6882801852829/12500000000000 : ℝ)^51
        have hw : |(-6349515189/10000000000 : ℝ)|=(6349515189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5880725731/10000000000 : ℝ)*x 0 + (643183381/1250000000 : ℝ)*x 1 + (152351257/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5880725731/10000000000 : ℝ)^67 ≤ (398277264767/800000000000 : ℝ)^51 := by
    have hnat : (5880725731 : ℕ)^67*800000000000^51 ≤ 398277264767^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5880725731 10000000000 398277264767 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643183381/1250000000 : ℝ)^67 ≤ (8354518042739/20000000000000 : ℝ)^51 := by
    have hnat : (643183381 : ℕ)^67*20000000000000^51 ≤ 8354518042739^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643183381 1250000000 8354518042739 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152351257/1000000000 : ℝ)^67 ≤ (8442751675927/100000000000000 : ℝ)^51 := by
    have hnat : (152351257 : ℕ)^67*100000000000000^51 ≤ 8442751675927^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152351257 1000000000 8442751675927 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5880725731/10000000000 : ℝ), (643183381/1250000000 : ℝ), (152351257/1000000000 : ℝ)] ![(398277264767/800000000000 : ℝ), (8354518042739/20000000000000 : ℝ), (8442751675927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5880725731/10000000000 : ℝ)|^67 ≤ (398277264767/800000000000 : ℝ)^51
        have hw : |(5880725731/10000000000 : ℝ)|=(5880725731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643183381/1250000000 : ℝ)|^67 ≤ (8354518042739/20000000000000 : ℝ)^51
        have hw : |(643183381/1250000000 : ℝ)|=(643183381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152351257/1000000000 : ℝ)|^67 ≤ (8442751675927/100000000000000 : ℝ)^51
        have hw : |(152351257/1000000000 : ℝ)|=(152351257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-65640921/250000000 : ℝ)*x 0 + (2280235221/10000000000 : ℝ)*x 1 + (-748936623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65640921/250000000 : ℝ)^67 ≤ (8629860386807/50000000000000 : ℝ)^51 := by
    have hnat : (65640921 : ℕ)^67*50000000000000^51 ≤ 8629860386807^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65640921 250000000 8629860386807 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280235221/10000000000 : ℝ)^67 ≤ (14340407762099/100000000000000 : ℝ)^51 := by
    have hnat : (2280235221 : ℕ)^67*100000000000000^51 ≤ 14340407762099^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280235221 10000000000 14340407762099 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748936623/1000000000 : ℝ)^67 ≤ (13679974291193/20000000000000 : ℝ)^51 := by
    have hnat : (748936623 : ℕ)^67*20000000000000^51 ≤ 13679974291193^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748936623 1000000000 13679974291193 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65640921/250000000 : ℝ), (2280235221/10000000000 : ℝ), (-748936623/1000000000 : ℝ)] ![(8629860386807/50000000000000 : ℝ), (14340407762099/100000000000000 : ℝ), (13679974291193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65640921/250000000 : ℝ)|^67 ≤ (8629860386807/50000000000000 : ℝ)^51
        have hw : |(-65640921/250000000 : ℝ)|=(65640921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2280235221/10000000000 : ℝ)|^67 ≤ (14340407762099/100000000000000 : ℝ)^51
        have hw : |(2280235221/10000000000 : ℝ)|=(2280235221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748936623/1000000000 : ℝ)|^67 ≤ (13679974291193/20000000000000 : ℝ)^51
        have hw : |(-748936623/1000000000 : ℝ)|=(748936623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2847178627/10000000000 : ℝ)*x 0 + (-452112153/2000000000 : ℝ)*x 1 + (-7340903573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2847178627/10000000000 : ℝ)^67 ≤ (19197766444997/100000000000000 : ℝ)^51 := by
    have hnat : (2847178627 : ℕ)^67*100000000000000^51 ≤ 19197766444997^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847178627 10000000000 19197766444997 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452112153/2000000000 : ℝ)^67 ≤ (1772259670699/12500000000000 : ℝ)^51 := by
    have hnat : (452112153 : ℕ)^67*12500000000000^51 ≤ 1772259670699^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452112153 2000000000 1772259670699 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7340903573/10000000000 : ℝ)^67 ≤ (104100244031/156250000000 : ℝ)^51 := by
    have hnat : (7340903573 : ℕ)^67*156250000000^51 ≤ 104100244031^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7340903573 10000000000 104100244031 156250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2847178627/10000000000 : ℝ), (-452112153/2000000000 : ℝ), (-7340903573/10000000000 : ℝ)] ![(19197766444997/100000000000000 : ℝ), (1772259670699/12500000000000 : ℝ), (104100244031/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2847178627/10000000000 : ℝ)|^67 ≤ (19197766444997/100000000000000 : ℝ)^51
        have hw : |(2847178627/10000000000 : ℝ)|=(2847178627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452112153/2000000000 : ℝ)|^67 ≤ (1772259670699/12500000000000 : ℝ)^51
        have hw : |(-452112153/2000000000 : ℝ)|=(452112153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7340903573/10000000000 : ℝ)|^67 ≤ (104100244031/156250000000 : ℝ)^51
        have hw : |(-7340903573/10000000000 : ℝ)|=(7340903573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4959061299/10000000000 : ℝ)*x 0 + (3032007681/5000000000 : ℝ)*x 1 + (756826457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4959061299/10000000000 : ℝ)^67 ≤ (1243622439827/3125000000000 : ℝ)^51 := by
    have hnat : (4959061299 : ℕ)^67*3125000000000^51 ≤ 1243622439827^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959061299 10000000000 1243622439827 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3032007681/5000000000 : ℝ)^67 ≤ (51833037411287/100000000000000 : ℝ)^51 := by
    have hnat : (3032007681 : ℕ)^67*100000000000000^51 ≤ 51833037411287^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3032007681 5000000000 51833037411287 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (756826457/5000000000 : ℝ)^67 ≤ (4185522251159/50000000000000 : ℝ)^51 := by
    have hnat : (756826457 : ℕ)^67*50000000000000^51 ≤ 4185522251159^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756826457 5000000000 4185522251159 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4959061299/10000000000 : ℝ), (3032007681/5000000000 : ℝ), (756826457/5000000000 : ℝ)] ![(1243622439827/3125000000000 : ℝ), (51833037411287/100000000000000 : ℝ), (4185522251159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4959061299/10000000000 : ℝ)|^67 ≤ (1243622439827/3125000000000 : ℝ)^51
        have hw : |(4959061299/10000000000 : ℝ)|=(4959061299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3032007681/5000000000 : ℝ)|^67 ≤ (51833037411287/100000000000000 : ℝ)^51
        have hw : |(3032007681/5000000000 : ℝ)|=(3032007681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(756826457/5000000000 : ℝ)|^67 ≤ (4185522251159/50000000000000 : ℝ)^51
        have hw : |(756826457/5000000000 : ℝ)|=(756826457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3182939901/10000000000 : ℝ)*x 0 + (825858447/1000000000 : ℝ)*x 1 + (-5627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3182939901/10000000000 : ℝ)^67 ≤ (22225577109771/100000000000000 : ℝ)^51 := by
    have hnat : (3182939901 : ℕ)^67*100000000000000^51 ≤ 22225577109771^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182939901 10000000000 22225577109771 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825858447/1000000000 : ℝ)^67 ≤ (15554884268681/20000000000000 : ℝ)^51 := by
    have hnat : (825858447 : ℕ)^67*20000000000000^51 ≤ 15554884268681^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825858447 1000000000 15554884268681 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5627/5000000000 : ℝ)^67 ≤ (306253/20000000000000 : ℝ)^51 := by
    have hnat : (5627 : ℕ)^67*20000000000000^51 ≤ 306253^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5627 5000000000 306253 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3182939901/10000000000 : ℝ), (825858447/1000000000 : ℝ), (-5627/5000000000 : ℝ)] ![(22225577109771/100000000000000 : ℝ), (15554884268681/20000000000000 : ℝ), (306253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3182939901/10000000000 : ℝ)|^67 ≤ (22225577109771/100000000000000 : ℝ)^51
        have hw : |(3182939901/10000000000 : ℝ)|=(3182939901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825858447/1000000000 : ℝ)|^67 ≤ (15554884268681/20000000000000 : ℝ)^51
        have hw : |(825858447/1000000000 : ℝ)|=(825858447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5627/5000000000 : ℝ)|^67 ≤ (306253/20000000000000 : ℝ)^51
        have hw : |(-5627/5000000000 : ℝ)|=(5627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2652951159/10000000000 : ℝ)*x 0 + (1396277597/5000000000 : ℝ)*x 1 + (-1775463833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652951159/10000000000 : ℝ)^67 ≤ (17495986406369/100000000000000 : ℝ)^51 := by
    have hnat : (2652951159 : ℕ)^67*100000000000000^51 ≤ 17495986406369^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652951159 10000000000 17495986406369 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396277597/5000000000 : ℝ)^67 ≤ (233942114461/1250000000000 : ℝ)^51 := by
    have hnat : (1396277597 : ℕ)^67*1250000000000^51 ≤ 233942114461^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396277597 5000000000 233942114461 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775463833/2500000000 : ℝ)^67 ≤ (31894322213681/50000000000000 : ℝ)^51 := by
    have hnat : (1775463833 : ℕ)^67*50000000000000^51 ≤ 31894322213681^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775463833 2500000000 31894322213681 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2652951159/10000000000 : ℝ), (1396277597/5000000000 : ℝ), (-1775463833/2500000000 : ℝ)] ![(17495986406369/100000000000000 : ℝ), (233942114461/1250000000000 : ℝ), (31894322213681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2652951159/10000000000 : ℝ)|^67 ≤ (17495986406369/100000000000000 : ℝ)^51
        have hw : |(-2652951159/10000000000 : ℝ)|=(2652951159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396277597/5000000000 : ℝ)|^67 ≤ (233942114461/1250000000000 : ℝ)^51
        have hw : |(1396277597/5000000000 : ℝ)|=(1396277597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1775463833/2500000000 : ℝ)|^67 ≤ (31894322213681/50000000000000 : ℝ)^51
        have hw : |(-1775463833/2500000000 : ℝ)|=(1775463833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2729005421/10000000000 : ℝ)*x 0 + (-2904766753/10000000000 : ℝ)*x 1 + (-6961074637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2729005421/10000000000 : ℝ)^67 ≤ (18157857428037/100000000000000 : ℝ)^51 := by
    have hnat : (2729005421 : ℕ)^67*100000000000000^51 ≤ 18157857428037^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729005421 10000000000 18157857428037 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2904766753/10000000000 : ℝ)^67 ≤ (2463687367191/12500000000000 : ℝ)^51 := by
    have hnat : (2904766753 : ℕ)^67*12500000000000^51 ≤ 2463687367191^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2904766753 10000000000 2463687367191 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6961074637/10000000000 : ℝ)^67 ≤ (62132643620407/100000000000000 : ℝ)^51 := by
    have hnat : (6961074637 : ℕ)^67*100000000000000^51 ≤ 62132643620407^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6961074637 10000000000 62132643620407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2729005421/10000000000 : ℝ), (-2904766753/10000000000 : ℝ), (-6961074637/10000000000 : ℝ)] ![(18157857428037/100000000000000 : ℝ), (2463687367191/12500000000000 : ℝ), (62132643620407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2729005421/10000000000 : ℝ)|^67 ≤ (18157857428037/100000000000000 : ℝ)^51
        have hw : |(2729005421/10000000000 : ℝ)|=(2729005421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2904766753/10000000000 : ℝ)|^67 ≤ (2463687367191/12500000000000 : ℝ)^51
        have hw : |(-2904766753/10000000000 : ℝ)|=(2904766753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6961074637/10000000000 : ℝ)|^67 ≤ (62132643620407/100000000000000 : ℝ)^51
        have hw : |(-6961074637/10000000000 : ℝ)|=(6961074637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6419321151/10000000000 : ℝ)*x 0 + (38779757/78125000 : ℝ)*x 1 + (910789061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6419321151/10000000000 : ℝ)^67 ≤ (11171809555967/20000000000000 : ℝ)^51 := by
    have hnat : (6419321151 : ℕ)^67*20000000000000^51 ≤ 11171809555967^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6419321151 10000000000 11171809555967 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38779757/78125000 : ℝ)^67 ≤ (39845977138507/100000000000000 : ℝ)^51 := by
    have hnat : (38779757 : ℕ)^67*100000000000000^51 ≤ 39845977138507^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38779757 78125000 39845977138507 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910789061/10000000000 : ℝ)^67 ≤ (2147487533173/50000000000000 : ℝ)^51 := by
    have hnat : (910789061 : ℕ)^67*50000000000000^51 ≤ 2147487533173^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910789061 10000000000 2147487533173 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6419321151/10000000000 : ℝ), (38779757/78125000 : ℝ), (910789061/10000000000 : ℝ)] ![(11171809555967/20000000000000 : ℝ), (39845977138507/100000000000000 : ℝ), (2147487533173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6419321151/10000000000 : ℝ)|^67 ≤ (11171809555967/20000000000000 : ℝ)^51
        have hw : |(6419321151/10000000000 : ℝ)|=(6419321151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38779757/78125000 : ℝ)|^67 ≤ (39845977138507/100000000000000 : ℝ)^51
        have hw : |(38779757/78125000 : ℝ)|=(38779757/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910789061/10000000000 : ℝ)|^67 ≤ (2147487533173/50000000000000 : ℝ)^51
        have hw : |(910789061/10000000000 : ℝ)|=(910789061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-667833177/2000000000 : ℝ)*x 0 + (655170311/2000000000 : ℝ)*x 1 + (-1237934223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667833177/2000000000 : ℝ)^67 ≤ (4733921879113/20000000000000 : ℝ)^51 := by
    have hnat : (667833177 : ℕ)^67*20000000000000^51 ≤ 4733921879113^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667833177 2000000000 4733921879113 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655170311/2000000000 : ℝ)^67 ≤ (23081767643011/100000000000000 : ℝ)^51 := by
    have hnat : (655170311 : ℕ)^67*100000000000000^51 ≤ 23081767643011^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655170311 2000000000 23081767643011 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237934223/2000000000 : ℝ)^67 ≤ (26624311472481/50000000000000 : ℝ)^51 := by
    have hnat : (1237934223 : ℕ)^67*50000000000000^51 ≤ 26624311472481^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237934223 2000000000 26624311472481 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-667833177/2000000000 : ℝ), (655170311/2000000000 : ℝ), (-1237934223/2000000000 : ℝ)] ![(4733921879113/20000000000000 : ℝ), (23081767643011/100000000000000 : ℝ), (26624311472481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-667833177/2000000000 : ℝ)|^67 ≤ (4733921879113/20000000000000 : ℝ)^51
        have hw : |(-667833177/2000000000 : ℝ)|=(667833177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655170311/2000000000 : ℝ)|^67 ≤ (23081767643011/100000000000000 : ℝ)^51
        have hw : |(655170311/2000000000 : ℝ)|=(655170311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1237934223/2000000000 : ℝ)|^67 ≤ (26624311472481/50000000000000 : ℝ)^51
        have hw : |(-1237934223/2000000000 : ℝ)|=(1237934223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3485588561/10000000000 : ℝ)*x 0 + (-164793131/500000000 : ℝ)*x 1 + (-6051308101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3485588561/10000000000 : ℝ)^67 ≤ (25042430292561/100000000000000 : ℝ)^51 := by
    have hnat : (3485588561 : ℕ)^67*100000000000000^51 ≤ 25042430292561^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3485588561 10000000000 25042430292561 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164793131/500000000 : ℝ)^67 ≤ (5816794613339/25000000000000 : ℝ)^51 := by
    have hnat : (164793131 : ℕ)^67*25000000000000^51 ≤ 5816794613339^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164793131 500000000 5816794613339 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6051308101/10000000000 : ℝ)^67 ≤ (51690391248113/100000000000000 : ℝ)^51 := by
    have hnat : (6051308101 : ℕ)^67*100000000000000^51 ≤ 51690391248113^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051308101 10000000000 51690391248113 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3485588561/10000000000 : ℝ), (-164793131/500000000 : ℝ), (-6051308101/10000000000 : ℝ)] ![(25042430292561/100000000000000 : ℝ), (5816794613339/25000000000000 : ℝ), (51690391248113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3485588561/10000000000 : ℝ)|^67 ≤ (25042430292561/100000000000000 : ℝ)^51
        have hw : |(3485588561/10000000000 : ℝ)|=(3485588561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164793131/500000000 : ℝ)|^67 ≤ (5816794613339/25000000000000 : ℝ)^51
        have hw : |(-164793131/500000000 : ℝ)|=(164793131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6051308101/10000000000 : ℝ)|^67 ≤ (51690391248113/100000000000000 : ℝ)^51
        have hw : |(-6051308101/10000000000 : ℝ)|=(6051308101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (870609779/1250000000 : ℝ)*x 0 + (2009387983/5000000000 : ℝ)*x 1 + (1410681039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870609779/1250000000 : ℝ)^67 ≤ (31088624110463/50000000000000 : ℝ)^51 := by
    have hnat : (870609779 : ℕ)^67*50000000000000^51 ≤ 31088624110463^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870609779 1250000000 31088624110463 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009387983/5000000000 : ℝ)^67 ≤ (1509586254947/5000000000000 : ℝ)^51 := by
    have hnat : (2009387983 : ℕ)^67*5000000000000^51 ≤ 1509586254947^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009387983 5000000000 1509586254947 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1410681039/10000000000 : ℝ)^67 ≤ (1526205334229/20000000000000 : ℝ)^51 := by
    have hnat : (1410681039 : ℕ)^67*20000000000000^51 ≤ 1526205334229^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410681039 10000000000 1526205334229 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870609779/1250000000 : ℝ), (2009387983/5000000000 : ℝ), (1410681039/10000000000 : ℝ)] ![(31088624110463/50000000000000 : ℝ), (1509586254947/5000000000000 : ℝ), (1526205334229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870609779/1250000000 : ℝ)|^67 ≤ (31088624110463/50000000000000 : ℝ)^51
        have hw : |(870609779/1250000000 : ℝ)|=(870609779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009387983/5000000000 : ℝ)|^67 ≤ (1509586254947/5000000000000 : ℝ)^51
        have hw : |(2009387983/5000000000 : ℝ)|=(2009387983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1410681039/10000000000 : ℝ)|^67 ≤ (1526205334229/20000000000000 : ℝ)^51
        have hw : |(1410681039/10000000000 : ℝ)|=(1410681039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305058_s2_s2_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1339474517/5000000000 : ℝ)*x 0 + (2155044261/2500000000 : ℝ)*x 1 + (-7/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339474517/5000000000 : ℝ)^67 ≤ (17721575058593/100000000000000 : ℝ)^51 := by
    have hnat : (1339474517 : ℕ)^67*100000000000000^51 ≤ 17721575058593^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339474517 5000000000 17721575058593 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155044261/2500000000 : ℝ)^67 ≤ (20569606231839/25000000000000 : ℝ)^51 := by
    have hnat : (2155044261 : ℕ)^67*25000000000000^51 ≤ 20569606231839^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155044261 2500000000 20569606231839 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7/1250000000 : ℝ)^67 ≤ (361/25000000000000 : ℝ)^51 := by
    have hnat : (7 : ℕ)^67*25000000000000^51 ≤ 361^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7 1250000000 361 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339474517/5000000000 : ℝ), (2155044261/2500000000 : ℝ), (-7/1250000000 : ℝ)] ![(17721575058593/100000000000000 : ℝ), (20569606231839/25000000000000 : ℝ), (361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339474517/5000000000 : ℝ)|^67 ≤ (17721575058593/100000000000000 : ℝ)^51
        have hw : |(1339474517/5000000000 : ℝ)|=(1339474517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2155044261/2500000000 : ℝ)|^67 ≤ (20569606231839/25000000000000 : ℝ)^51
        have hw : |(2155044261/2500000000 : ℝ)|=(2155044261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7/1250000000 : ℝ)|^67 ≤ (361/25000000000000 : ℝ)^51
        have hw : |(-7/1250000000 : ℝ)|=(7/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305058_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((11111/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11111/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39933/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39933/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-70233/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-70233/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18423/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18423/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63329/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63329/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-10107/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-10107/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (11111/12500 : ℝ) ^ (133/32 : ℝ) ≤ (61288540324677778133/100000000000000000000 : ℝ) := by
    have hpowers : (11111/12500 : ℝ)^133 ≤ (61288540324677778133/100000000000000000000 : ℝ)^32 := by
      have hnat : (11111 : ℕ)^133*100000000000000000000^32 ≤ 61288540324677778133^32*12500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11111 12500 61288540324677778133 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11111/12500 : ℝ)) (X := (61288540324677778133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (161288540324677778133/100000000000000000000 : ℝ) ≤ (11218885536837657/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (161288540324677778133/100000000000000000000 : ℝ)^32 ≤ (11218885536837657/10000000000000000 : ℝ)^133 := by
      have hnat : (161288540324677778133 : ℕ)^32*10000000000000000^133 ≤ 11218885536837657^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        161288540324677778133 100000000000000000000 11218885536837657 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11218885536837657/10000000000000000 : ℝ)) (X := (161288540324677778133/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (111288540324677778133/50000000000000000000 : ℝ) ≤ (12122838424352349/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (111288540324677778133/50000000000000000000 : ℝ)^32 ≤ (12122838424352349/10000000000000000 : ℝ)^133 := by
      have hnat : (111288540324677778133 : ℕ)^32*10000000000000000^133 ≤ 12122838424352349^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111288540324677778133 50000000000000000000 12122838424352349 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12122838424352349/10000000000000000 : ℝ)) (X := (111288540324677778133/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1218885536837657/8888800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(225988221878673/2222200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (11111/12500 : ℝ)) (alpha := (1218885536837657/8888800000000000 : ℝ)) (beta := (225988221878673/2222200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11111/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1218885536837657/8888800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(225988221878673/2222200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (39933/50000 : ℝ) ^ (133/32 : ℝ) ≤ (39281836840316592953/100000000000000000000 : ℝ) := by
    have hpowers : (39933/50000 : ℝ)^133 ≤ (39281836840316592953/100000000000000000000 : ℝ)^32 := by
      have hnat : (39933 : ℕ)^133*100000000000000000000^32 ≤ 39281836840316592953^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39933 50000 39281836840316592953 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39933/50000 : ℝ)) (X := (39281836840316592953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (139281836840316592953/100000000000000000000 : ℝ) ≤ (10829819781620053/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (139281836840316592953/100000000000000000000 : ℝ)^32 ≤ (10829819781620053/10000000000000000 : ℝ)^133 := by
      have hnat : (139281836840316592953 : ℕ)^32*10000000000000000^133 ≤ 10829819781620053^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139281836840316592953 100000000000000000000 10829819781620053 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10829819781620053/10000000000000000 : ℝ)) (X := (139281836840316592953/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (89281836840316592953/50000000000000000000 : ℝ) ≤ (11496927731993167/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (89281836840316592953/50000000000000000000 : ℝ)^32 ≤ (11496927731993167/10000000000000000 : ℝ)^133 := by
      have hnat : (89281836840316592953 : ℕ)^32*10000000000000000^133 ≤ 11496927731993167^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89281836840316592953 50000000000000000000 11496927731993167 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11496927731993167/10000000000000000 : ℝ)) (X := (89281836840316592953/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(276606593873351/2662200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(111184658395519/1331100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (39933/50000 : ℝ)) (alpha := (276606593873351/2662200000000000 : ℝ)) (beta := (111184658395519/1331100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39933/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(276606593873351/2662200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(111184658395519/1331100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (70233/100000 : ℝ) ^ (133/32 : ℝ) ≤ (4604865396498440603/20000000000000000000 : ℝ) := by
    have hpowers : (70233/100000 : ℝ)^133 ≤ (4604865396498440603/20000000000000000000 : ℝ)^32 := by
      have hnat : (70233 : ℕ)^133*20000000000000000000^32 ≤ 4604865396498440603^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70233 100000 4604865396498440603 20000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70233/100000 : ℝ)) (X := (4604865396498440603/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (24604865396498440603/20000000000000000000 : ℝ) ≤ (5255596003881269/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (24604865396498440603/20000000000000000000 : ℝ)^32 ≤ (5255596003881269/5000000000000000 : ℝ)^133 := by
      have hnat : (24604865396498440603 : ℕ)^32*5000000000000000^133 ≤ 5255596003881269^133*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24604865396498440603 20000000000000000000 5255596003881269 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5255596003881269/5000000000000000 : ℝ)) (X := (24604865396498440603/20000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (14604865396498440603/10000000000000000000 : ℝ) ≤ (10954141837218593/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (14604865396498440603/10000000000000000000 : ℝ)^32 ≤ (10954141837218593/10000000000000000 : ℝ)^133 := by
      have hnat : (14604865396498440603 : ℕ)^32*10000000000000000^133 ≤ 10954141837218593^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14604865396498440603 10000000000000000000 10954141837218593 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10954141837218593/10000000000000000 : ℝ)) (X := (14604865396498440603/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(85198667960423/1170550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(88589965891211/1404660000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (70233/100000 : ℝ)) (alpha := (85198667960423/1170550000000000 : ℝ)) (beta := (88589965891211/1404660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (70233/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(85198667960423/1170550000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(88589965891211/1404660000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1643553799/5000000000 : ℝ)*X 0 0+(1589825011/5000000000 : ℝ)*X 0 1+(-6310519199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((3277155121/10000000000 : ℝ)*X 1 0+(-392653817/1250000000 : ℝ)*X 1 1+(-6349515189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5880725731/10000000000 : ℝ)*X 2 0+(643183381/1250000000 : ℝ)*X 2 1+(152351257/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-65640921/250000000 : ℝ)*X 0 0+(2280235221/10000000000 : ℝ)*X 0 1+(-748936623/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2847178627/10000000000 : ℝ)*X 1 0+(-452112153/2000000000 : ℝ)*X 1 1+(-7340903573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4959061299/10000000000 : ℝ)*X 2 0+(3032007681/5000000000 : ℝ)*X 2 1+(756826457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3182939901/10000000000 : ℝ)*X 0 0+(825858447/1000000000 : ℝ)*X 0 1+(-5627/5000000000 : ℝ)*X 0 2+(3182939901/10000000000 : ℝ)*X 1 0+(825858447/1000000000 : ℝ)*X 1 1+(-5627/5000000000 : ℝ)*X 1 2+(3182939901/10000000000 : ℝ)*X 2 0+(825858447/1000000000 : ℝ)*X 2 1+(-5627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-2652951159/10000000000 : ℝ)*X 0 0+(1396277597/5000000000 : ℝ)*X 0 1+(-1775463833/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2729005421/10000000000 : ℝ)*X 1 0+(-2904766753/10000000000 : ℝ)*X 1 1+(-6961074637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6419321151/10000000000 : ℝ)*X 2 0+(38779757/78125000 : ℝ)*X 2 1+(910789061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-667833177/2000000000 : ℝ)*X 0 0+(655170311/2000000000 : ℝ)*X 0 1+(-1237934223/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3485588561/10000000000 : ℝ)*X 1 0+(-164793131/500000000 : ℝ)*X 1 1+(-6051308101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((870609779/1250000000 : ℝ)*X 2 0+(2009387983/5000000000 : ℝ)*X 2 1+(1410681039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1339474517/5000000000 : ℝ)*X 0 0+(2155044261/2500000000 : ℝ)*X 0 1+(-7/1250000000 : ℝ)*X 0 2+(1339474517/5000000000 : ℝ)*X 1 0+(2155044261/2500000000 : ℝ)*X 1 1+(-7/1250000000 : ℝ)*X 1 2+(1339474517/5000000000 : ℝ)*X 2 0+(2155044261/2500000000 : ℝ)*X 2 1+(-7/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305058_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((18423/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18423/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13521453191670824201290673699/750667159920000000000000000000000 : ℝ) := by norm_num
    linear_combination (639527960447/1000000000000 : ℝ)*(base7) + (266089403829/1000000000000 : ℝ)*(base60) + (651013609173/200000000000 : ℝ)*(major_s2_0) + (651013609173/200000000000 : ℝ)*(major_s2_1) + (651013609173/200000000000 : ℝ)*(major_s2_2) + (34831323/1000000000000 : ℝ)*(sp_s2_2) + (1991546228667/500000000000 : ℝ)*(sp_s2_7) + (3983092528207/1000000000000 : ℝ)*(sp_s2_8) + (3983167821947/1000000000000 : ℝ)*(sp_s2_9) + (2768023377523/1000000000000 : ℝ)*(sp_s2_13) + (127400891/1000000000000 : ℝ)*(sp_s2_14) + (63665009/500000000000 : ℝ)*(sp_s2_15) + (8602477/500000000000 : ℝ)*(sp_s2_16) + (1683433/1000000000000 : ℝ)*(sp_s2_27) + (532124275127/250000000000 : ℝ)*(f.failure) + (159328794329/40000000000 : ℝ)*(f.sum) + (755606468371418711/4154984280000000000000000000000 : ℝ)*base63 + (23249824722831/93644000000000000000000000 : ℝ)*base64 + (21490245116957/88740000000000000000000000 : ℝ)*base67 + (2900328302411/234110000000000000000000000 : ℝ)*base68 + (48134900995080217/1015100960000000000000000000000 : ℝ)*base70 + (99168660821577/444440000000000000000000000 : ℝ)*base73 + (44666975377021/177480000000000000000000000 : ℝ)*base75 + (121967374492403/1777760000000000000000000000 : ℝ)*base76 + (32202416627146219/394396056000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (393/3125000000000000 : ℝ)*base86 + (393/3125000000000000 : ℝ)*base88 + (393/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63329/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63329/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1142343387661289762099/58527500000000000000000000 : ℝ) := by norm_num
    linear_combination (3686984620177/1000000000000 : ℝ)*(base5) + (221492593027/500000000000 : ℝ)*(base7) + (17829903899/6250000000 : ℝ)*(base60) + (992196690923/200000000000 : ℝ)*(major_s2_0) + (992196690923/200000000000 : ℝ)*(major_s2_1) + (992196690923/200000000000 : ℝ)*(major_s2_2) + (3762999/1000000000000 : ℝ)*(sp_s2_0) + (86947967/1000000000000 : ℝ)*(sp_s2_1) + (7064323/1000000000000 : ℝ)*(sp_s2_2) + (16262981/125000000000 : ℝ)*(sp_s2_8) + (6401986294871/1000000000000 : ℝ)*(sp_s2_14) + (1280354601211/200000000000 : ℝ)*(sp_s2_15) + (2522238963431/250000000000 : ℝ)*(sp_s2_16) + (11759999/1000000000000 : ℝ)*(sp_s2_23) + (1621999717061/500000000000 : ℝ)*(f.failure) + (640199005787/100000000000 : ℝ)*(f.sum) + (4559700114718348729/12464952840000000000000000000000 : ℝ)*base62 + (218965149004867/1404660000000000000000000000 : ℝ)*base64 + (59015837304757/266220000000000000000000000 : ℝ)*base66 + (41220628186067/234110000000000000000000000 : ℝ)*base68 + (974235960629679701/3045302880000000000000000000000 : ℝ)*base70 + (82710480791133/444440000000000000000000000 : ℝ)*base72 + (338361696845953/532440000000000000000000000 : ℝ)*base75 + (1080910849449619/1777760000000000000000000000 : ℝ)*base77 + (738078465255750143/5915940840000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (2837/3125000000000000 : ℝ)*base86 + (2837/3125000000000000 : ℝ)*base88 + (2837/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-10107/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-10107/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5553364269337059/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (41384507561/200000000000 : ℝ)*(base7) + (253177/1000000000000 : ℝ)*(base33) + (273053/1000000000000 : ℝ)*(base44) + (91530328353/1000000000000 : ℝ)*(base60) + (3896286774607/1000000000000 : ℝ)*(major_s2_0) + (3896286754731/1000000000000 : ℝ)*(major_s2_1) + (487035878473/125000000000 : ℝ)*(major_s2_2) + (64112343/1000000000000 : ℝ)*(sp_s2_2) + (16818189/100000000000 : ℝ)*(sp_s2_13) + (14370323/1000000000000 : ℝ)*(sp_s2_16) + (2557935906191/500000000000 : ℝ)*(sp_s2_21) + (5115871286153/1000000000000 : ℝ)*(sp_s2_22) + (5115793076539/1000000000000 : ℝ)*(sp_s2_23) + (1377272936161/500000000000 : ℝ)*(sp_s2_27) + (2547791789459/1000000000000 : ℝ)*(f.failure) + (2557935906191/500000000000 : ℝ)*(f.sum) + (2876901398596065341/20774921400000000000000000000000 : ℝ)*base63 + (70754096021081/351165000000000000000000000 : ℝ)*base64 + (101818110720397/443700000000000000000000000 : ℝ)*base66 + (108117984811537/1170550000000000000000000000 : ℝ)*base68 + (1260757430533984327/15226514400000000000000000000000 : ℝ)*base71 + (314754907333589/2222200000000000000000000000 : ℝ)*base72 + (34011009481553/887400000000000000000000000 : ℝ)*base74 + (1688043102108521/8888800000000000000000000000 : ℝ)*base76 + (10938421211174213/9859901400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (439/3125000000000000 : ℝ)*base86 + (439/3125000000000000 : ℝ)*base88 + (439/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((11111/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11111/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39933/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39933/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-70233/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-70233/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18423/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18423/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63329/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63329/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-10107/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-10107/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305058_s2 p hpa hpb X hX hprev1

#print axioms solution

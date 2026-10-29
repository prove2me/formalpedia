-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:47:51.350437+00:00
-- url     : https://prove2.me/submissions/e4ad6561-0e04-4409-9dab-de8ea8fa5dfa

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
theorem collision_support_c314062_s2_s2_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914707601/10000000000 : ℝ)*x 0 + (4899450463/10000000000 : ℝ)*x 1 + (-5557846313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914707601/10000000000 : ℝ)^75 ≤ (12229772634313/100000000000000 : ℝ)^59 := by
    have hnat : (1914707601 : ℕ)^75*100000000000000^59 ≤ 12229772634313^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914707601 10000000000 12229772634313 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899450463/10000000000 : ℝ)^75 ≤ (40375651150771/100000000000000 : ℝ)^59 := by
    have hnat : (4899450463 : ℕ)^75*100000000000000^59 ≤ 40375651150771^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899450463 10000000000 40375651150771 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5557846313/10000000000 : ℝ)^75 ≤ (1184864404869/2500000000000 : ℝ)^59 := by
    have hnat : (5557846313 : ℕ)^75*2500000000000^59 ≤ 1184864404869^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557846313 10000000000 1184864404869 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914707601/10000000000 : ℝ), (4899450463/10000000000 : ℝ), (-5557846313/10000000000 : ℝ)] ![(12229772634313/100000000000000 : ℝ), (40375651150771/100000000000000 : ℝ), (1184864404869/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914707601/10000000000 : ℝ)|^75 ≤ (12229772634313/100000000000000 : ℝ)^59
        have hw : |(-1914707601/10000000000 : ℝ)|=(1914707601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4899450463/10000000000 : ℝ)|^75 ≤ (40375651150771/100000000000000 : ℝ)^59
        have hw : |(4899450463/10000000000 : ℝ)|=(4899450463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5557846313/10000000000 : ℝ)|^75 ≤ (1184864404869/2500000000000 : ℝ)^59
        have hw : |(-5557846313/10000000000 : ℝ)|=(5557846313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2449441641/5000000000 : ℝ)*x 0 + (-191684737/1000000000 : ℝ)*x 1 + (-5556791419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2449441641/5000000000 : ℝ)^75 ≤ (40369709648371/100000000000000 : ℝ)^59 := by
    have hnat : (2449441641 : ℕ)^75*100000000000000^59 ≤ 40369709648371^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449441641 5000000000 40369709648371 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191684737/1000000000 : ℝ)^75 ≤ (6123574478063/50000000000000 : ℝ)^59 := by
    have hnat : (191684737 : ℕ)^75*50000000000000^59 ≤ 6123574478063^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191684737 1000000000 6123574478063 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5556791419/10000000000 : ℝ)^75 ≤ (11845785345833/25000000000000 : ℝ)^59 := by
    have hnat : (5556791419 : ℕ)^75*25000000000000^59 ≤ 11845785345833^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5556791419 10000000000 11845785345833 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2449441641/5000000000 : ℝ), (-191684737/1000000000 : ℝ), (-5556791419/10000000000 : ℝ)] ![(40369709648371/100000000000000 : ℝ), (6123574478063/50000000000000 : ℝ), (11845785345833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2449441641/5000000000 : ℝ)|^75 ≤ (40369709648371/100000000000000 : ℝ)^59
        have hw : |(2449441641/5000000000 : ℝ)|=(2449441641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191684737/1000000000 : ℝ)|^75 ≤ (6123574478063/50000000000000 : ℝ)^59
        have hw : |(-191684737/1000000000 : ℝ)|=(191684737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5556791419/10000000000 : ℝ)|^75 ≤ (11845785345833/25000000000000 : ℝ)^59
        have hw : |(-5556791419/10000000000 : ℝ)|=(5556791419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1009091973/2000000000 : ℝ)*x 0 + (5044660353/10000000000 : ℝ)*x 1 + (238699621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009091973/2000000000 : ℝ)^75 ≤ (41911332556949/100000000000000 : ℝ)^59 := by
    have hnat : (1009091973 : ℕ)^75*100000000000000^59 ≤ 41911332556949^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009091973 2000000000 41911332556949 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5044660353/10000000000 : ℝ)^75 ≤ (20951445178637/50000000000000 : ℝ)^59 := by
    have hnat : (5044660353 : ℕ)^75*50000000000000^59 ≤ 20951445178637^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044660353 10000000000 20951445178637 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238699621/1000000000 : ℝ)^75 ≤ (4046444266673/25000000000000 : ℝ)^59 := by
    have hnat : (238699621 : ℕ)^75*25000000000000^59 ≤ 4046444266673^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238699621 1000000000 4046444266673 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1009091973/2000000000 : ℝ), (5044660353/10000000000 : ℝ), (238699621/1000000000 : ℝ)] ![(41911332556949/100000000000000 : ℝ), (20951445178637/50000000000000 : ℝ), (4046444266673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1009091973/2000000000 : ℝ)|^75 ≤ (41911332556949/100000000000000 : ℝ)^59
        have hw : |(1009091973/2000000000 : ℝ)|=(1009091973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5044660353/10000000000 : ℝ)|^75 ≤ (20951445178637/50000000000000 : ℝ)^59
        have hw : |(5044660353/10000000000 : ℝ)|=(5044660353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238699621/1000000000 : ℝ)|^75 ≤ (4046444266673/25000000000000 : ℝ)^59
        have hw : |(238699621/1000000000 : ℝ)|=(238699621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1725785077/10000000000 : ℝ)*x 0 + (1155918983/2500000000 : ℝ)*x 1 + (-2979006949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725785077/10000000000 : ℝ)^75 ≤ (5358433620803/50000000000000 : ℝ)^59 := by
    have hnat : (1725785077 : ℕ)^75*50000000000000^59 ≤ 5358433620803^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725785077 10000000000 5358433620803 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155918983/2500000000 : ℝ)^75 ≤ (18754544193083/50000000000000 : ℝ)^59 := by
    have hnat : (1155918983 : ℕ)^75*50000000000000^59 ≤ 18754544193083^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155918983 2500000000 18754544193083 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2979006949/5000000000 : ℝ)^75 ≤ (51774044356753/100000000000000 : ℝ)^59 := by
    have hnat : (2979006949 : ℕ)^75*100000000000000^59 ≤ 51774044356753^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979006949 5000000000 51774044356753 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1725785077/10000000000 : ℝ), (1155918983/2500000000 : ℝ), (-2979006949/5000000000 : ℝ)] ![(5358433620803/50000000000000 : ℝ), (18754544193083/50000000000000 : ℝ), (51774044356753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1725785077/10000000000 : ℝ)|^75 ≤ (5358433620803/50000000000000 : ℝ)^59
        have hw : |(-1725785077/10000000000 : ℝ)|=(1725785077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155918983/2500000000 : ℝ)|^75 ≤ (18754544193083/50000000000000 : ℝ)^59
        have hw : |(1155918983/2500000000 : ℝ)|=(1155918983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2979006949/5000000000 : ℝ)|^75 ≤ (51774044356753/100000000000000 : ℝ)^59
        have hw : |(-2979006949/5000000000 : ℝ)|=(2979006949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (980265721/2000000000 : ℝ)*x 0 + (-190331341/1250000000 : ℝ)*x 1 + (-2919591447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980265721/2000000000 : ℝ)^75 ≤ (40395326951519/100000000000000 : ℝ)^59 := by
    have hnat : (980265721 : ℕ)^75*100000000000000^59 ≤ 40395326951519^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980265721 2000000000 40395326951519 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190331341/1250000000 : ℝ)^75 ≤ (1827942680969/20000000000000 : ℝ)^59 := by
    have hnat : (190331341 : ℕ)^75*20000000000000^59 ≤ 1827942680969^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190331341 1250000000 1827942680969 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2919591447/5000000000 : ℝ)^75 ≤ (10092991925089/20000000000000 : ℝ)^59 := by
    have hnat : (2919591447 : ℕ)^75*20000000000000^59 ≤ 10092991925089^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919591447 5000000000 10092991925089 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980265721/2000000000 : ℝ), (-190331341/1250000000 : ℝ), (-2919591447/5000000000 : ℝ)] ![(40395326951519/100000000000000 : ℝ), (1827942680969/20000000000000 : ℝ), (10092991925089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980265721/2000000000 : ℝ)|^75 ≤ (40395326951519/100000000000000 : ℝ)^59
        have hw : |(980265721/2000000000 : ℝ)|=(980265721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190331341/1250000000 : ℝ)|^75 ≤ (1827942680969/20000000000000 : ℝ)^59
        have hw : |(-190331341/1250000000 : ℝ)|=(190331341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2919591447/5000000000 : ℝ)|^75 ≤ (10092991925089/20000000000000 : ℝ)^59
        have hw : |(-2919591447/5000000000 : ℝ)|=(2919591447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4928737447/10000000000 : ℝ)*x 0 + (2784111299/5000000000 : ℝ)*x 1 + (1862842617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4928737447/10000000000 : ℝ)^75 ≤ (20341349982189/50000000000000 : ℝ)^59 := by
    have hnat : (4928737447 : ℕ)^75*50000000000000^59 ≤ 20341349982189^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4928737447 10000000000 20341349982189 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2784111299/5000000000 : ℝ)^75 ≤ (47507084123913/100000000000000 : ℝ)^59 := by
    have hnat : (2784111299 : ℕ)^75*100000000000000^59 ≤ 47507084123913^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784111299 5000000000 47507084123913 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862842617/10000000000 : ℝ)^75 ≤ (1181021589491/10000000000000 : ℝ)^59 := by
    have hnat : (1862842617 : ℕ)^75*10000000000000^59 ≤ 1181021589491^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862842617 10000000000 1181021589491 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4928737447/10000000000 : ℝ), (2784111299/5000000000 : ℝ), (1862842617/10000000000 : ℝ)] ![(20341349982189/50000000000000 : ℝ), (47507084123913/100000000000000 : ℝ), (1181021589491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4928737447/10000000000 : ℝ)|^75 ≤ (20341349982189/50000000000000 : ℝ)^59
        have hw : |(4928737447/10000000000 : ℝ)|=(4928737447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2784111299/5000000000 : ℝ)|^75 ≤ (47507084123913/100000000000000 : ℝ)^59
        have hw : |(2784111299/5000000000 : ℝ)|=(2784111299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1862842617/10000000000 : ℝ)|^75 ≤ (1181021589491/10000000000000 : ℝ)^59
        have hw : |(1862842617/10000000000 : ℝ)|=(1862842617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5243339277/10000000000 : ℝ)*x 0 + (2907067013/5000000000 : ℝ)*x 1 + (-532226331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243339277/10000000000 : ℝ)^75 ≤ (1760473257371/4000000000000 : ℝ)^59 := by
    have hnat : (5243339277 : ℕ)^75*4000000000000^59 ≤ 1760473257371^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243339277 10000000000 1760473257371 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2907067013/5000000000 : ℝ)^75 ≤ (5018992824051/10000000000000 : ℝ)^59 := by
    have hnat : (2907067013 : ℕ)^75*10000000000000^59 ≤ 5018992824051^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2907067013 5000000000 5018992824051 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532226331/5000000000 : ℝ)^75 ≤ (5798240307381/100000000000000 : ℝ)^59 := by
    have hnat : (532226331 : ℕ)^75*100000000000000^59 ≤ 5798240307381^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532226331 5000000000 5798240307381 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243339277/10000000000 : ℝ), (2907067013/5000000000 : ℝ), (-532226331/5000000000 : ℝ)] ![(1760473257371/4000000000000 : ℝ), (5018992824051/10000000000000 : ℝ), (5798240307381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243339277/10000000000 : ℝ)|^75 ≤ (1760473257371/4000000000000 : ℝ)^59
        have hw : |(5243339277/10000000000 : ℝ)|=(5243339277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2907067013/5000000000 : ℝ)|^75 ≤ (5018992824051/10000000000000 : ℝ)^59
        have hw : |(2907067013/5000000000 : ℝ)|=(2907067013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532226331/5000000000 : ℝ)|^75 ≤ (5798240307381/100000000000000 : ℝ)^59
        have hw : |(-532226331/5000000000 : ℝ)|=(532226331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1472927379/10000000000 : ℝ)*x 0 + (96951433/200000000 : ℝ)*x 1 + (-5924582371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472927379/10000000000 : ℝ)^75 ≤ (1095250360831/12500000000000 : ℝ)^59 := by
    have hnat : (1472927379 : ℕ)^75*12500000000000^59 ≤ 1095250360831^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472927379 10000000000 1095250360831 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96951433/200000000 : ℝ)^75 ≤ (2489560538233/6250000000000 : ℝ)^59 := by
    have hnat : (96951433 : ℕ)^75*6250000000000^59 ≤ 2489560538233^59*200000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96951433 200000000 2489560538233 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5924582371/10000000000 : ℝ)^75 ≤ (5140502849083/10000000000000 : ℝ)^59 := by
    have hnat : (5924582371 : ℕ)^75*10000000000000^59 ≤ 5140502849083^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5924582371 10000000000 5140502849083 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1472927379/10000000000 : ℝ), (96951433/200000000 : ℝ), (-5924582371/10000000000 : ℝ)] ![(1095250360831/12500000000000 : ℝ), (2489560538233/6250000000000 : ℝ), (5140502849083/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1472927379/10000000000 : ℝ)|^75 ≤ (1095250360831/12500000000000 : ℝ)^59
        have hw : |(-1472927379/10000000000 : ℝ)|=(1472927379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96951433/200000000 : ℝ)|^75 ≤ (2489560538233/6250000000000 : ℝ)^59
        have hw : |(96951433/200000000 : ℝ)|=(96951433/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5924582371/10000000000 : ℝ)|^75 ≤ (5140502849083/10000000000000 : ℝ)^59
        have hw : |(-5924582371/10000000000 : ℝ)|=(5924582371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4683273943/10000000000 : ℝ)*x 0 + (-1784938327/10000000000 : ℝ)*x 1 + (-2929795633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4683273943/10000000000 : ℝ)^75 ≤ (19062377895261/50000000000000 : ℝ)^59 := by
    have hnat : (4683273943 : ℕ)^75*50000000000000^59 ≤ 19062377895261^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4683273943 10000000000 19062377895261 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784938327/10000000000 : ℝ)^75 ≤ (2796492037393/25000000000000 : ℝ)^59 := by
    have hnat : (1784938327 : ℕ)^75*25000000000000^59 ≤ 2796492037393^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784938327 10000000000 2796492037393 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2929795633/5000000000 : ℝ)^75 ≤ (10137855208347/20000000000000 : ℝ)^59 := by
    have hnat : (2929795633 : ℕ)^75*20000000000000^59 ≤ 10137855208347^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929795633 5000000000 10137855208347 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4683273943/10000000000 : ℝ), (-1784938327/10000000000 : ℝ), (-2929795633/5000000000 : ℝ)] ![(19062377895261/50000000000000 : ℝ), (2796492037393/25000000000000 : ℝ), (10137855208347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4683273943/10000000000 : ℝ)|^75 ≤ (19062377895261/50000000000000 : ℝ)^59
        have hw : |(4683273943/10000000000 : ℝ)|=(4683273943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784938327/10000000000 : ℝ)|^75 ≤ (2796492037393/25000000000000 : ℝ)^59
        have hw : |(-1784938327/10000000000 : ℝ)|=(1784938327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2929795633/5000000000 : ℝ)|^75 ≤ (10137855208347/20000000000000 : ℝ)^59
        have hw : |(-2929795633/5000000000 : ℝ)|=(2929795633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1374305457/2500000000 : ℝ)*x 0 + (4992989217/10000000000 : ℝ)*x 1 + (117150993/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374305457/2500000000 : ℝ)^75 ≤ (46738378200973/100000000000000 : ℝ)^59 := by
    have hnat : (1374305457 : ℕ)^75*100000000000000^59 ≤ 46738378200973^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374305457 2500000000 46738378200973 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992989217/10000000000 : ℝ)^75 ≤ (10339514085551/25000000000000 : ℝ)^59 := by
    have hnat : (4992989217 : ℕ)^75*25000000000000^59 ≤ 10339514085551^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992989217 10000000000 10339514085551 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117150993/625000000 : ℝ)^75 ≤ (5951782718437/50000000000000 : ℝ)^59 := by
    have hnat : (117150993 : ℕ)^75*50000000000000^59 ≤ 5951782718437^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117150993 625000000 5951782718437 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374305457/2500000000 : ℝ), (4992989217/10000000000 : ℝ), (117150993/625000000 : ℝ)] ![(46738378200973/100000000000000 : ℝ), (10339514085551/25000000000000 : ℝ), (5951782718437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374305457/2500000000 : ℝ)|^75 ≤ (46738378200973/100000000000000 : ℝ)^59
        have hw : |(1374305457/2500000000 : ℝ)|=(1374305457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992989217/10000000000 : ℝ)|^75 ≤ (10339514085551/25000000000000 : ℝ)^59
        have hw : |(4992989217/10000000000 : ℝ)|=(4992989217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117150993/625000000 : ℝ)|^75 ≤ (5951782718437/50000000000000 : ℝ)^59
        have hw : |(117150993/625000000 : ℝ)|=(117150993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5963366971/10000000000 : ℝ)*x 0 + (1271598867/2500000000 : ℝ)*x 1 + (-66749447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5963366971/10000000000 : ℝ)^75 ≤ (259165918087/500000000000 : ℝ)^59 := by
    have hnat : (5963366971 : ℕ)^75*500000000000^59 ≤ 259165918087^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963366971 10000000000 259165918087 500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271598867/2500000000 : ℝ)^75 ≤ (21172031640591/50000000000000 : ℝ)^59 := by
    have hnat : (1271598867 : ℕ)^75*50000000000000^59 ≤ 21172031640591^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271598867 2500000000 21172031640591 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66749447/625000000 : ℝ)^75 ≤ (291137654563/5000000000000 : ℝ)^59 := by
    have hnat : (66749447 : ℕ)^75*5000000000000^59 ≤ 291137654563^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66749447 625000000 291137654563 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5963366971/10000000000 : ℝ), (1271598867/2500000000 : ℝ), (-66749447/625000000 : ℝ)] ![(259165918087/500000000000 : ℝ), (21172031640591/50000000000000 : ℝ), (291137654563/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5963366971/10000000000 : ℝ)|^75 ≤ (259165918087/500000000000 : ℝ)^59
        have hw : |(5963366971/10000000000 : ℝ)|=(5963366971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271598867/2500000000 : ℝ)|^75 ≤ (21172031640591/50000000000000 : ℝ)^59
        have hw : |(1271598867/2500000000 : ℝ)|=(1271598867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66749447/625000000 : ℝ)|^75 ≤ (291137654563/5000000000000 : ℝ)^59
        have hw : |(-66749447/625000000 : ℝ)|=(66749447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1337445977/10000000000 : ℝ)*x 0 + (640010653/1250000000 : ℝ)*x 1 + (-2877800989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337445977/10000000000 : ℝ)^75 ≤ (7750580199329/100000000000000 : ℝ)^59 := by
    have hnat : (1337445977 : ℕ)^75*100000000000000^59 ≤ 7750580199329^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337445977 10000000000 7750580199329 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640010653/1250000000 : ℝ)^75 ≤ (42700907581361/100000000000000 : ℝ)^59 := by
    have hnat : (640010653 : ℕ)^75*100000000000000^59 ≤ 42700907581361^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640010653 1250000000 42700907581361 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2877800989/5000000000 : ℝ)^75 ≤ (49548512204549/100000000000000 : ℝ)^59 := by
    have hnat : (2877800989 : ℕ)^75*100000000000000^59 ≤ 49548512204549^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877800989 5000000000 49548512204549 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1337445977/10000000000 : ℝ), (640010653/1250000000 : ℝ), (-2877800989/5000000000 : ℝ)] ![(7750580199329/100000000000000 : ℝ), (42700907581361/100000000000000 : ℝ), (49548512204549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1337445977/10000000000 : ℝ)|^75 ≤ (7750580199329/100000000000000 : ℝ)^59
        have hw : |(-1337445977/10000000000 : ℝ)|=(1337445977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640010653/1250000000 : ℝ)|^75 ≤ (42700907581361/100000000000000 : ℝ)^59
        have hw : |(640010653/1250000000 : ℝ)|=(640010653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2877800989/5000000000 : ℝ)|^75 ≤ (49548512204549/100000000000000 : ℝ)^59
        have hw : |(-2877800989/5000000000 : ℝ)|=(2877800989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2742958119/5000000000 : ℝ)*x 0 + (-852994989/5000000000 : ℝ)*x 1 + (-2565795609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742958119/5000000000 : ℝ)^75 ≤ (23308111540543/50000000000000 : ℝ)^59 := by
    have hnat : (2742958119 : ℕ)^75*50000000000000^59 ≤ 23308111540543^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742958119 5000000000 23308111540543 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852994989/5000000000 : ℝ)^75 ≤ (528042543007/5000000000000 : ℝ)^59 := by
    have hnat : (852994989 : ℕ)^75*5000000000000^59 ≤ 528042543007^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852994989 5000000000 528042543007 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565795609/5000000000 : ℝ)^75 ≤ (42822926044857/100000000000000 : ℝ)^59 := by
    have hnat : (2565795609 : ℕ)^75*100000000000000^59 ≤ 42822926044857^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565795609 5000000000 42822926044857 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742958119/5000000000 : ℝ), (-852994989/5000000000 : ℝ), (-2565795609/5000000000 : ℝ)] ![(23308111540543/50000000000000 : ℝ), (528042543007/5000000000000 : ℝ), (42822926044857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742958119/5000000000 : ℝ)|^75 ≤ (23308111540543/50000000000000 : ℝ)^59
        have hw : |(2742958119/5000000000 : ℝ)|=(2742958119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852994989/5000000000 : ℝ)|^75 ≤ (528042543007/5000000000000 : ℝ)^59
        have hw : |(-852994989/5000000000 : ℝ)|=(852994989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2565795609/5000000000 : ℝ)|^75 ≤ (42822926044857/100000000000000 : ℝ)^59
        have hw : |(-2565795609/5000000000 : ℝ)|=(2565795609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4791695097/10000000000 : ℝ)*x 0 + (329094081/625000000 : ℝ)*x 1 + (2423524639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4791695097/10000000000 : ℝ)^75 ≤ (39250226942571/100000000000000 : ℝ)^59 := by
    have hnat : (4791695097 : ℕ)^75*100000000000000^59 ≤ 39250226942571^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791695097 10000000000 39250226942571 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329094081/625000000 : ℝ)^75 ≤ (44248481729981/100000000000000 : ℝ)^59 := by
    have hnat : (329094081 : ℕ)^75*100000000000000^59 ≤ 44248481729981^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329094081 625000000 44248481729981 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2423524639/10000000000 : ℝ)^75 ≤ (8250645657219/50000000000000 : ℝ)^59 := by
    have hnat : (2423524639 : ℕ)^75*50000000000000^59 ≤ 8250645657219^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423524639 10000000000 8250645657219 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4791695097/10000000000 : ℝ), (329094081/625000000 : ℝ), (2423524639/10000000000 : ℝ)] ![(39250226942571/100000000000000 : ℝ), (44248481729981/100000000000000 : ℝ), (8250645657219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4791695097/10000000000 : ℝ)|^75 ≤ (39250226942571/100000000000000 : ℝ)^59
        have hw : |(4791695097/10000000000 : ℝ)|=(4791695097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329094081/625000000 : ℝ)|^75 ≤ (44248481729981/100000000000000 : ℝ)^59
        have hw : |(329094081/625000000 : ℝ)|=(329094081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2423524639/10000000000 : ℝ)|^75 ≤ (8250645657219/50000000000000 : ℝ)^59
        have hw : |(2423524639/10000000000 : ℝ)|=(2423524639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s2_s2_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (37856431/62500000 : ℝ)*x 0 + (4893656909/10000000000 : ℝ)*x 1 + (-604345277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37856431/62500000 : ℝ)^75 ≤ (826097762117/1562500000000 : ℝ)^59 := by
    have hnat : (37856431 : ℕ)^75*1562500000000^59 ≤ 826097762117^59*62500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37856431 62500000 826097762117 1562500000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4893656909/10000000000 : ℝ)^75 ≤ (40314969579183/100000000000000 : ℝ)^59 := by
    have hnat : (4893656909 : ℕ)^75*100000000000000^59 ≤ 40314969579183^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893656909 10000000000 40314969579183 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604345277/5000000000 : ℝ)^75 ≤ (1703693406649/25000000000000 : ℝ)^59 := by
    have hnat : (604345277 : ℕ)^75*25000000000000^59 ≤ 1703693406649^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604345277 5000000000 1703693406649 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(37856431/62500000 : ℝ), (4893656909/10000000000 : ℝ), (-604345277/5000000000 : ℝ)] ![(826097762117/1562500000000 : ℝ), (40314969579183/100000000000000 : ℝ), (1703693406649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(37856431/62500000 : ℝ)|^75 ≤ (826097762117/1562500000000 : ℝ)^59
        have hw : |(37856431/62500000 : ℝ)|=(37856431/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4893656909/10000000000 : ℝ)|^75 ≤ (40314969579183/100000000000000 : ℝ)^59
        have hw : |(4893656909/10000000000 : ℝ)|=(4893656909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-604345277/5000000000 : ℝ)|^75 ≤ (1703693406649/25000000000000 : ℝ)^59
        have hw : |(-604345277/5000000000 : ℝ)|=(604345277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314062_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((2373/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59533/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44133/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44133/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28871/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28871/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14507/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14507/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2157/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2157/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (2373/4000 : ℝ) ^ (37/8 : ℝ) ≤ (111720942894290007/1250000000000000000 : ℝ) := by
    have hpowers : (2373/4000 : ℝ)^37 ≤ (111720942894290007/1250000000000000000 : ℝ)^8 := by
      have hnat : (2373 : ℕ)^37*1250000000000000000^8 ≤ 111720942894290007^8*4000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2373 4000 111720942894290007 1250000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2373/4000 : ℝ)) (X := (111720942894290007/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (1361720942894290007/1250000000000000000 : ℝ) ≤ (127335213833023/125000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1361720942894290007/1250000000000000000 : ℝ)^8 ≤ (127335213833023/125000000000000 : ℝ)^37 := by
      have hnat : (1361720942894290007 : ℕ)^8*125000000000000^37 ≤ 127335213833023^37*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1361720942894290007 1250000000000000000 127335213833023 125000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (127335213833023/125000000000000 : ℝ)) (X := (1361720942894290007/1250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (736720942894290007/625000000000000000 : ℝ) ≤ (2590495362483733/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (736720942894290007/625000000000000000 : ℝ)^8 ≤ (2590495362483733/2500000000000000 : ℝ)^37 := by
      have hnat : (736720942894290007 : ℕ)^8*2500000000000000^37 ≤ 2590495362483733^37*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        736720942894290007 625000000000000000 2590495362483733 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2590495362483733/2500000000000000 : ℝ)) (X := (736720942894290007/625000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2335213833023/74156250000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(43791085823273/1483125000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (2373/4000 : ℝ)) (alpha := (2335213833023/74156250000000 : ℝ)) (beta := (43791085823273/1483125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2373/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2335213833023/74156250000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(43791085823273/1483125000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (59533/100000 : ℝ) ^ (37/8 : ℝ) ≤ (4541765239519942799/50000000000000000000 : ℝ) := by
    have hpowers : (59533/100000 : ℝ)^37 ≤ (4541765239519942799/50000000000000000000 : ℝ)^8 := by
      have hnat : (59533 : ℕ)^37*50000000000000000000^8 ≤ 4541765239519942799^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59533 100000 4541765239519942799 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59533/100000 : ℝ)) (X := (4541765239519942799/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (54541765239519942799/50000000000000000000 : ℝ) ≤ (1018976452903669/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (54541765239519942799/50000000000000000000 : ℝ)^8 ≤ (1018976452903669/1000000000000000 : ℝ)^37 := by
      have hnat : (54541765239519942799 : ℕ)^8*1000000000000000^37 ≤ 1018976452903669^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54541765239519942799 50000000000000000000 1018976452903669 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1018976452903669/1000000000000000 : ℝ)) (X := (54541765239519942799/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (29541765239519942799/25000000000000000000 : ℝ) ≤ (5183760272109589/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (29541765239519942799/25000000000000000000 : ℝ)^8 ≤ (5183760272109589/5000000000000000 : ℝ)^37 := by
      have hnat : (29541765239519942799 : ℕ)^8*5000000000000000^37 ≤ 5183760272109589^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29541765239519942799 25000000000000000000 5183760272109589 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5183760272109589/5000000000000000 : ℝ)) (X := (29541765239519942799/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(18976452903669/595330000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(22219501897811/744162500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (59533/100000 : ℝ)) (alpha := (18976452903669/595330000000000 : ℝ)) (beta := (22219501897811/744162500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (59533/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(18976452903669/595330000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(22219501897811/744162500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (44133/100000 : ℝ) ^ (37/8 : ℝ) ≤ (2275259609021487347/100000000000000000000 : ℝ) := by
    have hpowers : (44133/100000 : ℝ)^37 ≤ (2275259609021487347/100000000000000000000 : ℝ)^8 := by
      have hnat : (44133 : ℕ)^37*100000000000000000000^8 ≤ 2275259609021487347^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44133 100000 2275259609021487347 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44133/100000 : ℝ)) (X := (2275259609021487347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (102275259609021487347/100000000000000000000 : ℝ) ≤ (10048761995959111/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (102275259609021487347/100000000000000000000 : ℝ)^8 ≤ (10048761995959111/10000000000000000 : ℝ)^37 := by
      have hnat : (102275259609021487347 : ℕ)^8*10000000000000000^37 ≤ 10048761995959111^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102275259609021487347 100000000000000000000 10048761995959111 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048761995959111/10000000000000000 : ℝ)) (X := (102275259609021487347/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (52275259609021487347/50000000000000000000 : ℝ) ≤ (5048340516132401/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (52275259609021487347/50000000000000000000 : ℝ)^8 ≤ (5048340516132401/5000000000000000 : ℝ)^37 := by
      have hnat : (52275259609021487347 : ℕ)^8*5000000000000000^37 ≤ 5048340516132401^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52275259609021487347 50000000000000000000 5048340516132401 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048340516132401/5000000000000000 : ℝ)) (X := (52275259609021487347/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(16253998653037/1471100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(15973012101897/1471100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (44133/100000 : ℝ)) (alpha := (16253998653037/1471100000000000 : ℝ)) (beta := (15973012101897/1471100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44133/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(16253998653037/1471100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(15973012101897/1471100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1914707601/10000000000 : ℝ)*X 0 0+(4899450463/10000000000 : ℝ)*X 0 1+(-5557846313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2449441641/5000000000 : ℝ)*X 1 0+(-191684737/1000000000 : ℝ)*X 1 1+(-5556791419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1009091973/2000000000 : ℝ)*X 2 0+(5044660353/10000000000 : ℝ)*X 2 1+(238699621/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1725785077/10000000000 : ℝ)*X 0 0+(1155918983/2500000000 : ℝ)*X 0 1+(-2979006949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((980265721/2000000000 : ℝ)*X 1 0+(-190331341/1250000000 : ℝ)*X 1 1+(-2919591447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4928737447/10000000000 : ℝ)*X 2 0+(2784111299/5000000000 : ℝ)*X 2 1+(1862842617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5243339277/10000000000 : ℝ)*X 0 0+(2907067013/5000000000 : ℝ)*X 0 1+(-532226331/5000000000 : ℝ)*X 0 2+(5243339277/10000000000 : ℝ)*X 1 0+(2907067013/5000000000 : ℝ)*X 1 1+(-532226331/5000000000 : ℝ)*X 1 2+(5243339277/10000000000 : ℝ)*X 2 0+(2907067013/5000000000 : ℝ)*X 2 1+(-532226331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1472927379/10000000000 : ℝ)*X 0 0+(96951433/200000000 : ℝ)*X 0 1+(-5924582371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4683273943/10000000000 : ℝ)*X 1 0+(-1784938327/10000000000 : ℝ)*X 1 1+(-2929795633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1374305457/2500000000 : ℝ)*X 2 0+(4992989217/10000000000 : ℝ)*X 2 1+(117150993/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5963366971/10000000000 : ℝ)*X 0 0+(1271598867/2500000000 : ℝ)*X 0 1+(-66749447/625000000 : ℝ)*X 0 2+(5963366971/10000000000 : ℝ)*X 1 0+(1271598867/2500000000 : ℝ)*X 1 1+(-66749447/625000000 : ℝ)*X 1 2+(5963366971/10000000000 : ℝ)*X 2 0+(1271598867/2500000000 : ℝ)*X 2 1+(-66749447/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1337445977/10000000000 : ℝ)*X 0 0+(640010653/1250000000 : ℝ)*X 0 1+(-2877800989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2742958119/5000000000 : ℝ)*X 1 0+(-852994989/5000000000 : ℝ)*X 1 1+(-2565795609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4791695097/10000000000 : ℝ)*X 2 0+(329094081/625000000 : ℝ)*X 2 1+(2423524639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((37856431/62500000 : ℝ)*X 0 0+(4893656909/10000000000 : ℝ)*X 0 1+(-604345277/5000000000 : ℝ)*X 0 2+(37856431/62500000 : ℝ)*X 1 0+(4893656909/10000000000 : ℝ)*X 1 1+(-604345277/5000000000 : ℝ)*X 1 2+(37856431/62500000 : ℝ)*X 2 0+(4893656909/10000000000 : ℝ)*X 2 1+(-604345277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((28871/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28871/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4262844640689129206988993/1094737453750000000000000000000 : ℝ) := by norm_num
    linear_combination (207699584381/250000000000 : ℝ)*(base39) + (326269731747/500000000000 : ℝ)*(base49) + (87809979271/500000000000 : ℝ)*(base60) + (5184288467079/500000000000 : ℝ)*(major_s2_0) + (5184288467079/500000000000 : ℝ)*(major_s2_1) + (5184288467079/500000000000 : ℝ)*(major_s2_2) + (2462843/62500000000 : ℝ)*(sp_s2_0) + (2234661/250000000000 : ℝ)*(sp_s2_1) + (735564404903/50000000000 : ℝ)*(sp_s2_7) + (367781175367/25000000000 : ℝ)*(sp_s2_8) + (3677815589609/250000000000 : ℝ)*(sp_s2_9) + (301291253339/50000000000 : ℝ)*(sp_s2_13) + (4471889/62500000000 : ℝ)*(sp_s2_15) + (8143139/125000000000 : ℝ)*(sp_s2_23) + (301291253339/50000000000 : ℝ)*(f.failure) + (14711327503547/1000000000000 : ℝ)*(f.sum) + (5371344950728963311/43789498150000000000000000000000 : ℝ)*base62 + (41203578961943/735550000000000000000000000 : ℝ)*base65 + (244177845241239/372081250000000000000000000 : ℝ)*base67 + (546853367307577/735550000000000000000000000 : ℝ)*base68 + (1935104910112882429/2909100250000000000000000000000 : ℝ)*base71 + (12397787825641/61796875000000000000000000 : ℝ)*base73 + (108708626845613/297665000000000000000000000 : ℝ)*base74 + (2337713709843/6179687500000000000000000 : ℝ)*base76 + (712369294087748711/1839476679687500000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1609/5000000000000000 : ℝ)*base86 + (1609/5000000000000000 : ℝ)*base88 + (1609/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14507/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14507/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (52015147058946565738204866947/7663162176250000000000000000000000 : ℝ) := by norm_num
    linear_combination (406855632323/500000000000 : ℝ)*(base39) + (28511484311/40000000000 : ℝ)*(base49) + (477321/500000000000 : ℝ)*(base60) + (5282108187233/500000000000 : ℝ)*(major_s2_0) + (5282108187233/500000000000 : ℝ)*(major_s2_1) + (5282108187233/500000000000 : ℝ)*(major_s2_2) + (50617203/1000000000000 : ℝ)*(sp_s2_2) + (121305397/1000000000000 : ℝ)*(sp_s2_7) + (3764677/200000000000 : ℝ)*(sp_s2_8) + (14988785865043/1000000000000 : ℝ)*(sp_s2_14) + (2997777669411/200000000000 : ℝ)*(sp_s2_15) + (7494428276619/500000000000 : ℝ)*(sp_s2_16) + (306972319161/50000000000 : ℝ)*(sp_s2_20) + (76932697/1000000000000 : ℝ)*(sp_s2_27) + (6139523315917/1000000000000 : ℝ)*(f.failure) + (14988907170441/1000000000000 : ℝ)*(f.sum) + (14734511720801355153/43789498150000000000000000000000 : ℝ)*base63 + (99581214544929/183887500000000000000000000 : ℝ)*base65 + (2604646021340691/2976650000000000000000000000 : ℝ)*base66 + (833737383007471/735550000000000000000000000 : ℝ)*base69 + (20350339857130427/77232750000000000000000000000 : ℝ)*base70 + (16665318252539/13125000000000000000000000 : ℝ)*base72 + (207121833718087/595330000000000000000000000 : ℝ)*base75 + (931863140869/2625000000000000000000000 : ℝ)*base77 + (60934863510537139/97671328125000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (77727/100000000000000000 : ℝ)*base86 + (77727/100000000000000000 : ℝ)*base88 + (77727/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2157/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2157/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7158803418944025848692195193/1462731969453125000000000000000000 : ℝ) := by norm_num
    linear_combination (754501/250000000000 : ℝ)*(base11) + (254010577137/200000000000 : ℝ)*(base39) + (32959/15625000000 : ℝ)*(base40) + (131322161627/250000000000 : ℝ)*(base49) + (2095115217311/250000000000 : ℝ)*(major_s2_0) + (2095115217311/250000000000 : ℝ)*(major_s2_1) + (2095115217311/250000000000 : ℝ)*(major_s2_2) + (17704549/500000000000 : ℝ)*(sp_s2_0) + (22275299/1000000000000 : ℝ)*(sp_s2_2) + (63313239/1000000000000 : ℝ)*(sp_s2_9) + (2378094907127/200000000000 : ℝ)*(sp_s2_21) + (11890512962737/1000000000000 : ℝ)*(sp_s2_22) + (59452136871/5000000000 : ℝ)*(sp_s2_23) + (4870407144369/1000000000000 : ℝ)*(sp_s2_27) + (4870407144369/1000000000000 : ℝ)*(f.failure) + (11890512962737/1000000000000 : ℝ)*(f.sum) + (147474467589907199/1183499950000000000000000000000 : ℝ)*base62 + (113467471471491/735550000000000000000000000 : ℝ)*base64 + (15784304963189/40225000000000000000000000 : ℝ)*base67 + (10984155491129/183887500000000000000000000 : ℝ)*base68 + (4806281068814388659/8727300750000000000000000000000 : ℝ)*base70 + (63764719442681/741562500000000000000000000 : ℝ)*base73 + (1166280486893/2011250000000000000000000 : ℝ)*base74 + (315888779216177/296625000000000000000000000 : ℝ)*base76 + (1629093364715558141/4772696250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (29461/100000000000000000 : ℝ)*base87 + (29461/100000000000000000 : ℝ)*base89 + (29461/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((2373/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59533/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44133/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44133/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28871/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28871/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14507/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14507/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2157/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2157/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314062_s2 p hpa hpb X hX hprev1

#print axioms solution

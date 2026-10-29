-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308057_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:18.87947+00:00
-- url     : https://prove2.me/submissions/e86b27a4-375c-4764-bdbc-74da6a3778f5

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
theorem collision_support_c308057_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3215555319/10000000000 : ℝ)*x 0 + (1606557217/5000000000 : ℝ)*x 1 + (6261544281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3215555319/10000000000 : ℝ)^69 ≤ (22829850908891/100000000000000 : ℝ)^53 := by
    have hnat : (3215555319 : ℕ)^69*100000000000000^53 ≤ 22829850908891^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3215555319 10000000000 22829850908891 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1606557217/5000000000 : ℝ)^69 ≤ (22807292012123/100000000000000 : ℝ)^53 := by
    have hnat : (1606557217 : ℕ)^69*100000000000000^53 ≤ 22807292012123^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606557217 5000000000 22807292012123 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6261544281/10000000000 : ℝ)^69 ≤ (27181428531137/50000000000000 : ℝ)^53 := by
    have hnat : (6261544281 : ℕ)^69*50000000000000^53 ≤ 27181428531137^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6261544281 10000000000 27181428531137 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3215555319/10000000000 : ℝ), (1606557217/5000000000 : ℝ), (6261544281/10000000000 : ℝ)] ![(22829850908891/100000000000000 : ℝ), (22807292012123/100000000000000 : ℝ), (27181428531137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3215555319/10000000000 : ℝ)|^69 ≤ (22829850908891/100000000000000 : ℝ)^53
        have hw : |(-3215555319/10000000000 : ℝ)|=(3215555319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1606557217/5000000000 : ℝ)|^69 ≤ (22807292012123/100000000000000 : ℝ)^53
        have hw : |(1606557217/5000000000 : ℝ)|=(1606557217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6261544281/10000000000 : ℝ)|^69 ≤ (27181428531137/50000000000000 : ℝ)^53
        have hw : |(6261544281/10000000000 : ℝ)|=(6261544281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (321384283/1000000000 : ℝ)*x 0 + (-1605701623/5000000000 : ℝ)*x 1 + (1252868659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321384283/1000000000 : ℝ)^69 ≤ (912560935099/4000000000000 : ℝ)^53 := by
    have hnat : (321384283 : ℕ)^69*4000000000000^53 ≤ 912560935099^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321384283 1000000000 912560935099 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1605701623/5000000000 : ℝ)^69 ≤ (227914801303/1000000000000 : ℝ)^53 := by
    have hnat : (1605701623 : ℕ)^69*1000000000000^53 ≤ 227914801303^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605701623 5000000000 227914801303 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252868659/2000000000 : ℝ)^69 ≤ (54394496474613/100000000000000 : ℝ)^53 := by
    have hnat : (1252868659 : ℕ)^69*100000000000000^53 ≤ 54394496474613^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252868659 2000000000 54394496474613 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(321384283/1000000000 : ℝ), (-1605701623/5000000000 : ℝ), (1252868659/2000000000 : ℝ)] ![(912560935099/4000000000000 : ℝ), (227914801303/1000000000000 : ℝ), (54394496474613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(321384283/1000000000 : ℝ)|^69 ≤ (912560935099/4000000000000 : ℝ)^53
        have hw : |(321384283/1000000000 : ℝ)|=(321384283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1605701623/5000000000 : ℝ)|^69 ≤ (227914801303/1000000000000 : ℝ)^53
        have hw : |(-1605701623/5000000000 : ℝ)|=(1605701623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252868659/2000000000 : ℝ)|^69 ≤ (54394496474613/100000000000000 : ℝ)^53
        have hw : |(1252868659/2000000000 : ℝ)|=(1252868659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (236375627/500000000 : ℝ)*x 0 + (946079897/2000000000 : ℝ)*x 1 + (850241319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236375627/500000000 : ℝ)^69 ≤ (37705837869043/100000000000000 : ℝ)^53 := by
    have hnat : (236375627 : ℕ)^69*100000000000000^53 ≤ 37705837869043^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236375627 500000000 37705837869043 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946079897/2000000000 : ℝ)^69 ≤ (4716977199401/12500000000000 : ℝ)^53 := by
    have hnat : (946079897 : ℕ)^69*12500000000000^53 ≤ 4716977199401^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946079897 2000000000 4716977199401 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850241319/2500000000 : ℝ)^69 ≤ (196466756187/800000000000 : ℝ)^53 := by
    have hnat : (850241319 : ℕ)^69*800000000000^53 ≤ 196466756187^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850241319 2500000000 196466756187 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(236375627/500000000 : ℝ), (946079897/2000000000 : ℝ), (850241319/2500000000 : ℝ)] ![(37705837869043/100000000000000 : ℝ), (4716977199401/12500000000000 : ℝ), (196466756187/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(236375627/500000000 : ℝ)|^69 ≤ (37705837869043/100000000000000 : ℝ)^53
        have hw : |(236375627/500000000 : ℝ)|=(236375627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(946079897/2000000000 : ℝ)|^69 ≤ (4716977199401/12500000000000 : ℝ)^53
        have hw : |(946079897/2000000000 : ℝ)|=(946079897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850241319/2500000000 : ℝ)|^69 ≤ (196466756187/800000000000 : ℝ)^53
        have hw : |(850241319/2500000000 : ℝ)|=(850241319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1349899859/5000000000 : ℝ)*x 0 + (568777963/2500000000 : ℝ)*x 1 + (7374439569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349899859/5000000000 : ℝ)^69 ≤ (9091343286893/50000000000000 : ℝ)^53 := by
    have hnat : (1349899859 : ℕ)^69*50000000000000^53 ≤ 9091343286893^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349899859 5000000000 9091343286893 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568777963/2500000000 : ℝ)^69 ≤ (3637729358177/25000000000000 : ℝ)^53 := by
    have hnat : (568777963 : ℕ)^69*25000000000000^53 ≤ 3637729358177^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568777963 2500000000 3637729358177 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7374439569/10000000000 : ℝ)^69 ≤ (33633197988229/50000000000000 : ℝ)^53 := by
    have hnat : (7374439569 : ℕ)^69*50000000000000^53 ≤ 33633197988229^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7374439569 10000000000 33633197988229 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1349899859/5000000000 : ℝ), (568777963/2500000000 : ℝ), (7374439569/10000000000 : ℝ)] ![(9091343286893/50000000000000 : ℝ), (3637729358177/25000000000000 : ℝ), (33633197988229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1349899859/5000000000 : ℝ)|^69 ≤ (9091343286893/50000000000000 : ℝ)^53
        have hw : |(-1349899859/5000000000 : ℝ)|=(1349899859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568777963/2500000000 : ℝ)|^69 ≤ (3637729358177/25000000000000 : ℝ)^53
        have hw : |(568777963/2500000000 : ℝ)|=(568777963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7374439569/10000000000 : ℝ)|^69 ≤ (33633197988229/50000000000000 : ℝ)^53
        have hw : |(7374439569/10000000000 : ℝ)|=(7374439569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (674360971/2500000000 : ℝ)*x 0 + (-2273126599/10000000000 : ℝ)*x 1 + (7377570351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674360971/2500000000 : ℝ)^69 ≤ (4540508345309/25000000000000 : ℝ)^53 := by
    have hnat : (674360971 : ℕ)^69*25000000000000^53 ≤ 4540508345309^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674360971 2500000000 4540508345309 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273126599/10000000000 : ℝ)^69 ≤ (7267194731881/50000000000000 : ℝ)^53 := by
    have hnat : (2273126599 : ℕ)^69*50000000000000^53 ≤ 7267194731881^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273126599 10000000000 7267194731881 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7377570351/10000000000 : ℝ)^69 ≤ (16825894285821/25000000000000 : ℝ)^53 := by
    have hnat : (7377570351 : ℕ)^69*25000000000000^53 ≤ 16825894285821^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7377570351 10000000000 16825894285821 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674360971/2500000000 : ℝ), (-2273126599/10000000000 : ℝ), (7377570351/10000000000 : ℝ)] ![(4540508345309/25000000000000 : ℝ), (7267194731881/50000000000000 : ℝ), (16825894285821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674360971/2500000000 : ℝ)|^69 ≤ (4540508345309/25000000000000 : ℝ)^53
        have hw : |(674360971/2500000000 : ℝ)|=(674360971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273126599/10000000000 : ℝ)|^69 ≤ (7267194731881/50000000000000 : ℝ)^53
        have hw : |(-2273126599/10000000000 : ℝ)|=(2273126599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7377570351/10000000000 : ℝ)|^69 ≤ (16825894285821/25000000000000 : ℝ)^53
        have hw : |(7377570351/10000000000 : ℝ)|=(7377570351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (888457723/2000000000 : ℝ)*x 0 + (1800554181/2500000000 : ℝ)*x 1 + (19179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888457723/2000000000 : ℝ)^69 ≤ (278172309783/800000000000 : ℝ)^53 := by
    have hnat : (888457723 : ℕ)^69*800000000000^53 ≤ 278172309783^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888457723 2000000000 278172309783 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800554181/2500000000 : ℝ)^69 ≤ (32614228832933/50000000000000 : ℝ)^53 := by
    have hnat : (1800554181 : ℕ)^69*50000000000000^53 ≤ 32614228832933^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800554181 2500000000 32614228832933 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19179/10000000000 : ℝ)^69 ≤ (1802423/50000000000000 : ℝ)^53 := by
    have hnat : (19179 : ℕ)^69*50000000000000^53 ≤ 1802423^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19179 10000000000 1802423 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(888457723/2000000000 : ℝ), (1800554181/2500000000 : ℝ), (19179/10000000000 : ℝ)] ![(278172309783/800000000000 : ℝ), (32614228832933/50000000000000 : ℝ), (1802423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(888457723/2000000000 : ℝ)|^69 ≤ (278172309783/800000000000 : ℝ)^53
        have hw : |(888457723/2000000000 : ℝ)|=(888457723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1800554181/2500000000 : ℝ)|^69 ≤ (32614228832933/50000000000000 : ℝ)^53
        have hw : |(1800554181/2500000000 : ℝ)|=(1800554181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19179/10000000000 : ℝ)|^69 ≤ (1802423/50000000000000 : ℝ)^53
        have hw : |(19179/10000000000 : ℝ)|=(19179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (200171531/500000000 : ℝ)*x 0 + (3245351379/5000000000 : ℝ)*x 1 + (2045025611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200171531/500000000 : ℝ)^69 ≤ (30367697926799/100000000000000 : ℝ)^53 := by
    have hnat : (200171531 : ℕ)^69*100000000000000^53 ≤ 30367697926799^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200171531 500000000 30367697926799 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3245351379/5000000000 : ℝ)^69 ≤ (569672258239/1000000000000 : ℝ)^53 := by
    have hnat : (3245351379 : ℕ)^69*1000000000000^53 ≤ 569672258239^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3245351379 5000000000 569672258239 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045025611/10000000000 : ℝ)^69 ≤ (6332538117451/50000000000000 : ℝ)^53 := by
    have hnat : (2045025611 : ℕ)^69*50000000000000^53 ≤ 6332538117451^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045025611 10000000000 6332538117451 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(200171531/500000000 : ℝ), (3245351379/5000000000 : ℝ), (2045025611/10000000000 : ℝ)] ![(30367697926799/100000000000000 : ℝ), (569672258239/1000000000000 : ℝ), (6332538117451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(200171531/500000000 : ℝ)|^69 ≤ (30367697926799/100000000000000 : ℝ)^53
        have hw : |(200171531/500000000 : ℝ)|=(200171531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3245351379/5000000000 : ℝ)|^69 ≤ (569672258239/1000000000000 : ℝ)^53
        have hw : |(3245351379/5000000000 : ℝ)|=(3245351379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2045025611/10000000000 : ℝ)|^69 ≤ (6332538117451/50000000000000 : ℝ)^53
        have hw : |(2045025611/10000000000 : ℝ)|=(2045025611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-45552567/200000000 : ℝ)*x 0 + (2697298149/10000000000 : ℝ)*x 1 + (1843630389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45552567/200000000 : ℝ)^69 ≤ (7285937235781/50000000000000 : ℝ)^53 := by
    have hnat : (45552567 : ℕ)^69*50000000000000^53 ≤ 7285937235781^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45552567 200000000 7285937235781 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697298149/10000000000 : ℝ)^69 ≤ (454018898157/2500000000000 : ℝ)^53 := by
    have hnat : (2697298149 : ℕ)^69*2500000000000^53 ≤ 454018898157^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697298149 10000000000 454018898157 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1843630389/2500000000 : ℝ)^69 ≤ (33633684796657/50000000000000 : ℝ)^53 := by
    have hnat : (1843630389 : ℕ)^69*50000000000000^53 ≤ 33633684796657^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843630389 2500000000 33633684796657 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45552567/200000000 : ℝ), (2697298149/10000000000 : ℝ), (1843630389/2500000000 : ℝ)] ![(7285937235781/50000000000000 : ℝ), (454018898157/2500000000000 : ℝ), (33633684796657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45552567/200000000 : ℝ)|^69 ≤ (7285937235781/50000000000000 : ℝ)^53
        have hw : |(-45552567/200000000 : ℝ)|=(45552567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697298149/10000000000 : ℝ)|^69 ≤ (454018898157/2500000000000 : ℝ)^53
        have hw : |(2697298149/10000000000 : ℝ)|=(2697298149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1843630389/2500000000 : ℝ)|^69 ≤ (33633684796657/50000000000000 : ℝ)^53
        have hw : |(1843630389/2500000000 : ℝ)|=(1843630389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2275640757/10000000000 : ℝ)*x 0 + (-2694944327/10000000000 : ℝ)*x 1 + (368882623/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2275640757/10000000000 : ℝ)^69 ≤ (14555321498069/100000000000000 : ℝ)^53 := by
    have hnat : (2275640757 : ℕ)^69*100000000000000^53 ≤ 14555321498069^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275640757 10000000000 14555321498069 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694944327/10000000000 : ℝ)^69 ≤ (18140126146851/100000000000000 : ℝ)^53 := by
    have hnat : (2694944327 : ℕ)^69*100000000000000^53 ≤ 18140126146851^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694944327 10000000000 18140126146851 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368882623/500000000 : ℝ)^69 ≤ (67304552333873/100000000000000 : ℝ)^53 := by
    have hnat : (368882623 : ℕ)^69*100000000000000^53 ≤ 67304552333873^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368882623 500000000 67304552333873 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2275640757/10000000000 : ℝ), (-2694944327/10000000000 : ℝ), (368882623/500000000 : ℝ)] ![(14555321498069/100000000000000 : ℝ), (18140126146851/100000000000000 : ℝ), (67304552333873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2275640757/10000000000 : ℝ)|^69 ≤ (14555321498069/100000000000000 : ℝ)^53
        have hw : |(2275640757/10000000000 : ℝ)|=(2275640757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2694944327/10000000000 : ℝ)|^69 ≤ (18140126146851/100000000000000 : ℝ)^53
        have hw : |(-2694944327/10000000000 : ℝ)|=(2694944327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368882623/500000000 : ℝ)|^69 ≤ (67304552333873/100000000000000 : ℝ)^53
        have hw : |(368882623/500000000 : ℝ)|=(368882623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (449942919/625000000 : ℝ)*x 0 + (138934673/312500000 : ℝ)*x 1 + (19159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449942919/625000000 : ℝ)^69 ≤ (16297888643279/25000000000000 : ℝ)^53 := by
    have hnat : (449942919 : ℕ)^69*25000000000000^53 ≤ 16297888643279^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449942919 625000000 16297888643279 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138934673/312500000 : ℝ)^69 ≤ (17404220910541/50000000000000 : ℝ)^53 := by
    have hnat : (138934673 : ℕ)^69*50000000000000^53 ≤ 17404220910541^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138934673 312500000 17404220910541 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19159/10000000000 : ℝ)^69 ≤ (3599953/100000000000000 : ℝ)^53 := by
    have hnat : (19159 : ℕ)^69*100000000000000^53 ≤ 3599953^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19159 10000000000 3599953 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449942919/625000000 : ℝ), (138934673/312500000 : ℝ), (19159/10000000000 : ℝ)] ![(16297888643279/25000000000000 : ℝ), (17404220910541/50000000000000 : ℝ), (3599953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449942919/625000000 : ℝ)|^69 ≤ (16297888643279/25000000000000 : ℝ)^53
        have hw : |(449942919/625000000 : ℝ)|=(449942919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138934673/312500000 : ℝ)|^69 ≤ (17404220910541/50000000000000 : ℝ)^53
        have hw : |(138934673/312500000 : ℝ)|=(138934673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19159/10000000000 : ℝ)|^69 ≤ (3599953/100000000000000 : ℝ)^53
        have hw : |(19159/10000000000 : ℝ)|=(19159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_18 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3243953557/5000000000 : ℝ)*x 0 + (4006709363/10000000000 : ℝ)*x 1 + (2044970927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3243953557/5000000000 : ℝ)^69 ≤ (11387056792819/20000000000000 : ℝ)^53 := by
    have hnat : (3243953557 : ℕ)^69*20000000000000^53 ≤ 11387056792819^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3243953557 5000000000 11387056792819 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006709363/10000000000 : ℝ)^69 ≤ (30400080684907/100000000000000 : ℝ)^53 := by
    have hnat : (4006709363 : ℕ)^69*100000000000000^53 ≤ 30400080684907^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006709363 10000000000 30400080684907 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044970927/10000000000 : ℝ)^69 ≤ (12664635334191/100000000000000 : ℝ)^53 := by
    have hnat : (2044970927 : ℕ)^69*100000000000000^53 ≤ 12664635334191^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044970927 10000000000 12664635334191 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3243953557/5000000000 : ℝ), (4006709363/10000000000 : ℝ), (2044970927/10000000000 : ℝ)] ![(11387056792819/20000000000000 : ℝ), (30400080684907/100000000000000 : ℝ), (12664635334191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3243953557/5000000000 : ℝ)|^69 ≤ (11387056792819/20000000000000 : ℝ)^53
        have hw : |(3243953557/5000000000 : ℝ)|=(3243953557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006709363/10000000000 : ℝ)|^69 ≤ (30400080684907/100000000000000 : ℝ)^53
        have hw : |(4006709363/10000000000 : ℝ)|=(4006709363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2044970927/10000000000 : ℝ)|^69 ≤ (12664635334191/100000000000000 : ℝ)^53
        have hw : |(2044970927/10000000000 : ℝ)|=(2044970927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4224584857/10000000000 : ℝ)*x 0 + (1160810621/5000000000 : ℝ)*x 1 + (6095264627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224584857/10000000000 : ℝ)^69 ≤ (32569656745381/100000000000000 : ℝ)^53 := by
    have hnat : (4224584857 : ℕ)^69*100000000000000^53 ≤ 32569656745381^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224584857 10000000000 32569656745381 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1160810621/5000000000 : ℝ)^69 ≤ (7469682864601/50000000000000 : ℝ)^53 := by
    have hnat : (1160810621 : ℕ)^69*50000000000000^53 ≤ 7469682864601^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160810621 5000000000 7469682864601 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6095264627/10000000000 : ℝ)^69 ≤ (52490977517989/100000000000000 : ℝ)^53 := by
    have hnat : (6095264627 : ℕ)^69*100000000000000^53 ≤ 52490977517989^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6095264627 10000000000 52490977517989 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4224584857/10000000000 : ℝ), (1160810621/5000000000 : ℝ), (6095264627/10000000000 : ℝ)] ![(32569656745381/100000000000000 : ℝ), (7469682864601/50000000000000 : ℝ), (52490977517989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4224584857/10000000000 : ℝ)|^69 ≤ (32569656745381/100000000000000 : ℝ)^53
        have hw : |(-4224584857/10000000000 : ℝ)|=(4224584857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1160810621/5000000000 : ℝ)|^69 ≤ (7469682864601/50000000000000 : ℝ)^53
        have hw : |(1160810621/5000000000 : ℝ)|=(1160810621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6095264627/10000000000 : ℝ)|^69 ≤ (52490977517989/100000000000000 : ℝ)^53
        have hw : |(6095264627/10000000000 : ℝ)|=(6095264627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (92903787/400000000 : ℝ)*x 0 + (-4220587767/10000000000 : ℝ)*x 1 + (3049057417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92903787/400000000 : ℝ)^69 ≤ (14947521172251/100000000000000 : ℝ)^53 := by
    have hnat : (92903787 : ℕ)^69*100000000000000^53 ≤ 14947521172251^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92903787 400000000 14947521172251 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4220587767/10000000000 : ℝ)^69 ≤ (32529543827919/100000000000000 : ℝ)^53 := by
    have hnat : (4220587767 : ℕ)^69*100000000000000^53 ≤ 32529543827919^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220587767 10000000000 32529543827919 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3049057417/5000000000 : ℝ)^69 ≤ (13130733746593/25000000000000 : ℝ)^53 := by
    have hnat : (3049057417 : ℕ)^69*25000000000000^53 ≤ 13130733746593^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049057417 5000000000 13130733746593 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(92903787/400000000 : ℝ), (-4220587767/10000000000 : ℝ), (3049057417/5000000000 : ℝ)] ![(14947521172251/100000000000000 : ℝ), (32529543827919/100000000000000 : ℝ), (13130733746593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(92903787/400000000 : ℝ)|^69 ≤ (14947521172251/100000000000000 : ℝ)^53
        have hw : |(92903787/400000000 : ℝ)|=(92903787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4220587767/10000000000 : ℝ)|^69 ≤ (32529543827919/100000000000000 : ℝ)^53
        have hw : |(-4220587767/10000000000 : ℝ)|=(4220587767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3049057417/5000000000 : ℝ)|^69 ≤ (13130733746593/25000000000000 : ℝ)^53
        have hw : |(3049057417/5000000000 : ℝ)|=(3049057417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3091904243/5000000000 : ℝ)*x 0 + (221805573/400000000 : ℝ)*x 1 + (-51534569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3091904243/5000000000 : ℝ)^69 ≤ (53485860051943/100000000000000 : ℝ)^53 := by
    have hnat : (3091904243 : ℕ)^69*100000000000000^53 ≤ 53485860051943^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091904243 5000000000 53485860051943 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221805573/400000000 : ℝ)^69 ≤ (46409086207039/100000000000000 : ℝ)^53 := by
    have hnat : (221805573 : ℕ)^69*100000000000000^53 ≤ 46409086207039^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221805573 400000000 46409086207039 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51534569/10000000000 : ℝ)^69 ≤ (105053722939/100000000000000 : ℝ)^53 := by
    have hnat : (51534569 : ℕ)^69*100000000000000^53 ≤ 105053722939^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51534569 10000000000 105053722939 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3091904243/5000000000 : ℝ), (221805573/400000000 : ℝ), (-51534569/10000000000 : ℝ)] ![(53485860051943/100000000000000 : ℝ), (46409086207039/100000000000000 : ℝ), (105053722939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3091904243/5000000000 : ℝ)|^69 ≤ (53485860051943/100000000000000 : ℝ)^53
        have hw : |(3091904243/5000000000 : ℝ)|=(3091904243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221805573/400000000 : ℝ)|^69 ≤ (46409086207039/100000000000000 : ℝ)^53
        have hw : |(221805573/400000000 : ℝ)|=(221805573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51534569/10000000000 : ℝ)|^69 ≤ (105053722939/100000000000000 : ℝ)^53
        have hw : |(-51534569/10000000000 : ℝ)|=(51534569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s2_s2_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (857951401/2500000000 : ℝ)*x 0 + (221805573/400000000 : ℝ)*x 1 + (3837789219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857951401/2500000000 : ℝ)^69 ≤ (24848667825481/100000000000000 : ℝ)^53 := by
    have hnat : (857951401 : ℕ)^69*100000000000000^53 ≤ 24848667825481^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857951401 2500000000 24848667825481 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221805573/400000000 : ℝ)^69 ≤ (46409086207039/100000000000000 : ℝ)^53 := by
    have hnat : (221805573 : ℕ)^69*100000000000000^53 ≤ 46409086207039^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221805573 400000000 46409086207039 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3837789219/10000000000 : ℝ)^69 ≤ (1437112297827/5000000000000 : ℝ)^53 := by
    have hnat : (3837789219 : ℕ)^69*5000000000000^53 ≤ 1437112297827^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837789219 10000000000 1437112297827 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857951401/2500000000 : ℝ), (221805573/400000000 : ℝ), (3837789219/10000000000 : ℝ)] ![(24848667825481/100000000000000 : ℝ), (46409086207039/100000000000000 : ℝ), (1437112297827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857951401/2500000000 : ℝ)|^69 ≤ (24848667825481/100000000000000 : ℝ)^53
        have hw : |(857951401/2500000000 : ℝ)|=(857951401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221805573/400000000 : ℝ)|^69 ≤ (46409086207039/100000000000000 : ℝ)^53
        have hw : |(221805573/400000000 : ℝ)|=(221805573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3837789219/10000000000 : ℝ)|^69 ≤ (1437112297827/5000000000000 : ℝ)^53
        have hw : |(3837789219/10000000000 : ℝ)|=(3837789219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308057_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((20633/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20633/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7093/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7093/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2126/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2126/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13601/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13601/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2957/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2957/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (20633/25000 : ℝ) ^ (17/4 : ℝ) ≤ (221113406148710399/500000000000000000 : ℝ) := by
    have hpowers : (20633/25000 : ℝ)^17 ≤ (221113406148710399/500000000000000000 : ℝ)^4 := by
      have hnat : (20633 : ℕ)^17*500000000000000000^4 ≤ 221113406148710399^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20633 25000 221113406148710399 500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20633/25000 : ℝ)) (X := (221113406148710399/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (721113406148710399/500000000000000000 : ℝ) ≤ (1089982844189249/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (721113406148710399/500000000000000000 : ℝ)^4 ≤ (1089982844189249/1000000000000000 : ℝ)^17 := by
      have hnat : (721113406148710399 : ℕ)^4*1000000000000000^17 ≤ 1089982844189249^17*500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        721113406148710399 500000000000000000 1089982844189249 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1089982844189249/1000000000000000 : ℝ)) (X := (721113406148710399/500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (471113406148710399/250000000000000000 : ℝ) ≤ (2901947340143541/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (471113406148710399/250000000000000000 : ℝ)^4 ≤ (2901947340143541/2500000000000000 : ℝ)^17 := by
      have hnat : (471113406148710399 : ℕ)^4*2500000000000000^17 ≤ 2901947340143541^17*250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        471113406148710399 250000000000000000 2901947340143541 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2901947340143541/2500000000000000 : ℝ)) (X := (471113406148710399/250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(89982844189249/825320000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(353980459340837/4126600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (20633/25000 : ℝ)) (alpha := (89982844189249/825320000000000 : ℝ)) (beta := (353980459340837/4126600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20633/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(89982844189249/825320000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(353980459340837/4126600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (82343/100000 : ℝ) ^ (17/4 : ℝ) ≤ (21896939481906623181/50000000000000000000 : ℝ) := by
    have hpowers : (82343/100000 : ℝ)^17 ≤ (21896939481906623181/50000000000000000000 : ℝ)^4 := by
      have hnat : (82343 : ℕ)^17*50000000000000000000^4 ≤ 21896939481906623181^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82343 100000 21896939481906623181 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82343/100000 : ℝ)) (X := (21896939481906623181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (71896939481906623181/50000000000000000000 : ℝ) ≤ (5446097252785181/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (71896939481906623181/50000000000000000000 : ℝ)^4 ≤ (5446097252785181/5000000000000000 : ℝ)^17 := by
      have hnat : (71896939481906623181 : ℕ)^4*5000000000000000^17 ≤ 5446097252785181^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71896939481906623181 50000000000000000000 5446097252785181 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5446097252785181/5000000000000000 : ℝ)) (X := (71896939481906623181/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (46896939481906623181/25000000000000000000 : ℝ) ≤ (2898834482348733/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (46896939481906623181/25000000000000000000 : ℝ)^4 ≤ (2898834482348733/2500000000000000 : ℝ)^17 := by
      have hnat : (46896939481906623181 : ℕ)^4*2500000000000000^17 ≤ 2898834482348733^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46896939481906623181 25000000000000000000 2898834482348733 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2898834482348733/2500000000000000 : ℝ)) (X := (46896939481906623181/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(446097252785181/4117150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(70314342382457/823430000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (82343/100000 : ℝ)) (alpha := (446097252785181/4117150000000000 : ℝ)) (beta := (70314342382457/823430000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (82343/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(446097252785181/4117150000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(70314342382457/823430000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (7093/20000 : ℝ) ^ (17/4 : ℝ) ≤ (1220814974754697933/100000000000000000000 : ℝ) := by
    have hpowers : (7093/20000 : ℝ)^17 ≤ (1220814974754697933/100000000000000000000 : ℝ)^4 := by
      have hnat : (7093 : ℕ)^17*100000000000000000000^4 ≤ 1220814974754697933^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7093 20000 1220814974754697933 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7093/20000 : ℝ)) (X := (1220814974754697933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (101220814974754697933/100000000000000000000 : ℝ) ≤ (5014295964804879/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (101220814974754697933/100000000000000000000 : ℝ)^4 ≤ (5014295964804879/5000000000000000 : ℝ)^17 := by
      have hnat : (101220814974754697933 : ℕ)^4*5000000000000000^17 ≤ 5014295964804879^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101220814974754697933 100000000000000000000 5014295964804879 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014295964804879/5000000000000000 : ℝ)) (X := (101220814974754697933/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (51220814974754697933/50000000000000000000 : ℝ) ≤ (5028460679042799/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (51220814974754697933/50000000000000000000 : ℝ)^4 ≤ (5028460679042799/5000000000000000 : ℝ)^17 := by
      have hnat : (51220814974754697933 : ℕ)^4*5000000000000000^17 ≤ 5028460679042799^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51220814974754697933 50000000000000000000 5028460679042799 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028460679042799/5000000000000000 : ℝ)) (X := (51220814974754697933/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(14295964804879/1773250000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(88529463987/11082812500000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (7093/20000 : ℝ)) (alpha := (14295964804879/1773250000000000 : ℝ)) (beta := (88529463987/11082812500000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7093/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(14295964804879/1773250000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(88529463987/11082812500000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3215555319/10000000000 : ℝ)*X 0 0+(1606557217/5000000000 : ℝ)*X 0 1+(6261544281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((321384283/1000000000 : ℝ)*X 1 0+(-1605701623/5000000000 : ℝ)*X 1 1+(1252868659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((236375627/500000000 : ℝ)*X 0 0+(946079897/2000000000 : ℝ)*X 0 1+(850241319/2500000000 : ℝ)*X 0 2+(236375627/500000000 : ℝ)*X 1 0+(946079897/2000000000 : ℝ)*X 1 1+(850241319/2500000000 : ℝ)*X 1 2+(236375627/500000000 : ℝ)*X 2 0+(946079897/2000000000 : ℝ)*X 2 1+(850241319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1349899859/5000000000 : ℝ)*X 0 0+(568777963/2500000000 : ℝ)*X 0 1+(7374439569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((674360971/2500000000 : ℝ)*X 1 0+(-2273126599/10000000000 : ℝ)*X 1 1+(7377570351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((888457723/2000000000 : ℝ)*X 2 0+(1800554181/2500000000 : ℝ)*X 2 1+(19179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((200171531/500000000 : ℝ)*X 0 0+(3245351379/5000000000 : ℝ)*X 0 1+(2045025611/10000000000 : ℝ)*X 0 2+(200171531/500000000 : ℝ)*X 1 0+(3245351379/5000000000 : ℝ)*X 1 1+(2045025611/10000000000 : ℝ)*X 1 2+(200171531/500000000 : ℝ)*X 2 0+(3245351379/5000000000 : ℝ)*X 2 1+(2045025611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-45552567/200000000 : ℝ)*X 0 0+(2697298149/10000000000 : ℝ)*X 0 1+(1843630389/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((2275640757/10000000000 : ℝ)*X 1 0+(-2694944327/10000000000 : ℝ)*X 1 1+(368882623/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((449942919/625000000 : ℝ)*X 2 0+(138934673/312500000 : ℝ)*X 2 1+(19159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((3243953557/5000000000 : ℝ)*X 0 0+(4006709363/10000000000 : ℝ)*X 0 1+(2044970927/10000000000 : ℝ)*X 0 2+(3243953557/5000000000 : ℝ)*X 1 0+(4006709363/10000000000 : ℝ)*X 1 1+(2044970927/10000000000 : ℝ)*X 1 2+(3243953557/5000000000 : ℝ)*X 2 0+(4006709363/10000000000 : ℝ)*X 2 1+(2044970927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-4224584857/10000000000 : ℝ)*X 0 0+(1160810621/5000000000 : ℝ)*X 0 1+(6095264627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((92903787/400000000 : ℝ)*X 1 0+(-4220587767/10000000000 : ℝ)*X 1 1+(3049057417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((3091904243/5000000000 : ℝ)*X 2 0+(221805573/400000000 : ℝ)*X 2 1+(-51534569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((857951401/2500000000 : ℝ)*X 0 0+(221805573/400000000 : ℝ)*X 0 1+(3837789219/10000000000 : ℝ)*X 0 2+(857951401/2500000000 : ℝ)*X 1 0+(221805573/400000000 : ℝ)*X 1 1+(3837789219/10000000000 : ℝ)*X 1 2+(857951401/2500000000 : ℝ)*X 2 0+(221805573/400000000 : ℝ)*X 2 1+(3837789219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((2126/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2126/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1848603879649248022376589321/146014724750000000000000000000000 : ℝ) := by norm_num
    linear_combination (607995061437/1000000000000 : ℝ)*(base7) + (814954675817/1000000000000 : ℝ)*(base59) + (305390309973/1000000000000 : ℝ)*(base60) + (3057007849003/1000000000000 : ℝ)*(major_s2_0) + (3057007849003/1000000000000 : ℝ)*(major_s2_1) + (3057007849003/1000000000000 : ℝ)*(major_s2_2) + (1011501/200000000000 : ℝ)*(sp_s2_0) + (1026839/250000000000 : ℝ)*(sp_s2_1) + (3789718077957/1000000000000 : ℝ)*(sp_s2_7) + (3789822893199/1000000000000 : ℝ)*(sp_s2_8) + (1894913500277/500000000000 : ℝ)*(sp_s2_9) + (639678805661/250000000000 : ℝ)*(sp_s2_12) + (25966273/250000000000 : ℝ)*(sp_s2_13) + (942957/100000000000 : ℝ)*(sp_s2_25) + (1950729590777/1000000000000 : ℝ)*(f.failure) + (1894913500277/500000000000 : ℝ)*(f.sum) + (57812214388618235979/146014724750000000000000000000000 : ℝ)*base63 + (50798429224553/88662500000000000000000000 : ℝ)*base64 + (403164018213299/823430000000000000000000000 : ℝ)*base67 + (603969440716663/1773250000000000000000000000 : ℝ)*base69 + (15884264851479590209/29269973800000000000000000000000 : ℝ)*base70 + (839950428801269/4126600000000000000000000000 : ℝ)*base72 + (1299693900031493/4117150000000000000000000000 : ℝ)*base75 + (378770690143811/825320000000000000000000000 : ℝ)*base77 + (52907005991551356733/339796623800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (45553/100000000000000000 : ℝ)*base86 + (45553/100000000000000000 : ℝ)*base88 + (45553/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13601/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13601/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7600510219457630992654928273013/376590226970843750000000000000000000 : ℝ) := by norm_num
    linear_combination (30397473321/50000000000 : ℝ)*(base7) + (814646362003/1000000000000 : ℝ)*(base59) + (509732542827/1000000000000 : ℝ)*(base60) + (1528236541787/500000000000 : ℝ)*(major_s2_0) + (1528236541787/500000000000 : ℝ)*(major_s2_1) + (1528236541787/500000000000 : ℝ)*(major_s2_2) + (10164541/500000000000 : ℝ)*(sp_s2_0) + (19672811/1000000000000 : ℝ)*(sp_s2_1) + (751721/31250000000 : ℝ)*(sp_s2_6) + (17174209/100000000000 : ℝ)*(sp_s2_8) + (189455194131/50000000000 : ℝ)*(sp_s2_13) + (1184041499/312500000 : ℝ)*(sp_s2_14) + (1894562105851/500000000000 : ℝ)*(sp_s2_15) + (1279156879527/500000000000 : ℝ)*(sp_s2_18) + (975194173853/500000000000 : ℝ)*(f.failure) + (1894562105851/500000000000 : ℝ)*(f.sum) + (31597030338818151191/73007362375000000000000000000000 : ℝ)*base63 + (16350516931533/177325000000000000000000000 : ℝ)*base64 + (565126198519/411715000000000000000000000 : ℝ)*base66 + (69774723172469/110828125000000000000000000 : ℝ)*base69 + (4578911435750152801/14634986900000000000000000000000 : ℝ)*base70 + (1360809717733269/2063300000000000000000000000 : ℝ)*base73 + (315070367156717/2058575000000000000000000000 : ℝ)*base75 + (37266543782759/412660000000000000000000000 : ℝ)*base77 + (10358290231438130437/169898311900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (22517/50000000000000000 : ℝ)*base86 + (22517/50000000000000000 : ℝ)*base88 + (22517/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2957/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2957/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5956698239145142536811304585211/1506360907883375000000000000000000000 : ℝ) := by norm_num
    linear_combination (166343474097/500000000000 : ℝ)*(base5) + (119467/1000000000000 : ℝ)*(base16) + (885761/1000000000000 : ℝ)*(base40) + (408091/500000000000 : ℝ)*(base50) + (809108307813/1000000000000 : ℝ)*(base59) + (969954006319/500000000000 : ℝ)*(major_s2_0) + (969954006319/500000000000 : ℝ)*(major_s2_1) + (969954006319/500000000000 : ℝ)*(major_s2_2) + (10564349/250000000000 : ℝ)*(sp_s2_6) + (26339667/500000000000 : ℝ)*(sp_s2_12) + (1320962923177/500000000000 : ℝ)*(sp_s2_19) + (2641925726887/1000000000000 : ℝ)*(sp_s2_20) + (743653198637/250000000000 : ℝ)*(sp_s2_21) + (905106975871/1000000000000 : ℝ)*(sp_s2_25) + (618944430397/500000000000 : ℝ)*(f.failure) + (1320962923177/500000000000 : ℝ)*(f.sum) + (51108534361786615583/73007362375000000000000000000000 : ℝ)*base62 + (161669371074967/354650000000000000000000000 : ℝ)*base64 + (25592760977169/164686000000000000000000000 : ℝ)*base66 + (1020498874830727/1773250000000000000000000000 : ℝ)*base68 + (6310730950802368877/14634986900000000000000000000000 : ℝ)*base70 + (1283873298602407/2063300000000000000000000000 : ℝ)*base72 + (2156389458095951/2058575000000000000000000000 : ℝ)*base74 + (371857763616831/412660000000000000000000000 : ℝ)*base76 + (23305458378964918521/169898311900000000000000000000000 : ℝ)*base78 + (44267/50000000000000000 : ℝ)*base87 + (44267/50000000000000000 : ℝ)*base89 + (44267/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((20633/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20633/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7093/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7093/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2126/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2126/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13601/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13601/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2957/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2957/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308057_s2 p hpa hpb X hX hprev1

#print axioms solution

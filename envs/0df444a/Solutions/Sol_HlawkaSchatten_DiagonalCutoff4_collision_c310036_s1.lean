-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310036_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:24:02.47337+00:00
-- url     : https://prove2.me/submissions/16bcc786-994d-4af1-b9eb-216894d8aeac

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
theorem collision_support_c310036_s1_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1163535339/2000000000 : ℝ)*x 0 + (3394825387/10000000000 : ℝ)*x 1 + (-856637983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163535339/2000000000 : ℝ)^9 ≤ (49835082048013/100000000000000 : ℝ)^7 := by
    have hnat : (1163535339 : ℕ)^9*100000000000000^7 ≤ 49835082048013^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163535339 2000000000 49835082048013 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3394825387/10000000000 : ℝ)^9 ≤ (24932468647399/100000000000000 : ℝ)^7 := by
    have hnat : (3394825387 : ℕ)^9*100000000000000^7 ≤ 24932468647399^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394825387 10000000000 24932468647399 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (856637983/2500000000 : ℝ)^9 ≤ (25232449294711/100000000000000 : ℝ)^7 := by
    have hnat : (856637983 : ℕ)^9*100000000000000^7 ≤ 25232449294711^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856637983 2500000000 25232449294711 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1163535339/2000000000 : ℝ), (3394825387/10000000000 : ℝ), (-856637983/2500000000 : ℝ)] ![(49835082048013/100000000000000 : ℝ), (24932468647399/100000000000000 : ℝ), (25232449294711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1163535339/2000000000 : ℝ)|^9 ≤ (49835082048013/100000000000000 : ℝ)^7
        have hw : |(1163535339/2000000000 : ℝ)|=(1163535339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3394825387/10000000000 : ℝ)|^9 ≤ (24932468647399/100000000000000 : ℝ)^7
        have hw : |(3394825387/10000000000 : ℝ)|=(3394825387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-856637983/2500000000 : ℝ)|^9 ≤ (25232449294711/100000000000000 : ℝ)^7
        have hw : |(-856637983/2500000000 : ℝ)|=(856637983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (662971347/1250000000 : ℝ)*x 0 + (-3718573501/10000000000 : ℝ)*x 1 + (-3686694627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662971347/1250000000 : ℝ)^9 ≤ (5531013091829/12500000000000 : ℝ)^7 := by
    have hnat : (662971347 : ℕ)^9*12500000000000^7 ≤ 5531013091829^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662971347 1250000000 5531013091829 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3718573501/10000000000 : ℝ)^9 ≤ (14015118235361/50000000000000 : ℝ)^7 := by
    have hnat : (3718573501 : ℕ)^9*50000000000000^7 ≤ 14015118235361^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718573501 10000000000 14015118235361 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3686694627/10000000000 : ℝ)^9 ≤ (2772165877043/10000000000000 : ℝ)^7 := by
    have hnat : (3686694627 : ℕ)^9*10000000000000^7 ≤ 2772165877043^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686694627 10000000000 2772165877043 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662971347/1250000000 : ℝ), (-3718573501/10000000000 : ℝ), (-3686694627/10000000000 : ℝ)] ![(5531013091829/12500000000000 : ℝ), (14015118235361/50000000000000 : ℝ), (2772165877043/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662971347/1250000000 : ℝ)|^9 ≤ (5531013091829/12500000000000 : ℝ)^7
        have hw : |(662971347/1250000000 : ℝ)|=(662971347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3718573501/10000000000 : ℝ)|^9 ≤ (14015118235361/50000000000000 : ℝ)^7
        have hw : |(-3718573501/10000000000 : ℝ)|=(3718573501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3686694627/10000000000 : ℝ)|^9 ≤ (2772165877043/10000000000000 : ℝ)^7
        have hw : |(-3686694627/10000000000 : ℝ)|=(3686694627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-185961889/10000000000 : ℝ)*x 0 + (-406767877/625000000 : ℝ)*x 1 + (-2538829801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185961889/10000000000 : ℝ)^9 ≤ (595626002351/100000000000000 : ℝ)^7 := by
    have hnat : (185961889 : ℕ)^9*100000000000000^7 ≤ 595626002351^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185961889 10000000000 595626002351 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406767877/625000000 : ℝ)^9 ≤ (28783353245507/50000000000000 : ℝ)^7 := by
    have hnat : (406767877 : ℕ)^9*50000000000000^7 ≤ 28783353245507^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406767877 625000000 28783353245507 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538829801/5000000000 : ℝ)^9 ≤ (41837667491891/100000000000000 : ℝ)^7 := by
    have hnat : (2538829801 : ℕ)^9*100000000000000^7 ≤ 41837667491891^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538829801 5000000000 41837667491891 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185961889/10000000000 : ℝ), (-406767877/625000000 : ℝ), (-2538829801/5000000000 : ℝ)] ![(595626002351/100000000000000 : ℝ), (28783353245507/50000000000000 : ℝ), (41837667491891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185961889/10000000000 : ℝ)|^9 ≤ (595626002351/100000000000000 : ℝ)^7
        have hw : |(-185961889/10000000000 : ℝ)|=(185961889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406767877/625000000 : ℝ)|^9 ≤ (28783353245507/50000000000000 : ℝ)^7
        have hw : |(-406767877/625000000 : ℝ)|=(406767877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2538829801/5000000000 : ℝ)|^9 ≤ (41837667491891/100000000000000 : ℝ)^7
        have hw : |(-2538829801/5000000000 : ℝ)|=(2538829801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1024794333/2000000000 : ℝ)*x 0 + (34584101/80000000 : ℝ)*x 1 + (-3258404689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024794333/2000000000 : ℝ)^9 ≤ (42328922235549/100000000000000 : ℝ)^7 := by
    have hnat : (1024794333 : ℕ)^9*100000000000000^7 ≤ 42328922235549^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024794333 2000000000 42328922235549 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34584101/80000000 : ℝ)^9 ≤ (34019310330019/100000000000000 : ℝ)^7 := by
    have hnat : (34584101 : ℕ)^9*100000000000000^7 ≤ 34019310330019^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34584101 80000000 34019310330019 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3258404689/10000000000 : ℝ)^9 ≤ (1478235463989/6250000000000 : ℝ)^7 := by
    have hnat : (3258404689 : ℕ)^9*6250000000000^7 ≤ 1478235463989^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3258404689 10000000000 1478235463989 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1024794333/2000000000 : ℝ), (34584101/80000000 : ℝ), (-3258404689/10000000000 : ℝ)] ![(42328922235549/100000000000000 : ℝ), (34019310330019/100000000000000 : ℝ), (1478235463989/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1024794333/2000000000 : ℝ)|^9 ≤ (42328922235549/100000000000000 : ℝ)^7
        have hw : |(1024794333/2000000000 : ℝ)|=(1024794333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34584101/80000000 : ℝ)|^9 ≤ (34019310330019/100000000000000 : ℝ)^7
        have hw : |(34584101/80000000 : ℝ)|=(34584101/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3258404689/10000000000 : ℝ)|^9 ≤ (1478235463989/6250000000000 : ℝ)^7
        have hw : |(-3258404689/10000000000 : ℝ)|=(3258404689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1479844839/2500000000 : ℝ)*x 0 + (-579450783/2500000000 : ℝ)*x 1 + (2149570067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479844839/2500000000 : ℝ)^9 ≤ (50957982243083/100000000000000 : ℝ)^7 := by
    have hnat : (1479844839 : ℕ)^9*100000000000000^7 ≤ 50957982243083^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479844839 2500000000 50957982243083 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579450783/2500000000 : ℝ)^9 ≤ (15264052252723/100000000000000 : ℝ)^7 := by
    have hnat : (579450783 : ℕ)^9*100000000000000^7 ≤ 15264052252723^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579450783 2500000000 15264052252723 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149570067/5000000000 : ℝ)^9 ≤ (33777965492379/100000000000000 : ℝ)^7 := by
    have hnat : (2149570067 : ℕ)^9*100000000000000^7 ≤ 33777965492379^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149570067 5000000000 33777965492379 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1479844839/2500000000 : ℝ), (-579450783/2500000000 : ℝ), (2149570067/5000000000 : ℝ)] ![(50957982243083/100000000000000 : ℝ), (15264052252723/100000000000000 : ℝ), (33777965492379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1479844839/2500000000 : ℝ)|^9 ≤ (50957982243083/100000000000000 : ℝ)^7
        have hw : |(1479844839/2500000000 : ℝ)|=(1479844839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579450783/2500000000 : ℝ)|^9 ≤ (15264052252723/100000000000000 : ℝ)^7
        have hw : |(-579450783/2500000000 : ℝ)|=(579450783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2149570067/5000000000 : ℝ)|^9 ≤ (33777965492379/100000000000000 : ℝ)^7
        have hw : |(2149570067/5000000000 : ℝ)|=(2149570067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5581067317/10000000000 : ℝ)*x 0 + (-115588/390625 : ℝ)*x 1 + (-4108050749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5581067317/10000000000 : ℝ)^9 ≤ (47244446354491/100000000000000 : ℝ)^7 := by
    have hnat : (5581067317 : ℕ)^9*100000000000000^7 ≤ 47244446354491^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581067317 10000000000 47244446354491 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115588/390625 : ℝ)^9 ≤ (2611941845377/12500000000000 : ℝ)^7 := by
    have hnat : (115588 : ℕ)^9*12500000000000^7 ≤ 2611941845377^7*390625^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115588 390625 2611941845377 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4108050749/10000000000 : ℝ)^9 ≤ (31860018864803/100000000000000 : ℝ)^7 := by
    have hnat : (4108050749 : ℕ)^9*100000000000000^7 ≤ 31860018864803^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108050749 10000000000 31860018864803 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5581067317/10000000000 : ℝ), (-115588/390625 : ℝ), (-4108050749/10000000000 : ℝ)] ![(47244446354491/100000000000000 : ℝ), (2611941845377/12500000000000 : ℝ), (31860018864803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5581067317/10000000000 : ℝ)|^9 ≤ (47244446354491/100000000000000 : ℝ)^7
        have hw : |(5581067317/10000000000 : ℝ)|=(5581067317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115588/390625 : ℝ)|^9 ≤ (2611941845377/12500000000000 : ℝ)^7
        have hw : |(-115588/390625 : ℝ)|=(115588/390625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4108050749/10000000000 : ℝ)|^9 ≤ (31860018864803/100000000000000 : ℝ)^7
        have hw : |(-4108050749/10000000000 : ℝ)|=(4108050749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (33889681/10000000000 : ℝ)*x 0 + (-271753157/500000000 : ℝ)*x 1 + (-777084831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33889681/10000000000 : ℝ)^9 ≤ (52138977/78125000000 : ℝ)^7 := by
    have hnat : (33889681 : ℕ)^9*78125000000^7 ≤ 52138977^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33889681 10000000000 52138977 78125000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271753157/500000000 : ℝ)^9 ≤ (22830675834973/50000000000000 : ℝ)^7 := by
    have hnat : (271753157 : ℕ)^9*50000000000000^7 ≤ 22830675834973^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271753157 500000000 22830675834973 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777084831/1250000000 : ℝ)^9 ≤ (27135955210879/50000000000000 : ℝ)^7 := by
    have hnat : (777084831 : ℕ)^9*50000000000000^7 ≤ 27135955210879^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777084831 1250000000 27135955210879 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33889681/10000000000 : ℝ), (-271753157/500000000 : ℝ), (-777084831/1250000000 : ℝ)] ![(52138977/78125000000 : ℝ), (22830675834973/50000000000000 : ℝ), (27135955210879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33889681/10000000000 : ℝ)|^9 ≤ (52138977/78125000000 : ℝ)^7
        have hw : |(33889681/10000000000 : ℝ)|=(33889681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271753157/500000000 : ℝ)|^9 ≤ (22830675834973/50000000000000 : ℝ)^7
        have hw : |(-271753157/500000000 : ℝ)|=(271753157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-777084831/1250000000 : ℝ)|^9 ≤ (27135955210879/50000000000000 : ℝ)^7
        have hw : |(-777084831/1250000000 : ℝ)|=(777084831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2516558217/5000000000 : ℝ)*x 0 + (702441973/2000000000 : ℝ)*x 1 + (-167232183/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2516558217/5000000000 : ℝ)^9 ≤ (10341595597421/25000000000000 : ℝ)^7 := by
    have hnat : (2516558217 : ℕ)^9*25000000000000^7 ≤ 10341595597421^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516558217 5000000000 10341595597421 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702441973/2000000000 : ℝ)^9 ≤ (13023157953167/50000000000000 : ℝ)^7 := by
    have hnat : (702441973 : ℕ)^9*50000000000000^7 ≤ 13023157953167^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702441973 2000000000 13023157953167 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167232183/400000000 : ℝ)^9 ≤ (32587301686109/100000000000000 : ℝ)^7 := by
    have hnat : (167232183 : ℕ)^9*100000000000000^7 ≤ 32587301686109^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167232183 400000000 32587301686109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2516558217/5000000000 : ℝ), (702441973/2000000000 : ℝ), (-167232183/400000000 : ℝ)] ![(10341595597421/25000000000000 : ℝ), (13023157953167/50000000000000 : ℝ), (32587301686109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2516558217/5000000000 : ℝ)|^9 ≤ (10341595597421/25000000000000 : ℝ)^7
        have hw : |(2516558217/5000000000 : ℝ)|=(2516558217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702441973/2000000000 : ℝ)|^9 ≤ (13023157953167/50000000000000 : ℝ)^7
        have hw : |(702441973/2000000000 : ℝ)|=(702441973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-167232183/400000000 : ℝ)|^9 ≤ (32587301686109/100000000000000 : ℝ)^7
        have hw : |(-167232183/400000000 : ℝ)|=(167232183/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (69433121/100000000 : ℝ)*x 0 + (-495549033/2000000000 : ℝ)*x 1 + (2949416099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69433121/100000000 : ℝ)^9 ≤ (62560473383553/100000000000000 : ℝ)^7 := by
    have hnat : (69433121 : ℕ)^9*100000000000000^7 ≤ 62560473383553^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69433121 100000000 62560473383553 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495549033/2000000000 : ℝ)^9 ≤ (8315722085707/50000000000000 : ℝ)^7 := by
    have hnat : (495549033 : ℕ)^9*50000000000000^7 ≤ 8315722085707^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495549033 2000000000 8315722085707 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949416099/10000000000 : ℝ)^9 ≤ (5202020608811/25000000000000 : ℝ)^7 := by
    have hnat : (2949416099 : ℕ)^9*25000000000000^7 ≤ 5202020608811^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949416099 10000000000 5202020608811 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(69433121/100000000 : ℝ), (-495549033/2000000000 : ℝ), (2949416099/10000000000 : ℝ)] ![(62560473383553/100000000000000 : ℝ), (8315722085707/50000000000000 : ℝ), (5202020608811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(69433121/100000000 : ℝ)|^9 ≤ (62560473383553/100000000000000 : ℝ)^7
        have hw : |(69433121/100000000 : ℝ)|=(69433121/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495549033/2000000000 : ℝ)|^9 ≤ (8315722085707/50000000000000 : ℝ)^7
        have hw : |(-495549033/2000000000 : ℝ)|=(495549033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949416099/10000000000 : ℝ)|^9 ≤ (5202020608811/25000000000000 : ℝ)^7
        have hw : |(2949416099/10000000000 : ℝ)|=(2949416099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2973972431/5000000000 : ℝ)*x 0 + (-3108671159/10000000000 : ℝ)*x 1 + (-3555728631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2973972431/5000000000 : ℝ)^9 ≤ (6409296407073/12500000000000 : ℝ)^7 := by
    have hnat : (2973972431 : ℕ)^9*12500000000000^7 ≤ 6409296407073^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2973972431 5000000000 6409296407073 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3108671159/10000000000 : ℝ)^9 ≤ (11131819486153/50000000000000 : ℝ)^7 := by
    have hnat : (3108671159 : ℕ)^9*50000000000000^7 ≤ 11131819486153^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3108671159 10000000000 11131819486153 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3555728631/10000000000 : ℝ)^9 ≤ (6615497438249/25000000000000 : ℝ)^7 := by
    have hnat : (3555728631 : ℕ)^9*25000000000000^7 ≤ 6615497438249^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3555728631 10000000000 6615497438249 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2973972431/5000000000 : ℝ), (-3108671159/10000000000 : ℝ), (-3555728631/10000000000 : ℝ)] ![(6409296407073/12500000000000 : ℝ), (11131819486153/50000000000000 : ℝ), (6615497438249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2973972431/5000000000 : ℝ)|^9 ≤ (6409296407073/12500000000000 : ℝ)^7
        have hw : |(2973972431/5000000000 : ℝ)|=(2973972431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3108671159/10000000000 : ℝ)|^9 ≤ (11131819486153/50000000000000 : ℝ)^7
        have hw : |(-3108671159/10000000000 : ℝ)|=(3108671159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3555728631/10000000000 : ℝ)|^9 ≤ (6615497438249/25000000000000 : ℝ)^7
        have hw : |(-3555728631/10000000000 : ℝ)|=(3555728631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (33908827/10000000000 : ℝ)*x 0 + (-125037463/200000000 : ℝ)*x 1 + (-1349605471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33908827/10000000000 : ℝ)^9 ≤ (13357274111/20000000000000 : ℝ)^7 := by
    have hnat : (33908827 : ℕ)^9*20000000000000^7 ≤ 13357274111^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33908827 10000000000 13357274111 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125037463/200000000 : ℝ)^9 ≤ (13666816213017/25000000000000 : ℝ)^7 := by
    have hnat : (125037463 : ℕ)^9*25000000000000^7 ≤ 13666816213017^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125037463 200000000 13666816213017 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349605471/2500000000 : ℝ)^9 ≤ (5658243596249/12500000000000 : ℝ)^7 := by
    have hnat : (1349605471 : ℕ)^9*12500000000000^7 ≤ 5658243596249^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349605471 2500000000 5658243596249 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33908827/10000000000 : ℝ), (-125037463/200000000 : ℝ), (-1349605471/2500000000 : ℝ)] ![(13357274111/20000000000000 : ℝ), (13666816213017/25000000000000 : ℝ), (5658243596249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33908827/10000000000 : ℝ)|^9 ≤ (13357274111/20000000000000 : ℝ)^7
        have hw : |(33908827/10000000000 : ℝ)|=(33908827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125037463/200000000 : ℝ)|^9 ≤ (13666816213017/25000000000000 : ℝ)^7
        have hw : |(-125037463/200000000 : ℝ)|=(125037463/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1349605471/2500000000 : ℝ)|^9 ≤ (5658243596249/12500000000000 : ℝ)^7
        have hw : |(-1349605471/2500000000 : ℝ)|=(1349605471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7017084777/10000000000 : ℝ)*x 0 + (1438888403/5000000000 : ℝ)*x 1 + (-2453567573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7017084777/10000000000 : ℝ)^9 ≤ (15854096974527/25000000000000 : ℝ)^7 := by
    have hnat : (7017084777 : ℕ)^9*25000000000000^7 ≤ 15854096974527^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7017084777 10000000000 15854096974527 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1438888403/5000000000 : ℝ)^9 ≤ (1260033272669/6250000000000 : ℝ)^7 := by
    have hnat : (1438888403 : ℕ)^9*6250000000000^7 ≤ 1260033272669^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438888403 5000000000 1260033272669 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2453567573/10000000000 : ℝ)^9 ≤ (205288496651/1250000000000 : ℝ)^7 := by
    have hnat : (2453567573 : ℕ)^9*1250000000000^7 ≤ 205288496651^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453567573 10000000000 205288496651 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7017084777/10000000000 : ℝ), (1438888403/5000000000 : ℝ), (-2453567573/10000000000 : ℝ)] ![(15854096974527/25000000000000 : ℝ), (1260033272669/6250000000000 : ℝ), (205288496651/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7017084777/10000000000 : ℝ)|^9 ≤ (15854096974527/25000000000000 : ℝ)^7
        have hw : |(7017084777/10000000000 : ℝ)|=(7017084777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1438888403/5000000000 : ℝ)|^9 ≤ (1260033272669/6250000000000 : ℝ)^7
        have hw : |(1438888403/5000000000 : ℝ)|=(1438888403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2453567573/10000000000 : ℝ)|^9 ≤ (205288496651/1250000000000 : ℝ)^7
        have hw : |(-2453567573/10000000000 : ℝ)|=(2453567573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (991654287/2000000000 : ℝ)*x 0 + (-839342063/2000000000 : ℝ)*x 1 + (447259857/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991654287/2000000000 : ℝ)^9 ≤ (40577175353963/100000000000000 : ℝ)^7 := by
    have hnat : (991654287 : ℕ)^9*100000000000000^7 ≤ 40577175353963^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991654287 2000000000 40577175353963 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (839342063/2000000000 : ℝ)^9 ≤ (32746787713987/100000000000000 : ℝ)^7 := by
    have hnat : (839342063 : ℕ)^9*100000000000000^7 ≤ 32746787713987^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839342063 2000000000 32746787713987 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447259857/1250000000 : ℝ)^9 ≤ (26676036917037/100000000000000 : ℝ)^7 := by
    have hnat : (447259857 : ℕ)^9*100000000000000^7 ≤ 26676036917037^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447259857 1250000000 26676036917037 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(991654287/2000000000 : ℝ), (-839342063/2000000000 : ℝ), (447259857/1250000000 : ℝ)] ![(40577175353963/100000000000000 : ℝ), (32746787713987/100000000000000 : ℝ), (26676036917037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(991654287/2000000000 : ℝ)|^9 ≤ (40577175353963/100000000000000 : ℝ)^7
        have hw : |(991654287/2000000000 : ℝ)|=(991654287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-839342063/2000000000 : ℝ)|^9 ≤ (32746787713987/100000000000000 : ℝ)^7
        have hw : |(-839342063/2000000000 : ℝ)|=(839342063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447259857/1250000000 : ℝ)|^9 ≤ (26676036917037/100000000000000 : ℝ)^7
        have hw : |(447259857/1250000000 : ℝ)|=(447259857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310036_s1_s1_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5945960909/10000000000 : ℝ)*x 0 + (-3577115043/10000000000 : ℝ)*x 1 + (-617759691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5945960909/10000000000 : ℝ)^9 ≤ (12813095778277/25000000000000 : ℝ)^7 := by
    have hnat : (5945960909 : ℕ)^9*25000000000000^7 ≤ 12813095778277^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5945960909 10000000000 12813095778277 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3577115043/10000000000 : ℝ)^9 ≤ (13333399309829/50000000000000 : ℝ)^7 := by
    have hnat : (3577115043 : ℕ)^9*50000000000000^7 ≤ 13333399309829^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577115043 10000000000 13333399309829 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617759691/2000000000 : ℝ)^9 ≤ (2760102282397/12500000000000 : ℝ)^7 := by
    have hnat : (617759691 : ℕ)^9*12500000000000^7 ≤ 2760102282397^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617759691 2000000000 2760102282397 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5945960909/10000000000 : ℝ), (-3577115043/10000000000 : ℝ), (-617759691/2000000000 : ℝ)] ![(12813095778277/25000000000000 : ℝ), (13333399309829/50000000000000 : ℝ), (2760102282397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5945960909/10000000000 : ℝ)|^9 ≤ (12813095778277/25000000000000 : ℝ)^7
        have hw : |(5945960909/10000000000 : ℝ)|=(5945960909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3577115043/10000000000 : ℝ)|^9 ≤ (13333399309829/50000000000000 : ℝ)^7
        have hw : |(-3577115043/10000000000 : ℝ)|=(3577115043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-617759691/2000000000 : ℝ)|^9 ≤ (2760102282397/12500000000000 : ℝ)^7
        have hw : |(-617759691/2000000000 : ℝ)|=(617759691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310036_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((27033/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27033/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-15963/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-15963/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-20709/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-20709/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27421/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-27421/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-55163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-55163/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (27033/50000 : ℝ) ^ (35/8 : ℝ) ≤ (1696225387349416637/25000000000000000000 : ℝ) := by
    have hpowers : (27033/50000 : ℝ)^35 ≤ (1696225387349416637/25000000000000000000 : ℝ)^8 := by
      have hnat : (27033 : ℕ)^35*25000000000000000000^8 ≤ 1696225387349416637^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27033 50000 1696225387349416637 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27033/50000 : ℝ)) (X := (1696225387349416637/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (26696225387349416637/25000000000000000000 : ℝ) ≤ (10151180205336589/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26696225387349416637/25000000000000000000 : ℝ)^8 ≤ (10151180205336589/10000000000000000 : ℝ)^35 := by
      have hnat : (26696225387349416637 : ℕ)^8*10000000000000000^35 ≤ 10151180205336589^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26696225387349416637 25000000000000000000 10151180205336589 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10151180205336589/10000000000000000 : ℝ)) (X := (26696225387349416637/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (14196225387349416637/12500000000000000000 : ℝ) ≤ (2059024477264943/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (14196225387349416637/12500000000000000000 : ℝ)^8 ≤ (2059024477264943/2000000000000000 : ℝ)^35 := by
      have hnat : (14196225387349416637 : ℕ)^8*2000000000000000^35 ≤ 2059024477264943^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14196225387349416637 12500000000000000000 2059024477264943 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2059024477264943/2000000000000000 : ℝ)) (X := (14196225387349416637/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(50393401778863/1802200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23990363498021/901100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (27033/50000 : ℝ)) (alpha := (50393401778863/1802200000000000 : ℝ)) (beta := (23990363498021/901100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (27033/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(50393401778863/1802200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23990363498021/901100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (15963/20000 : ℝ) ^ (35/8 : ℝ) ≤ (37292351254636004637/100000000000000000000 : ℝ) := by
    have hpowers : (15963/20000 : ℝ)^35 ≤ (37292351254636004637/100000000000000000000 : ℝ)^8 := by
      have hnat : (15963 : ℕ)^35*100000000000000000000^8 ≤ 37292351254636004637^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15963 20000 37292351254636004637 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15963/20000 : ℝ)) (X := (37292351254636004637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (137292351254636004637/100000000000000000000 : ℝ) ≤ (10751325765734459/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (137292351254636004637/100000000000000000000 : ℝ)^8 ≤ (10751325765734459/10000000000000000 : ℝ)^35 := by
      have hnat : (137292351254636004637 : ℕ)^8*10000000000000000^35 ≤ 10751325765734459^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        137292351254636004637 100000000000000000000 10751325765734459 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10751325765734459/10000000000000000 : ℝ)) (X := (137292351254636004637/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (87292351254636004637/50000000000000000000 : ℝ) ≤ (11358361844558137/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (87292351254636004637/50000000000000000000 : ℝ)^8 ≤ (11358361844558137/10000000000000000 : ℝ)^35 := by
      have hnat : (87292351254636004637 : ℕ)^8*10000000000000000^35 ≤ 11358361844558137^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87292351254636004637 50000000000000000000 11358361844558137 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11358361844558137/10000000000000000 : ℝ)) (X := (87292351254636004637/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(751325765734459/7981500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(303518039411839/3990750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (15963/20000 : ℝ)) (alpha := (751325765734459/7981500000000000 : ℝ)) (beta := (303518039411839/3990750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15963/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(751325765734459/7981500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(303518039411839/3990750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20709/25000 : ℝ) ^ (35/8 : ℝ) ≤ (438741431123976043/1000000000000000000 : ℝ) := by
    have hpowers : (20709/25000 : ℝ)^35 ≤ (438741431123976043/1000000000000000000 : ℝ)^8 := by
      have hnat : (20709 : ℕ)^35*1000000000000000000^8 ≤ 438741431123976043^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20709 25000 438741431123976043 1000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20709/25000 : ℝ)) (X := (438741431123976043/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1438741431123976043/1000000000000000000 : ℝ) ≤ (1358377113789551/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1438741431123976043/1000000000000000000 : ℝ)^8 ≤ (1358377113789551/1250000000000000 : ℝ)^35 := by
      have hnat : (1438741431123976043 : ℕ)^8*1250000000000000^35 ≤ 1358377113789551^35*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1438741431123976043 1000000000000000000 1358377113789551 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1358377113789551/1250000000000000 : ℝ)) (X := (1438741431123976043/1000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (938741431123976043/500000000000000000 : ℝ) ≤ (2887165380755479/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (938741431123976043/500000000000000000 : ℝ)^8 ≤ (2887165380755479/2500000000000000 : ℝ)^35 := by
      have hnat : (938741431123976043 : ℕ)^8*2500000000000000^35 ≤ 2887165380755479^35*500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        938741431123976043 500000000000000000 2887165380755479 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2887165380755479/2500000000000000 : ℝ)) (X := (938741431123976043/500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(36125704596517/345150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(18934572575153/230100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (20709/25000 : ℝ)) (alpha := (36125704596517/345150000000000 : ℝ)) (beta := (18934572575153/230100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (20709/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(36125704596517/345150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(18934572575153/230100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1163535339/2000000000 : ℝ)*X 1 0+(3394825387/10000000000 : ℝ)*X 1 1+(-856637983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((662971347/1250000000 : ℝ)*X 0 0+(-3718573501/10000000000 : ℝ)*X 0 1+(-3686694627/10000000000 : ℝ)*X 0 2+(662971347/1250000000 : ℝ)*X 1 0+(-3718573501/10000000000 : ℝ)*X 1 1+(-3686694627/10000000000 : ℝ)*X 1 2+(662971347/1250000000 : ℝ)*X 2 0+(-3718573501/10000000000 : ℝ)*X 2 1+(-3686694627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-185961889/10000000000 : ℝ)*X 0 0+(-406767877/625000000 : ℝ)*X 0 1+(-2538829801/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1024794333/2000000000 : ℝ)*X 1 0+(34584101/80000000 : ℝ)*X 1 1+(-3258404689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1479844839/2500000000 : ℝ)*X 2 0+(-579450783/2500000000 : ℝ)*X 2 1+(2149570067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5581067317/10000000000 : ℝ)*X 0 0+(-115588/390625 : ℝ)*X 0 1+(-4108050749/10000000000 : ℝ)*X 0 2+(5581067317/10000000000 : ℝ)*X 1 0+(-115588/390625 : ℝ)*X 1 1+(-4108050749/10000000000 : ℝ)*X 1 2+(5581067317/10000000000 : ℝ)*X 2 0+(-115588/390625 : ℝ)*X 2 1+(-4108050749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((33889681/10000000000 : ℝ)*X 0 0+(-271753157/500000000 : ℝ)*X 0 1+(-777084831/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2516558217/5000000000 : ℝ)*X 1 0+(702441973/2000000000 : ℝ)*X 1 1+(-167232183/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((69433121/100000000 : ℝ)*X 2 0+(-495549033/2000000000 : ℝ)*X 2 1+(2949416099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((2973972431/5000000000 : ℝ)*X 0 0+(-3108671159/10000000000 : ℝ)*X 0 1+(-3555728631/10000000000 : ℝ)*X 0 2+(2973972431/5000000000 : ℝ)*X 1 0+(-3108671159/10000000000 : ℝ)*X 1 1+(-3555728631/10000000000 : ℝ)*X 1 2+(2973972431/5000000000 : ℝ)*X 2 0+(-3108671159/10000000000 : ℝ)*X 2 1+(-3555728631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((33908827/10000000000 : ℝ)*X 0 0+(-125037463/200000000 : ℝ)*X 0 1+(-1349605471/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((7017084777/10000000000 : ℝ)*X 1 0+(1438888403/5000000000 : ℝ)*X 1 1+(-2453567573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((991654287/2000000000 : ℝ)*X 2 0+(-839342063/2000000000 : ℝ)*X 2 1+(447259857/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((5945960909/10000000000 : ℝ)*X 0 0+(-3577115043/10000000000 : ℝ)*X 0 1+(-617759691/2000000000 : ℝ)*X 0 2+(5945960909/10000000000 : ℝ)*X 1 0+(-3577115043/10000000000 : ℝ)*X 1 1+(-617759691/2000000000 : ℝ)*X 1 2+(5945960909/10000000000 : ℝ)*X 2 0+(-3577115043/10000000000 : ℝ)*X 2 1+(-617759691/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310036_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34565769501715373960140123/3060905250000000000000000000000 : ℝ) := by norm_num
    linear_combination (574143189617/1000000000000 : ℝ)*(base39) + (64229049439/250000000000 : ℝ)*(base50) + (10349/3125000000 : ℝ)*(base60) + (2132935626067/1000000000000 : ℝ)*(major_s1_0) + (2132935626067/1000000000000 : ℝ)*(major_s1_1) + (2132935626067/1000000000000 : ℝ)*(major_s1_2) + (29459/781250000 : ℝ)*(sp_s1_6) + (2947412430509/1000000000000 : ℝ)*(sp_s1_7) + (2947491972879/1000000000000 : ℝ)*(sp_s1_8) + (2947500172447/1000000000000 : ℝ)*(sp_s1_9) + (329568432803/250000000000 : ℝ)*(sp_s1_13) + (12815259/200000000000 : ℝ)*(sp_s1_15) + (28723733/200000000000 : ℝ)*(sp_s1_20) + (55876727/1000000000000 : ℝ)*(sp_s1_22) + (1318311438731/1000000000000 : ℝ)*(f.failure) + (1473778024587/500000000000 : ℝ)*(f.sum) + (6259444899113175143/18365431500000000000000000000000 : ℝ)*base63 + (41986449482329/230100000000000000000000000 : ℝ)*base65 + (932124733119737/3990750000000000000000000000 : ℝ)*base67 + (24353368387201/86287500000000000000000000 : ℝ)*base69 + (1718427058018405999/4146862200000000000000000000000 : ℝ)*base71 + (97977914197353/901100000000000000000000000 : ℝ)*base72 + (2436808927279603/7981500000000000000000000000 : ℝ)*base75 + (181008722249799/1802200000000000000000000000 : ℝ)*base76 + (34506486274249110719/71921296500000000000000000000000 : ℝ)*base79 + (95317/100000000000000000 : ℝ)*base86 + (95317/100000000000000000 : ℝ)*base88 + (95317/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27421/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-27421/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5250170116284367828535773451/1149242383656250000000000000000000 : ℝ) := by norm_num
    linear_combination (276367762133/500000000000 : ℝ)*(base7) + (1682167254663/1000000000000 : ℝ)*(base39) + (1057758874507/1000000000000 : ℝ)*(base40) + (513639/1000000000000 : ℝ)*(base60) + (121096696821/31250000000 : ℝ)*(major_s1_0) + (121096696821/31250000000 : ℝ)*(major_s1_1) + (121096696821/31250000000 : ℝ)*(major_s1_2) + (43308801/1000000000000 : ℝ)*(sp_s1_1) + (2907493/200000000000 : ℝ)*(sp_s1_9) + (1695593/125000000000 : ℝ)*(sp_s1_13) + (2510703361257/500000000000 : ℝ)*(sp_s1_14) + (5021363413713/1000000000000 : ℝ)*(sp_s1_15) + (5021392185049/1000000000000 : ℝ)*(sp_s1_16) + (589563174951/200000000000 : ℝ)*(sp_s1_19) + (74846684851/31250000000 : ℝ)*(f.failure) + (2510703361257/500000000000 : ℝ)*(f.sum) + (352644833641598813/765226312500000000000000000000 : ℝ)*base62 + (20270057039761/38350000000000000000000000 : ℝ)*base64 + (184721198073411/1330250000000000000000000000 : ℝ)*base66 + (33810366950267/115050000000000000000000000 : ℝ)*base68 + (141229559130320263/345571850000000000000000000000 : ℝ)*base70 + (17328278675113/56318750000000000000000000 : ℝ)*base72 + (84338575744679/665125000000000000000000000 : ℝ)*base75 + (44356580447383/225275000000000000000000000 : ℝ)*base76 + (157640060125320179/2996720687500000000000000000000 : ℝ)*base78 + (2157/3125000000000000 : ℝ)*base86 + (2157/3125000000000000 : ℝ)*base88 + (2157/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-55163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-55163/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7992549772963656321520976351/430965893871093750000000000000000 : ℝ) := by norm_num
    linear_combination (546973788731/1000000000000 : ℝ)*(base7) + (424589688367/250000000000 : ℝ)*(base39) + (152370872079/250000000000 : ℝ)*(base40) + (4217079/1000000000000 : ℝ)*(base50) + (3091561/1000000000000 : ℝ)*(base60) + (3898138554389/1000000000000 : ℝ)*(major_s1_0) + (3898138554389/1000000000000 : ℝ)*(major_s1_1) + (3898138554389/1000000000000 : ℝ)*(major_s1_2) + (6008379/100000000000 : ℝ)*(sp_s1_8) + (75841209/1000000000000 : ℝ)*(sp_s1_16) + (505672588649/100000000000 : ℝ)*(sp_s1_20) + (50566658027/10000000000 : ℝ)*(sp_s1_21) + (5056650045281/1000000000000 : ℝ)*(sp_s1_22) + (295631075287/100000000000 : ℝ)*(sp_s1_25) + (2409336964139/1000000000000 : ℝ)*(f.failure) + (505672588649/100000000000 : ℝ)*(f.sum) + (11510039703377988419/18365431500000000000000000000000 : ℝ)*base62 + (28343470102583/230100000000000000000000000 : ℝ)*base65 + (1076636423795621/3990750000000000000000000000 : ℝ)*base66 + (62561822803087/345150000000000000000000000 : ℝ)*base68 + (161888970937602367/4146862200000000000000000000000 : ℝ)*base70 + (199445683267231/901100000000000000000000000 : ℝ)*base72 + (5532480207474199/7981500000000000000000000000 : ℝ)*base74 + (26364664189907/1802200000000000000000000000 : ℝ)*base77 + (47148663065775557477/71921296500000000000000000000000 : ℝ)*base78 + (41227/100000000000000000 : ℝ)*base87 + (41227/100000000000000000 : ℝ)*base89 + (41227/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((27033/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27033/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-15963/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-15963/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-20709/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-20709/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27421/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-27421/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-55163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-55163/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310036_s1 p hpa hpb X hX hprev0

#print axioms solution

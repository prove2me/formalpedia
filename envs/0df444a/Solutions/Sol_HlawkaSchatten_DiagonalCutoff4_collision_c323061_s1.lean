-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c323061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:52:58.429302+00:00
-- url     : https://prove2.me/submissions/c79dcee7-bb35-4ccd-b2f8-41259c25137b

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
theorem collision_support_c323061_s1_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-877772569/5000000000 : ℝ)*x 0 + (4439766871/10000000000 : ℝ)*x 1 + (234363323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (877772569/5000000000 : ℝ)^21 ≤ (11658068121681/100000000000000 : ℝ)^17 := by
    have hnat : (877772569 : ℕ)^21*100000000000000^17 ≤ 11658068121681^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877772569 5000000000 11658068121681 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4439766871/10000000000 : ℝ)^21 ≤ (18338174120081/50000000000000 : ℝ)^17 := by
    have hnat : (4439766871 : ℕ)^21*50000000000000^17 ≤ 18338174120081^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439766871 10000000000 18338174120081 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234363323/400000000 : ℝ)^21 ≤ (51665583617691/100000000000000 : ℝ)^17 := by
    have hnat : (234363323 : ℕ)^21*100000000000000^17 ≤ 51665583617691^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234363323 400000000 51665583617691 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-877772569/5000000000 : ℝ), (4439766871/10000000000 : ℝ), (234363323/400000000 : ℝ)] ![(11658068121681/100000000000000 : ℝ), (18338174120081/50000000000000 : ℝ), (51665583617691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-877772569/5000000000 : ℝ)|^21 ≤ (11658068121681/100000000000000 : ℝ)^17
        have hw : |(-877772569/5000000000 : ℝ)|=(877772569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4439766871/10000000000 : ℝ)|^21 ≤ (18338174120081/50000000000000 : ℝ)^17
        have hw : |(4439766871/10000000000 : ℝ)|=(4439766871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234363323/400000000 : ℝ)|^21 ≤ (51665583617691/100000000000000 : ℝ)^17
        have hw : |(234363323/400000000 : ℝ)|=(234363323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1178151333/2500000000 : ℝ)*x 0 + (6283899797/10000000000 : ℝ)*x 1 + (-766416487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178151333/2500000000 : ℝ)^21 ≤ (39480379818709/100000000000000 : ℝ)^17 := by
    have hnat : (1178151333 : ℕ)^21*100000000000000^17 ≤ 39480379818709^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178151333 2500000000 39480379818709 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6283899797/10000000000 : ℝ)^21 ≤ (56331819735787/100000000000000 : ℝ)^17 := by
    have hnat : (6283899797 : ℕ)^21*100000000000000^17 ≤ 56331819735787^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6283899797 10000000000 56331819735787 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766416487/10000000000 : ℝ)^21 ≤ (4187800429719/100000000000000 : ℝ)^17 := by
    have hnat : (766416487 : ℕ)^21*100000000000000^17 ≤ 4187800429719^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766416487 10000000000 4187800429719 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1178151333/2500000000 : ℝ), (6283899797/10000000000 : ℝ), (-766416487/10000000000 : ℝ)] ![(39480379818709/100000000000000 : ℝ), (56331819735787/100000000000000 : ℝ), (4187800429719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1178151333/2500000000 : ℝ)|^21 ≤ (39480379818709/100000000000000 : ℝ)^17
        have hw : |(1178151333/2500000000 : ℝ)|=(1178151333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6283899797/10000000000 : ℝ)|^21 ≤ (56331819735787/100000000000000 : ℝ)^17
        have hw : |(6283899797/10000000000 : ℝ)|=(6283899797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-766416487/10000000000 : ℝ)|^21 ≤ (4187800429719/100000000000000 : ℝ)^17
        have hw : |(-766416487/10000000000 : ℝ)|=(766416487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3248400683/5000000000 : ℝ)*x 0 + (503138913/2000000000 : ℝ)*x 1 + (3055800091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3248400683/5000000000 : ℝ)^21 ≤ (5869875687097/10000000000000 : ℝ)^17 := by
    have hnat : (3248400683 : ℕ)^21*10000000000000^17 ≤ 5869875687097^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3248400683 5000000000 5869875687097 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503138913/2000000000 : ℝ)^21 ≤ (1818177351641/10000000000000 : ℝ)^17 := by
    have hnat : (503138913 : ℕ)^21*10000000000000^17 ≤ 1818177351641^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503138913 2000000000 1818177351641 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3055800091/10000000000 : ℝ)^21 ≤ (4623893920261/20000000000000 : ℝ)^17 := by
    have hnat : (3055800091 : ℕ)^21*20000000000000^17 ≤ 4623893920261^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3055800091 10000000000 4623893920261 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3248400683/5000000000 : ℝ), (503138913/2000000000 : ℝ), (3055800091/10000000000 : ℝ)] ![(5869875687097/10000000000000 : ℝ), (1818177351641/10000000000000 : ℝ), (4623893920261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3248400683/5000000000 : ℝ)|^21 ≤ (5869875687097/10000000000000 : ℝ)^17
        have hw : |(3248400683/5000000000 : ℝ)|=(3248400683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503138913/2000000000 : ℝ)|^21 ≤ (1818177351641/10000000000000 : ℝ)^17
        have hw : |(503138913/2000000000 : ℝ)|=(503138913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3055800091/10000000000 : ℝ)|^21 ≤ (4623893920261/20000000000000 : ℝ)^17
        have hw : |(3055800091/10000000000 : ℝ)|=(3055800091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-219538093/1250000000 : ℝ)*x 0 + (3931165039/10000000000 : ℝ)*x 1 + (3162050549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219538093/1250000000 : ℝ)^21 ≤ (364509364457/3125000000000 : ℝ)^17 := by
    have hnat : (219538093 : ℕ)^21*3125000000000^17 ≤ 364509364457^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219538093 1250000000 364509364457 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3931165039/10000000000 : ℝ)^21 ≤ (31558366714751/100000000000000 : ℝ)^17 := by
    have hnat : (3931165039 : ℕ)^21*100000000000000^17 ≤ 31558366714751^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3931165039 10000000000 31558366714751 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3162050549/5000000000 : ℝ)^21 ≤ (11355466720861/20000000000000 : ℝ)^17 := by
    have hnat : (3162050549 : ℕ)^21*20000000000000^17 ≤ 11355466720861^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162050549 5000000000 11355466720861 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219538093/1250000000 : ℝ), (3931165039/10000000000 : ℝ), (3162050549/5000000000 : ℝ)] ![(364509364457/3125000000000 : ℝ), (31558366714751/100000000000000 : ℝ), (11355466720861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219538093/1250000000 : ℝ)|^21 ≤ (364509364457/3125000000000 : ℝ)^17
        have hw : |(-219538093/1250000000 : ℝ)|=(219538093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3931165039/10000000000 : ℝ)|^21 ≤ (31558366714751/100000000000000 : ℝ)^17
        have hw : |(3931165039/10000000000 : ℝ)|=(3931165039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3162050549/5000000000 : ℝ)|^21 ≤ (11355466720861/20000000000000 : ℝ)^17
        have hw : |(3162050549/5000000000 : ℝ)|=(3162050549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2145198579/5000000000 : ℝ)*x 0 + (-644802273/5000000000 : ℝ)*x 1 + (19791019/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145198579/5000000000 : ℝ)^21 ≤ (17579087314411/50000000000000 : ℝ)^17 := by
    have hnat : (2145198579 : ℕ)^21*50000000000000^17 ≤ 17579087314411^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145198579 5000000000 17579087314411 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644802273/5000000000 : ℝ)^21 ≤ (796438444521/10000000000000 : ℝ)^17 := by
    have hnat : (644802273 : ℕ)^21*10000000000000^17 ≤ 796438444521^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644802273 5000000000 796438444521 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19791019/31250000 : ℝ)^21 ≤ (28438720456819/50000000000000 : ℝ)^17 := by
    have hnat : (19791019 : ℕ)^21*50000000000000^17 ≤ 28438720456819^17*31250000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19791019 31250000 28438720456819 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145198579/5000000000 : ℝ), (-644802273/5000000000 : ℝ), (19791019/31250000 : ℝ)] ![(17579087314411/50000000000000 : ℝ), (796438444521/10000000000000 : ℝ), (28438720456819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145198579/5000000000 : ℝ)|^21 ≤ (17579087314411/50000000000000 : ℝ)^17
        have hw : |(2145198579/5000000000 : ℝ)|=(2145198579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-644802273/5000000000 : ℝ)|^21 ≤ (796438444521/10000000000000 : ℝ)^17
        have hw : |(-644802273/5000000000 : ℝ)|=(644802273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19791019/31250000 : ℝ)|^21 ≤ (28438720456819/50000000000000 : ℝ)^17
        have hw : |(19791019/31250000 : ℝ)|=(19791019/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (870793569/2000000000 : ℝ)*x 0 + (6937168237/10000000000 : ℝ)*x 1 + (-147083657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870793569/2000000000 : ℝ)^21 ≤ (17901401678653/50000000000000 : ℝ)^17 := by
    have hnat : (870793569 : ℕ)^21*50000000000000^17 ≤ 17901401678653^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870793569 2000000000 17901401678653 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6937168237/10000000000 : ℝ)^21 ≤ (63652188342617/100000000000000 : ℝ)^17 := by
    have hnat : (6937168237 : ℕ)^21*100000000000000^17 ≤ 63652188342617^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6937168237 10000000000 63652188342617 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147083657/10000000000 : ℝ)^21 ≤ (109001657497/20000000000000 : ℝ)^17 := by
    have hnat : (147083657 : ℕ)^21*20000000000000^17 ≤ 109001657497^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147083657 10000000000 109001657497 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870793569/2000000000 : ℝ), (6937168237/10000000000 : ℝ), (-147083657/10000000000 : ℝ)] ![(17901401678653/50000000000000 : ℝ), (63652188342617/100000000000000 : ℝ), (109001657497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870793569/2000000000 : ℝ)|^21 ≤ (17901401678653/50000000000000 : ℝ)^17
        have hw : |(870793569/2000000000 : ℝ)|=(870793569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6937168237/10000000000 : ℝ)|^21 ≤ (63652188342617/100000000000000 : ℝ)^17
        have hw : |(6937168237/10000000000 : ℝ)|=(6937168237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147083657/10000000000 : ℝ)|^21 ≤ (109001657497/20000000000000 : ℝ)^17
        have hw : |(-147083657/10000000000 : ℝ)|=(147083657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (51679083/80000000 : ℝ)*x 0 + (3714618607/10000000000 : ℝ)*x 1 + (228992231/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51679083/80000000 : ℝ)^21 ≤ (5828701656907/10000000000000 : ℝ)^17 := by
    have hnat : (51679083 : ℕ)^21*10000000000000^17 ≤ 5828701656907^17*80000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51679083 80000000 5828701656907 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3714618607/10000000000 : ℝ)^21 ≤ (14712537485403/50000000000000 : ℝ)^17 := by
    have hnat : (3714618607 : ℕ)^21*50000000000000^17 ≤ 14712537485403^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714618607 10000000000 14712537485403 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228992231/1250000000 : ℝ)^21 ≤ (12287908453433/100000000000000 : ℝ)^17 := by
    have hnat : (228992231 : ℕ)^21*100000000000000^17 ≤ 12287908453433^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228992231 1250000000 12287908453433 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51679083/80000000 : ℝ), (3714618607/10000000000 : ℝ), (228992231/1250000000 : ℝ)] ![(5828701656907/10000000000000 : ℝ), (14712537485403/50000000000000 : ℝ), (12287908453433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51679083/80000000 : ℝ)|^21 ≤ (5828701656907/10000000000000 : ℝ)^17
        have hw : |(51679083/80000000 : ℝ)|=(51679083/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3714618607/10000000000 : ℝ)|^21 ≤ (14712537485403/50000000000000 : ℝ)^17
        have hw : |(3714618607/10000000000 : ℝ)|=(3714618607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228992231/1250000000 : ℝ)|^21 ≤ (12287908453433/100000000000000 : ℝ)^17
        have hw : |(228992231/1250000000 : ℝ)|=(228992231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-884225807/10000000000 : ℝ)*x 0 + (2298377439/5000000000 : ℝ)*x 1 + (3159384423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884225807/10000000000 : ℝ)^21 ≤ (2498421478373/50000000000000 : ℝ)^17 := by
    have hnat : (884225807 : ℕ)^21*50000000000000^17 ≤ 2498421478373^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884225807 10000000000 2498421478373 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298377439/5000000000 : ℝ)^21 ≤ (2392809642599/6250000000000 : ℝ)^17 := by
    have hnat : (2298377439 : ℕ)^21*6250000000000^17 ≤ 2392809642599^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298377439 5000000000 2392809642599 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3159384423/5000000000 : ℝ)^21 ≤ (5671820275229/10000000000000 : ℝ)^17 := by
    have hnat : (3159384423 : ℕ)^21*10000000000000^17 ≤ 5671820275229^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3159384423 5000000000 5671820275229 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884225807/10000000000 : ℝ), (2298377439/5000000000 : ℝ), (3159384423/5000000000 : ℝ)] ![(2498421478373/50000000000000 : ℝ), (2392809642599/6250000000000 : ℝ), (5671820275229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884225807/10000000000 : ℝ)|^21 ≤ (2498421478373/50000000000000 : ℝ)^17
        have hw : |(-884225807/10000000000 : ℝ)|=(884225807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2298377439/5000000000 : ℝ)|^21 ≤ (2392809642599/6250000000000 : ℝ)^17
        have hw : |(2298377439/5000000000 : ℝ)|=(2298377439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3159384423/5000000000 : ℝ)|^21 ≤ (5671820275229/10000000000000 : ℝ)^17
        have hw : |(3159384423/5000000000 : ℝ)|=(3159384423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4270159253/10000000000 : ℝ)*x 0 + (-1324088449/10000000000 : ℝ)*x 1 + (6327793981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270159253/10000000000 : ℝ)^21 ≤ (34953424877771/100000000000000 : ℝ)^17 := by
    have hnat : (4270159253 : ℕ)^21*100000000000000^17 ≤ 34953424877771^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270159253 10000000000 34953424877771 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324088449/10000000000 : ℝ)^21 ≤ (4114141606663/50000000000000 : ℝ)^17 := by
    have hnat : (1324088449 : ℕ)^21*50000000000000^17 ≤ 4114141606663^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324088449 10000000000 4114141606663 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6327793981/10000000000 : ℝ)^21 ≤ (56818291906013/100000000000000 : ℝ)^17 := by
    have hnat : (6327793981 : ℕ)^21*100000000000000^17 ≤ 56818291906013^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6327793981 10000000000 56818291906013 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270159253/10000000000 : ℝ), (-1324088449/10000000000 : ℝ), (6327793981/10000000000 : ℝ)] ![(34953424877771/100000000000000 : ℝ), (4114141606663/50000000000000 : ℝ), (56818291906013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270159253/10000000000 : ℝ)|^21 ≤ (34953424877771/100000000000000 : ℝ)^17
        have hw : |(4270159253/10000000000 : ℝ)|=(4270159253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324088449/10000000000 : ℝ)|^21 ≤ (4114141606663/50000000000000 : ℝ)^17
        have hw : |(-1324088449/10000000000 : ℝ)|=(1324088449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6327793981/10000000000 : ℝ)|^21 ≤ (56818291906013/100000000000000 : ℝ)^17
        have hw : |(6327793981/10000000000 : ℝ)|=(6327793981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (704177401/1250000000 : ℝ)*x 0 + (715657101/1250000000 : ℝ)*x 1 + (-38104041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704177401/1250000000 : ℝ)^21 ≤ (24609353728301/50000000000000 : ℝ)^17 := by
    have hnat : (704177401 : ℕ)^21*50000000000000^17 ≤ 24609353728301^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704177401 1250000000 24609353728301 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715657101/1250000000 : ℝ)^21 ≤ (50211772616757/100000000000000 : ℝ)^17 := by
    have hnat : (715657101 : ℕ)^21*100000000000000^17 ≤ 50211772616757^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715657101 1250000000 50211772616757 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38104041/2500000000 : ℝ)^21 ≤ (142379978999/25000000000000 : ℝ)^17 := by
    have hnat : (38104041 : ℕ)^21*25000000000000^17 ≤ 142379978999^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38104041 2500000000 142379978999 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(704177401/1250000000 : ℝ), (715657101/1250000000 : ℝ), (-38104041/2500000000 : ℝ)] ![(24609353728301/50000000000000 : ℝ), (50211772616757/100000000000000 : ℝ), (142379978999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(704177401/1250000000 : ℝ)|^21 ≤ (24609353728301/50000000000000 : ℝ)^17
        have hw : |(704177401/1250000000 : ℝ)|=(704177401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(715657101/1250000000 : ℝ)|^21 ≤ (50211772616757/100000000000000 : ℝ)^17
        have hw : |(715657101/1250000000 : ℝ)|=(715657101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38104041/2500000000 : ℝ)|^21 ≤ (142379978999/25000000000000 : ℝ)^17
        have hw : |(-38104041/2500000000 : ℝ)|=(38104041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7705377431/10000000000 : ℝ)*x 0 + (2166083379/10000000000 : ℝ)*x 1 + (923735039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7705377431/10000000000 : ℝ)^21 ≤ (3623491070039/5000000000000 : ℝ)^17 := by
    have hnat : (7705377431 : ℕ)^21*5000000000000^17 ≤ 3623491070039^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7705377431 10000000000 3623491070039 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166083379/10000000000 : ℝ)^21 ≤ (15113444139529/100000000000000 : ℝ)^17 := by
    have hnat : (2166083379 : ℕ)^21*100000000000000^17 ≤ 15113444139529^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166083379 10000000000 15113444139529 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923735039/5000000000 : ℝ)^21 ≤ (12416734438031/100000000000000 : ℝ)^17 := by
    have hnat : (923735039 : ℕ)^21*100000000000000^17 ≤ 12416734438031^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923735039 5000000000 12416734438031 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7705377431/10000000000 : ℝ), (2166083379/10000000000 : ℝ), (923735039/5000000000 : ℝ)] ![(3623491070039/5000000000000 : ℝ), (15113444139529/100000000000000 : ℝ), (12416734438031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7705377431/10000000000 : ℝ)|^21 ≤ (3623491070039/5000000000000 : ℝ)^17
        have hw : |(7705377431/10000000000 : ℝ)|=(7705377431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166083379/10000000000 : ℝ)|^21 ≤ (15113444139529/100000000000000 : ℝ)^17
        have hw : |(2166083379/10000000000 : ℝ)|=(2166083379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923735039/5000000000 : ℝ)|^21 ≤ (12416734438031/100000000000000 : ℝ)^17
        have hw : |(923735039/5000000000 : ℝ)|=(923735039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-816888649/10000000000 : ℝ)*x 0 + (5184916293/10000000000 : ℝ)*x 1 + (2900998407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (816888649/10000000000 : ℝ)^21 ≤ (453107427901/10000000000000 : ℝ)^17 := by
    have hnat : (816888649 : ℕ)^21*10000000000000^17 ≤ 453107427901^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816888649 10000000000 453107427901 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184916293/10000000000 : ℝ)^21 ≤ (44424460363257/100000000000000 : ℝ)^17 := by
    have hnat : (5184916293 : ℕ)^21*100000000000000^17 ≤ 44424460363257^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184916293 10000000000 44424460363257 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2900998407/5000000000 : ℝ)^21 ≤ (51044465334967/100000000000000 : ℝ)^17 := by
    have hnat : (2900998407 : ℕ)^21*100000000000000^17 ≤ 51044465334967^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900998407 5000000000 51044465334967 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-816888649/10000000000 : ℝ), (5184916293/10000000000 : ℝ), (2900998407/5000000000 : ℝ)] ![(453107427901/10000000000000 : ℝ), (44424460363257/100000000000000 : ℝ), (51044465334967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-816888649/10000000000 : ℝ)|^21 ≤ (453107427901/10000000000000 : ℝ)^17
        have hw : |(-816888649/10000000000 : ℝ)|=(816888649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184916293/10000000000 : ℝ)|^21 ≤ (44424460363257/100000000000000 : ℝ)^17
        have hw : |(5184916293/10000000000 : ℝ)|=(5184916293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2900998407/5000000000 : ℝ)|^21 ≤ (51044465334967/100000000000000 : ℝ)^17
        have hw : |(2900998407/5000000000 : ℝ)|=(2900998407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5637185123/10000000000 : ℝ)*x 0 + (-806351653/10000000000 : ℝ)*x 1 + (42877607/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5637185123/10000000000 : ℝ)^21 ≤ (3078709680867/6250000000000 : ℝ)^17 := by
    have hnat : (5637185123 : ℕ)^21*6250000000000^17 ≤ 3078709680867^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637185123 10000000000 3078709680867 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806351653/10000000000 : ℝ)^21 ≤ (4458986146639/100000000000000 : ℝ)^17 := by
    have hnat : (806351653 : ℕ)^21*100000000000000^17 ≤ 4458986146639^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806351653 10000000000 4458986146639 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42877607/80000000 : ℝ)^21 ≤ (11570414736439/25000000000000 : ℝ)^17 := by
    have hnat : (42877607 : ℕ)^21*25000000000000^17 ≤ 11570414736439^17*80000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42877607 80000000 11570414736439 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5637185123/10000000000 : ℝ), (-806351653/10000000000 : ℝ), (42877607/80000000 : ℝ)] ![(3078709680867/6250000000000 : ℝ), (4458986146639/100000000000000 : ℝ), (11570414736439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5637185123/10000000000 : ℝ)|^21 ≤ (3078709680867/6250000000000 : ℝ)^17
        have hw : |(5637185123/10000000000 : ℝ)|=(5637185123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-806351653/10000000000 : ℝ)|^21 ≤ (4458986146639/100000000000000 : ℝ)^17
        have hw : |(-806351653/10000000000 : ℝ)|=(806351653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42877607/80000000 : ℝ)|^21 ≤ (11570414736439/25000000000000 : ℝ)^17
        have hw : |(42877607/80000000 : ℝ)|=(42877607/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4184861393/10000000000 : ℝ)*x 0 + (137548427/200000000 : ℝ)*x 1 + (-574189161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184861393/10000000000 : ℝ)^21 ≤ (34092971968669/100000000000000 : ℝ)^17 := by
    have hnat : (4184861393 : ℕ)^21*100000000000000^17 ≤ 34092971968669^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184861393 10000000000 34092971968669 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137548427/200000000 : ℝ)^21 ≤ (31487838153429/50000000000000 : ℝ)^17 := by
    have hnat : (137548427 : ℕ)^21*50000000000000^17 ≤ 31487838153429^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137548427 200000000 31487838153429 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574189161/10000000000 : ℝ)^21 ≤ (1465675853993/50000000000000 : ℝ)^17 := by
    have hnat : (574189161 : ℕ)^21*50000000000000^17 ≤ 1465675853993^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574189161 10000000000 1465675853993 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184861393/10000000000 : ℝ), (137548427/200000000 : ℝ), (-574189161/10000000000 : ℝ)] ![(34092971968669/100000000000000 : ℝ), (31487838153429/50000000000000 : ℝ), (1465675853993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184861393/10000000000 : ℝ)|^21 ≤ (34092971968669/100000000000000 : ℝ)^17
        have hw : |(4184861393/10000000000 : ℝ)|=(4184861393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137548427/200000000 : ℝ)|^21 ≤ (31487838153429/50000000000000 : ℝ)^17
        have hw : |(137548427/200000000 : ℝ)|=(137548427/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-574189161/10000000000 : ℝ)|^21 ≤ (1465675853993/50000000000000 : ℝ)^17
        have hw : |(-574189161/10000000000 : ℝ)|=(574189161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323061_s1_s1_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (13022377/16000000 : ℝ)*x 0 + (164442141/1000000000 : ℝ)*x 1 + (880705861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13022377/16000000 : ℝ)^21 ≤ (75723039497/97656250000 : ℝ)^17 := by
    have hnat : (13022377 : ℕ)^21*97656250000^17 ≤ 75723039497^17*16000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13022377 16000000 75723039497 97656250000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164442141/1000000000 : ℝ)^21 ≤ (2150679114559/20000000000000 : ℝ)^17 := by
    have hnat : (164442141 : ℕ)^21*20000000000000^17 ≤ 2150679114559^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164442141 1000000000 2150679114559 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880705861/5000000000 : ℝ)^21 ≤ (2926552992933/25000000000000 : ℝ)^17 := by
    have hnat : (880705861 : ℕ)^21*25000000000000^17 ≤ 2926552992933^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880705861 5000000000 2926552992933 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13022377/16000000 : ℝ), (164442141/1000000000 : ℝ), (880705861/5000000000 : ℝ)] ![(75723039497/97656250000 : ℝ), (2150679114559/20000000000000 : ℝ), (2926552992933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13022377/16000000 : ℝ)|^21 ≤ (75723039497/97656250000 : ℝ)^17
        have hw : |(13022377/16000000 : ℝ)|=(13022377/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164442141/1000000000 : ℝ)|^21 ≤ (2150679114559/20000000000000 : ℝ)^17
        have hw : |(164442141/1000000000 : ℝ)|=(164442141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880705861/5000000000 : ℝ)|^21 ≤ (2926552992933/25000000000000 : ℝ)^17
        have hw : |(880705861/5000000000 : ℝ)|=(880705861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323061_s1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((7001/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34623/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34623/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64553/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64553/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8029/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8029/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(901/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(901/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (7001/10000 : ℝ) ^ (83/16 : ℝ) ≤ (7865709578768143997/50000000000000000000 : ℝ) := by
    have hpowers : (7001/10000 : ℝ)^83 ≤ (7865709578768143997/50000000000000000000 : ℝ)^16 := by
      have hnat : (7001 : ℕ)^83*50000000000000000000^16 ≤ 7865709578768143997^16*10000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 10000 7865709578768143997 50000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/10000 : ℝ)) (X := (7865709578768143997/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (57865709578768143997/50000000000000000000 : ℝ) ≤ (5142822983683239/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (57865709578768143997/50000000000000000000 : ℝ)^16 ≤ (5142822983683239/5000000000000000 : ℝ)^83 := by
      have hnat : (57865709578768143997 : ℕ)^16*5000000000000000^83 ≤ 5142822983683239^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57865709578768143997 50000000000000000000 5142822983683239 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5142822983683239/5000000000000000 : ℝ)) (X := (57865709578768143997/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (32865709578768143997/25000000000000000000 : ℝ) ≤ (5270742365264987/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (32865709578768143997/25000000000000000000 : ℝ)^16 ≤ (5270742365264987/5000000000000000 : ℝ)^83 := by
      have hnat : (32865709578768143997 : ℕ)^16*5000000000000000^83 ≤ 5270742365264987^83*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32865709578768143997 25000000000000000000 5270742365264987 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5270742365264987/5000000000000000 : ℝ)) (X := (32865709578768143997/25000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(142822983683239/3500500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(31979845395437/875125000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (7001/10000 : ℝ)) (alpha := (142822983683239/3500500000000000 : ℝ)) (beta := (31979845395437/875125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7001/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(142822983683239/3500500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(31979845395437/875125000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (34623/50000 : ℝ) ^ (83/16 : ℝ) ≤ (1857622551266377763/12500000000000000000 : ℝ) := by
    have hpowers : (34623/50000 : ℝ)^83 ≤ (1857622551266377763/12500000000000000000 : ℝ)^16 := by
      have hnat : (34623 : ℕ)^83*12500000000000000000^16 ≤ 1857622551266377763^16*50000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34623 50000 1857622551266377763 12500000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34623/50000 : ℝ)) (X := (1857622551266377763/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (14357622551266377763/12500000000000000000 : ℝ) ≤ (1027068764940811/1000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (14357622551266377763/12500000000000000000 : ℝ)^16 ≤ (1027068764940811/1000000000000000 : ℝ)^83 := by
      have hnat : (14357622551266377763 : ℕ)^16*1000000000000000^83 ≤ 1027068764940811^83*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14357622551266377763 12500000000000000000 1027068764940811 1000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1027068764940811/1000000000000000 : ℝ)) (X := (14357622551266377763/12500000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (8107622551266377763/6250000000000000000 : ℝ) ≤ (1051443004375297/1000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (8107622551266377763/6250000000000000000 : ℝ)^16 ≤ (1051443004375297/1000000000000000 : ℝ)^83 := by
      have hnat : (8107622551266377763 : ℕ)^16*1000000000000000^83 ≤ 1051443004375297^83*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8107622551266377763 6250000000000000000 1051443004375297 1000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1051443004375297/1000000000000000 : ℝ)) (X := (8107622551266377763/6250000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(3007640548979/76940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1354124413027/38470000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (34623/50000 : ℝ)) (alpha := (3007640548979/76940000000000 : ℝ)) (beta := (1354124413027/38470000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34623/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(3007640548979/76940000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1354124413027/38470000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (64553/100000 : ℝ) ^ (83/16 : ℝ) ≤ (1290777822090014209/12500000000000000000 : ℝ) := by
    have hpowers : (64553/100000 : ℝ)^83 ≤ (1290777822090014209/12500000000000000000 : ℝ)^16 := by
      have hnat : (64553 : ℕ)^83*12500000000000000000^16 ≤ 1290777822090014209^16*100000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64553 100000 1290777822090014209 12500000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64553/100000 : ℝ)) (X := (1290777822090014209/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13790777822090014209/12500000000000000000 : ℝ) ≤ (10191244681286741/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (13790777822090014209/12500000000000000000 : ℝ)^16 ≤ (10191244681286741/10000000000000000 : ℝ)^83 := by
      have hnat : (13790777822090014209 : ℕ)^16*10000000000000000^83 ≤ 10191244681286741^83*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13790777822090014209 12500000000000000000 10191244681286741 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10191244681286741/10000000000000000 : ℝ)) (X := (13790777822090014209/12500000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (7540777822090014209/6250000000000000000 : ℝ) ≤ (10368544782628571/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (7540777822090014209/6250000000000000000 : ℝ)^16 ≤ (10368544782628571/10000000000000000 : ℝ)^83 := by
      have hnat : (7540777822090014209 : ℕ)^16*10000000000000000^83 ≤ 10368544782628571^83*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7540777822090014209 6250000000000000000 10368544782628571 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10368544782628571/10000000000000000 : ℝ)) (X := (7540777822090014209/6250000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(191244681286741/6455300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(17730010134183/645530000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (64553/100000 : ℝ)) (alpha := (191244681286741/6455300000000000 : ℝ)) (beta := (17730010134183/645530000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64553/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(191244681286741/6455300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(17730010134183/645530000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-877772569/5000000000 : ℝ)*X 0 0+(4439766871/10000000000 : ℝ)*X 0 1+(234363323/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1178151333/2500000000 : ℝ)*X 2 0+(6283899797/10000000000 : ℝ)*X 2 1+(-766416487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3248400683/5000000000 : ℝ)*X 0 0+(503138913/2000000000 : ℝ)*X 0 1+(3055800091/10000000000 : ℝ)*X 0 2+(3248400683/5000000000 : ℝ)*X 1 0+(503138913/2000000000 : ℝ)*X 1 1+(3055800091/10000000000 : ℝ)*X 1 2+(3248400683/5000000000 : ℝ)*X 2 0+(503138913/2000000000 : ℝ)*X 2 1+(3055800091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-219538093/1250000000 : ℝ)*X 0 0+(3931165039/10000000000 : ℝ)*X 0 1+(3162050549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2145198579/5000000000 : ℝ)*X 1 0+(-644802273/5000000000 : ℝ)*X 1 1+(19791019/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((870793569/2000000000 : ℝ)*X 2 0+(6937168237/10000000000 : ℝ)*X 2 1+(-147083657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((51679083/80000000 : ℝ)*X 0 0+(3714618607/10000000000 : ℝ)*X 0 1+(228992231/1250000000 : ℝ)*X 0 2+(51679083/80000000 : ℝ)*X 1 0+(3714618607/10000000000 : ℝ)*X 1 1+(228992231/1250000000 : ℝ)*X 1 2+(51679083/80000000 : ℝ)*X 2 0+(3714618607/10000000000 : ℝ)*X 2 1+(228992231/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-884225807/10000000000 : ℝ)*X 0 0+(2298377439/5000000000 : ℝ)*X 0 1+(3159384423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4270159253/10000000000 : ℝ)*X 1 0+(-1324088449/10000000000 : ℝ)*X 1 1+(6327793981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((704177401/1250000000 : ℝ)*X 2 0+(715657101/1250000000 : ℝ)*X 2 1+(-38104041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7705377431/10000000000 : ℝ)*X 0 0+(2166083379/10000000000 : ℝ)*X 0 1+(923735039/5000000000 : ℝ)*X 0 2+(7705377431/10000000000 : ℝ)*X 1 0+(2166083379/10000000000 : ℝ)*X 1 1+(923735039/5000000000 : ℝ)*X 1 2+(7705377431/10000000000 : ℝ)*X 2 0+(2166083379/10000000000 : ℝ)*X 2 1+(923735039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-816888649/10000000000 : ℝ)*X 0 0+(5184916293/10000000000 : ℝ)*X 0 1+(2900998407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5637185123/10000000000 : ℝ)*X 1 0+(-806351653/10000000000 : ℝ)*X 1 1+(42877607/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4184861393/10000000000 : ℝ)*X 2 0+(137548427/200000000 : ℝ)*X 2 1+(-574189161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((13022377/16000000 : ℝ)*X 0 0+(164442141/1000000000 : ℝ)*X 0 1+(880705861/5000000000 : ℝ)*X 0 2+(13022377/16000000 : ℝ)*X 1 0+(164442141/1000000000 : ℝ)*X 1 1+(880705861/5000000000 : ℝ)*X 1 2+(13022377/16000000 : ℝ)*X 2 0+(164442141/1000000000 : ℝ)*X 2 1+(880705861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((16671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4113123454285272031731249/496670782000000000000000000000 : ℝ) := by norm_num
    linear_combination (925739/500000000000 : ℝ)*(base23) + (279609/1000000000000 : ℝ)*(base50) + (1084998289013/1000000000000 : ℝ)*(base59) + (219890534639/40000000000 : ℝ)*(major_s1_0) + (219890534639/40000000000 : ℝ)*(major_s1_1) + (219890534639/40000000000 : ℝ)*(major_s1_2) + (22069171/1000000000000 : ℝ)*(sp_s1_0) + (5714141/250000000000 : ℝ)*(sp_s1_6) + (511533031247/62500000000 : ℝ)*(sp_s1_7) + (1022903058647/125000000000 : ℝ)*(sp_s1_8) + (1636895324369/200000000000 : ℝ)*(sp_s1_9) + (2809950545797/1000000000000 : ℝ)*(sp_s1_13) + (663049973/500000000000 : ℝ)*(sp_s1_15) + (72095799/1000000000000 : ℝ)*(sp_s1_23) + (2809973402361/1000000000000 : ℝ)*(f.failure) + (4092275284561/500000000000 : ℝ)*(f.sum) + (163783149604137953/620838477500000000000000000000 : ℝ)*base63 + (109256259559349/645530000000000000000000000 : ℝ)*base64 + (5934717350811/19235000000000000000000000 : ℝ)*base66 + (19090873061333/51642400000000000000000000 : ℝ)*base69 + (1948541775039666571/9038711060000000000000000000000 : ℝ)*base70 + (43126666719/87512500000000000000000 : ℝ)*base73 + (29968819824811/76940000000000000000000000 : ℝ)*base75 + (79347311329013/140020000000000000000000000 : ℝ)*base77 + (8133499626690301/53865694000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (4063/50000000000000000 : ℝ)*base86 + (4063/50000000000000000 : ℝ)*base88 + (4063/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8029/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8029/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (466600148933127243458189404329/27165563631109375000000000000000000 : ℝ) := by norm_num
    linear_combination (1191469/500000000000 : ℝ)*(base19) + (903581/1000000000000 : ℝ)*(base39) + (128875780129/250000000000 : ℝ)*(base59) + (5167897414757/1000000000000 : ℝ)*(major_s1_0) + (5167897414757/1000000000000 : ℝ)*(major_s1_1) + (5167897414757/1000000000000 : ℝ)*(major_s1_2) + (45294867/1000000000000 : ℝ)*(sp_s1_2) + (22049647/500000000000 : ℝ)*(sp_s1_6) + (92251547/1000000000000 : ℝ)*(sp_s1_7) + (1923520421527/250000000000 : ℝ)*(sp_s1_14) + (1923542888679/250000000000 : ℝ)*(sp_s1_15) + (1923532160697/250000000000 : ℝ)*(sp_s1_16) + (528273302253/200000000000 : ℝ)*(sp_s1_20) + (1598093/7812500000 : ℝ)*(sp_s1_27) + (1320807583231/500000000000 : ℝ)*(f.failure) + (1538834787531/200000000000 : ℝ)*(f.sum) + (1228649607096662627/3104192387500000000000000000000 : ℝ)*base62 + (388759515633657/645530000000000000000000000 : ℝ)*base64 + (13090406758403/38470000000000000000000000 : ℝ)*base66 + (2042146328250573/6455300000000000000000000000 : ℝ)*base68 + (122836190260348005781/225967776500000000000000000000000 : ℝ)*base70 + (135196025619959/875125000000000000000000000 : ℝ)*base73 + (9156487882279/15388000000000000000000000 : ℝ)*base74 + (1052459816086477/3500500000000000000000000000 : ℝ)*base76 + (361957050991787813/841651468750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (18273/25000000000000000 : ℝ)*base86 + (18273/25000000000000000 : ℝ)*base88 + (18273/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(901/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(901/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1571904460190347944746477632059/217324509048875000000000000000000000 : ℝ) := by norm_num
    linear_combination (10046931/1000000000000 : ℝ)*(base11) + (1353343/250000000000 : ℝ)*(base15) + (9303826241/31250000000 : ℝ)*(base40) + (129075359491/250000000000 : ℝ)*(base59) + (276924924377/62500000000 : ℝ)*(major_s1_0) + (276924924377/62500000000 : ℝ)*(major_s1_1) + (276924924377/62500000000 : ℝ)*(major_s1_2) + (2268461/1000000000000 : ℝ)*(sp_s1_0) + (1341417/250000000000 : ℝ)*(sp_s1_2) + (4057447/100000000000 : ℝ)*(sp_s1_9) + (6596741982437/1000000000000 : ℝ)*(sp_s1_21) + (1319349776891/200000000000 : ℝ)*(sp_s1_22) + (659670835769/100000000000 : ℝ)*(sp_s1_23) + (452968174247/200000000000 : ℝ)*(sp_s1_27) + (452968174247/200000000000 : ℝ)*(f.failure) + (1649188574457/250000000000 : ℝ)*(f.sum) + (855380216590223493/3104192387500000000000000000000 : ℝ)*base63 + (437306028103861/322765000000000000000000000 : ℝ)*base64 + (31134442900797/38470000000000000000000000 : ℝ)*base66 + (157184917440657/403456250000000000000000000 : ℝ)*base69 + (11376572586799454397/112983888250000000000000000000000 : ℝ)*base71 + (758124216726907/1750250000000000000000000000 : ℝ)*base72 + (10484714345773/38470000000000000000000000 : ℝ)*base74 + (63866344876019/437562500000000000000000000 : ℝ)*base76 + (1057088309955633727/3366605875000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (1201/10000000000000000 : ℝ)*base86 + (1201/10000000000000000 : ℝ)*base88 + (1201/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((7001/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34623/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34623/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64553/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64553/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8029/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8029/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(901/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(901/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c323061_s1 p hpa hpb X hX hprev0

#print axioms solution

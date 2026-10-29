-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308055_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:10.439464+00:00
-- url     : https://prove2.me/submissions/21ceea06-9451-4701-9641-750c67cf34cf

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
theorem collision_support_c308055_s7_s7_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1311329589/5000000000 : ℝ)*x 0 + (5416069671/10000000000 : ℝ)*x 1 + (4706039387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311329589/5000000000 : ℝ)^69 ≤ (1750925629833/10000000000000 : ℝ)^53 := by
    have hnat : (1311329589 : ℕ)^69*10000000000000^53 ≤ 1750925629833^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311329589 5000000000 1750925629833 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416069671/10000000000 : ℝ)^69 ≤ (45007722021379/100000000000000 : ℝ)^53 := by
    have hnat : (5416069671 : ℕ)^69*100000000000000^53 ≤ 45007722021379^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416069671 10000000000 45007722021379 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4706039387/10000000000 : ℝ)^69 ≤ (37483021664813/100000000000000 : ℝ)^53 := by
    have hnat : (4706039387 : ℕ)^69*100000000000000^53 ≤ 37483021664813^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706039387 10000000000 37483021664813 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1311329589/5000000000 : ℝ), (5416069671/10000000000 : ℝ), (4706039387/10000000000 : ℝ)] ![(1750925629833/10000000000000 : ℝ), (45007722021379/100000000000000 : ℝ), (37483021664813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1311329589/5000000000 : ℝ)|^69 ≤ (1750925629833/10000000000000 : ℝ)^53
        have hw : |(-1311329589/5000000000 : ℝ)|=(1311329589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416069671/10000000000 : ℝ)|^69 ≤ (45007722021379/100000000000000 : ℝ)^53
        have hw : |(5416069671/10000000000 : ℝ)|=(5416069671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4706039387/10000000000 : ℝ)|^69 ≤ (37483021664813/100000000000000 : ℝ)^53
        have hw : |(4706039387/10000000000 : ℝ)|=(4706039387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2352545913/5000000000 : ℝ)*x 0 + (-1913156643/10000000000 : ℝ)*x 1 + (5954151743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2352545913/5000000000 : ℝ)^69 ≤ (1873659817771/5000000000000 : ℝ)^53 := by
    have hnat : (2352545913 : ℕ)^69*5000000000000^53 ≤ 1873659817771^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352545913 5000000000 1873659817771 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913156643/10000000000 : ℝ)^69 ≤ (2903090068949/25000000000000 : ℝ)^53 := by
    have hnat : (1913156643 : ℕ)^69*25000000000000^53 ≤ 2903090068949^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913156643 10000000000 2903090068949 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5954151743/10000000000 : ℝ)^69 ≤ (12728610838493/25000000000000 : ℝ)^53 := by
    have hnat : (5954151743 : ℕ)^69*25000000000000^53 ≤ 12728610838493^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954151743 10000000000 12728610838493 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2352545913/5000000000 : ℝ), (-1913156643/10000000000 : ℝ), (5954151743/10000000000 : ℝ)] ![(1873659817771/5000000000000 : ℝ), (2903090068949/25000000000000 : ℝ), (12728610838493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2352545913/5000000000 : ℝ)|^69 ≤ (1873659817771/5000000000000 : ℝ)^53
        have hw : |(2352545913/5000000000 : ℝ)|=(2352545913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1913156643/10000000000 : ℝ)|^69 ≤ (2903090068949/25000000000000 : ℝ)^53
        have hw : |(-1913156643/10000000000 : ℝ)|=(1913156643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5954151743/10000000000 : ℝ)|^69 ≤ (12728610838493/25000000000000 : ℝ)^53
        have hw : |(5954151743/10000000000 : ℝ)|=(5954151743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4706079351/10000000000 : ℝ)*x 0 + (5415596681/10000000000 : ℝ)*x 1 + (-2623200223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4706079351/10000000000 : ℝ)^69 ≤ (18741718033369/50000000000000 : ℝ)^53 := by
    have hnat : (4706079351 : ℕ)^69*50000000000000^53 ≤ 18741718033369^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706079351 10000000000 18741718033369 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415596681/10000000000 : ℝ)^69 ≤ (22501302470463/50000000000000 : ℝ)^53 := by
    have hnat : (5415596681 : ℕ)^69*50000000000000^53 ≤ 22501302470463^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415596681 10000000000 22501302470463 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623200223/10000000000 : ℝ)^69 ≤ (17513958984259/100000000000000 : ℝ)^53 := by
    have hnat : (2623200223 : ℕ)^69*100000000000000^53 ≤ 17513958984259^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623200223 10000000000 17513958984259 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4706079351/10000000000 : ℝ), (5415596681/10000000000 : ℝ), (-2623200223/10000000000 : ℝ)] ![(18741718033369/50000000000000 : ℝ), (22501302470463/50000000000000 : ℝ), (17513958984259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4706079351/10000000000 : ℝ)|^69 ≤ (18741718033369/50000000000000 : ℝ)^53
        have hw : |(4706079351/10000000000 : ℝ)|=(4706079351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415596681/10000000000 : ℝ)|^69 ≤ (22501302470463/50000000000000 : ℝ)^53
        have hw : |(5415596681/10000000000 : ℝ)|=(5415596681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2623200223/10000000000 : ℝ)|^69 ≤ (17513958984259/100000000000000 : ℝ)^53
        have hw : |(-2623200223/10000000000 : ℝ)|=(2623200223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2826658257/5000000000 : ℝ)*x 0 + (4135543393/10000000000 : ℝ)*x 1 + (2985852831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2826658257/5000000000 : ℝ)^69 ≤ (9518246216297/20000000000000 : ℝ)^53 := by
    have hnat : (2826658257 : ℕ)^69*20000000000000^53 ≤ 9518246216297^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826658257 5000000000 9518246216297 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135543393/10000000000 : ℝ)^69 ≤ (31678808114901/100000000000000 : ℝ)^53 := by
    have hnat : (4135543393 : ℕ)^69*100000000000000^53 ≤ 31678808114901^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135543393 10000000000 31678808114901 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2985852831/10000000000 : ℝ)^69 ≤ (2591245098001/12500000000000 : ℝ)^53 := by
    have hnat : (2985852831 : ℕ)^69*12500000000000^53 ≤ 2591245098001^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985852831 10000000000 2591245098001 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2826658257/5000000000 : ℝ), (4135543393/10000000000 : ℝ), (2985852831/10000000000 : ℝ)] ![(9518246216297/20000000000000 : ℝ), (31678808114901/100000000000000 : ℝ), (2591245098001/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2826658257/5000000000 : ℝ)|^69 ≤ (9518246216297/20000000000000 : ℝ)^53
        have hw : |(2826658257/5000000000 : ℝ)|=(2826658257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135543393/10000000000 : ℝ)|^69 ≤ (31678808114901/100000000000000 : ℝ)^53
        have hw : |(4135543393/10000000000 : ℝ)|=(4135543393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2985852831/10000000000 : ℝ)|^69 ≤ (2591245098001/12500000000000 : ℝ)^53
        have hw : |(2985852831/10000000000 : ℝ)|=(2985852831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-161658739/625000000 : ℝ)*x 0 + (5278657873/10000000000 : ℝ)*x 1 + (4878123787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161658739/625000000 : ℝ)^69 ≤ (107474853207/625000000000 : ℝ)^53 := by
    have hnat : (161658739 : ℕ)^69*625000000000^53 ≤ 107474853207^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161658739 625000000 107474853207 625000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5278657873/10000000000 : ℝ)^69 ≤ (43526828954389/100000000000000 : ℝ)^53 := by
    have hnat : (5278657873 : ℕ)^69*100000000000000^53 ≤ 43526828954389^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278657873 10000000000 43526828954389 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4878123787/10000000000 : ℝ)^69 ≤ (1227412328693/3125000000000 : ℝ)^53 := by
    have hnat : (4878123787 : ℕ)^69*3125000000000^53 ≤ 1227412328693^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878123787 10000000000 1227412328693 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-161658739/625000000 : ℝ), (5278657873/10000000000 : ℝ), (4878123787/10000000000 : ℝ)] ![(107474853207/625000000000 : ℝ), (43526828954389/100000000000000 : ℝ), (1227412328693/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-161658739/625000000 : ℝ)|^69 ≤ (107474853207/625000000000 : ℝ)^53
        have hw : |(-161658739/625000000 : ℝ)|=(161658739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5278657873/10000000000 : ℝ)|^69 ≤ (43526828954389/100000000000000 : ℝ)^53
        have hw : |(5278657873/10000000000 : ℝ)|=(5278657873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4878123787/10000000000 : ℝ)|^69 ≤ (1227412328693/3125000000000 : ℝ)^53
        have hw : |(4878123787/10000000000 : ℝ)|=(4878123787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (586589463/1250000000 : ℝ)*x 0 + (-1768104483/10000000000 : ℝ)*x 1 + (1213422673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586589463/1250000000 : ℝ)^69 ≤ (37344922582959/100000000000000 : ℝ)^53 := by
    have hnat : (586589463 : ℕ)^69*100000000000000^53 ≤ 37344922582959^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586589463 1250000000 37344922582959 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1768104483/10000000000 : ℝ)^69 ≤ (2095899732269/20000000000000 : ℝ)^53 := by
    have hnat : (1768104483 : ℕ)^69*20000000000000^53 ≤ 2095899732269^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768104483 10000000000 2095899732269 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213422673/2000000000 : ℝ)^69 ≤ (26087789376089/50000000000000 : ℝ)^53 := by
    have hnat : (1213422673 : ℕ)^69*50000000000000^53 ≤ 26087789376089^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213422673 2000000000 26087789376089 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(586589463/1250000000 : ℝ), (-1768104483/10000000000 : ℝ), (1213422673/2000000000 : ℝ)] ![(37344922582959/100000000000000 : ℝ), (2095899732269/20000000000000 : ℝ), (26087789376089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(586589463/1250000000 : ℝ)|^69 ≤ (37344922582959/100000000000000 : ℝ)^53
        have hw : |(586589463/1250000000 : ℝ)|=(586589463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1768104483/10000000000 : ℝ)|^69 ≤ (2095899732269/20000000000000 : ℝ)^53
        have hw : |(-1768104483/10000000000 : ℝ)|=(1768104483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1213422673/2000000000 : ℝ)|^69 ≤ (26087789376089/50000000000000 : ℝ)^53
        have hw : |(1213422673/2000000000 : ℝ)|=(1213422673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4693703681/10000000000 : ℝ)*x 0 + (2781185761/5000000000 : ℝ)*x 1 + (-1226419919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4693703681/10000000000 : ℝ)^69 ≤ (7471031767963/20000000000000 : ℝ)^53 := by
    have hnat : (4693703681 : ℕ)^69*20000000000000^53 ≤ 7471031767963^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4693703681 10000000000 7471031767963 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2781185761/5000000000 : ℝ)^69 ≤ (46596934800947/100000000000000 : ℝ)^53 := by
    have hnat : (2781185761 : ℕ)^69*100000000000000^53 ≤ 46596934800947^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781185761 5000000000 46596934800947 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1226419919/5000000000 : ℝ)^69 ≤ (8023953169463/50000000000000 : ℝ)^53 := by
    have hnat : (1226419919 : ℕ)^69*50000000000000^53 ≤ 8023953169463^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226419919 5000000000 8023953169463 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4693703681/10000000000 : ℝ), (2781185761/5000000000 : ℝ), (-1226419919/5000000000 : ℝ)] ![(7471031767963/20000000000000 : ℝ), (46596934800947/100000000000000 : ℝ), (8023953169463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4693703681/10000000000 : ℝ)|^69 ≤ (7471031767963/20000000000000 : ℝ)^53
        have hw : |(4693703681/10000000000 : ℝ)|=(4693703681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2781185761/5000000000 : ℝ)|^69 ≤ (46596934800947/100000000000000 : ℝ)^53
        have hw : |(2781185761/5000000000 : ℝ)|=(2781185761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1226419919/5000000000 : ℝ)|^69 ≤ (8023953169463/50000000000000 : ℝ)^53
        have hw : |(-1226419919/5000000000 : ℝ)|=(1226419919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1114982469/2000000000 : ℝ)*x 0 + (55394179/125000000 : ℝ)*x 1 + (1373876251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114982469/2000000000 : ℝ)^69 ≤ (292085957117/625000000000 : ℝ)^53 := by
    have hnat : (1114982469 : ℕ)^69*625000000000^53 ≤ 292085957117^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114982469 2000000000 292085957117 625000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55394179/125000000 : ℝ)^69 ≤ (34661988443941/100000000000000 : ℝ)^53 := by
    have hnat : (55394179 : ℕ)^69*100000000000000^53 ≤ 34661988443941^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55394179 125000000 34661988443941 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373876251/5000000000 : ℝ)^69 ≤ (72672884351/390625000000 : ℝ)^53 := by
    have hnat : (1373876251 : ℕ)^69*390625000000^53 ≤ 72672884351^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373876251 5000000000 72672884351 390625000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1114982469/2000000000 : ℝ), (55394179/125000000 : ℝ), (1373876251/5000000000 : ℝ)] ![(292085957117/625000000000 : ℝ), (34661988443941/100000000000000 : ℝ), (72672884351/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1114982469/2000000000 : ℝ)|^69 ≤ (292085957117/625000000000 : ℝ)^53
        have hw : |(1114982469/2000000000 : ℝ)|=(1114982469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55394179/125000000 : ℝ)|^69 ≤ (34661988443941/100000000000000 : ℝ)^53
        have hw : |(55394179/125000000 : ℝ)|=(55394179/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1373876251/5000000000 : ℝ)|^69 ≤ (72672884351/390625000000 : ℝ)^53
        have hw : |(1373876251/5000000000 : ℝ)|=(1373876251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-487274843/2000000000 : ℝ)*x 0 + (1345698061/2500000000 : ℝ)*x 1 + (152938889/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487274843/2000000000 : ℝ)^69 ≤ (3181559882249/20000000000000 : ℝ)^53 := by
    have hnat : (487274843 : ℕ)^69*20000000000000^53 ≤ 3181559882249^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487274843 2000000000 3181559882249 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345698061/2500000000 : ℝ)^69 ≤ (44648037118431/100000000000000 : ℝ)^53 := by
    have hnat : (1345698061 : ℕ)^69*100000000000000^53 ≤ 44648037118431^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345698061 2500000000 44648037118431 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152938889/312500000 : ℝ)^69 ≤ (39444163458649/100000000000000 : ℝ)^53 := by
    have hnat : (152938889 : ℕ)^69*100000000000000^53 ≤ 39444163458649^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152938889 312500000 39444163458649 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487274843/2000000000 : ℝ), (1345698061/2500000000 : ℝ), (152938889/312500000 : ℝ)] ![(3181559882249/20000000000000 : ℝ), (44648037118431/100000000000000 : ℝ), (39444163458649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487274843/2000000000 : ℝ)|^69 ≤ (3181559882249/20000000000000 : ℝ)^53
        have hw : |(-487274843/2000000000 : ℝ)|=(487274843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1345698061/2500000000 : ℝ)|^69 ≤ (44648037118431/100000000000000 : ℝ)^53
        have hw : |(1345698061/2500000000 : ℝ)|=(1345698061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152938889/312500000 : ℝ)|^69 ≤ (39444163458649/100000000000000 : ℝ)^53
        have hw : |(152938889/312500000 : ℝ)|=(152938889/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4599649481/10000000000 : ℝ)*x 0 + (-473506129/2500000000 : ℝ)*x 1 + (1516318469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4599649481/10000000000 : ℝ)^69 ≤ (36383610189059/100000000000000 : ℝ)^53 := by
    have hnat : (4599649481 : ℕ)^69*100000000000000^53 ≤ 36383610189059^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599649481 10000000000 36383610189059 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473506129/2500000000 : ℝ)^69 ≤ (2865351200999/25000000000000 : ℝ)^53 := by
    have hnat : (473506129 : ℕ)^69*25000000000000^53 ≤ 2865351200999^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473506129 2500000000 2865351200999 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1516318469/2500000000 : ℝ)^69 ≤ (26077492494733/50000000000000 : ℝ)^53 := by
    have hnat : (1516318469 : ℕ)^69*50000000000000^53 ≤ 26077492494733^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516318469 2500000000 26077492494733 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4599649481/10000000000 : ℝ), (-473506129/2500000000 : ℝ), (1516318469/2500000000 : ℝ)] ![(36383610189059/100000000000000 : ℝ), (2865351200999/25000000000000 : ℝ), (26077492494733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4599649481/10000000000 : ℝ)|^69 ≤ (36383610189059/100000000000000 : ℝ)^53
        have hw : |(4599649481/10000000000 : ℝ)|=(4599649481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473506129/2500000000 : ℝ)|^69 ≤ (2865351200999/25000000000000 : ℝ)^53
        have hw : |(-473506129/2500000000 : ℝ)|=(473506129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1516318469/2500000000 : ℝ)|^69 ≤ (26077492494733/50000000000000 : ℝ)^53
        have hw : |(1516318469/2500000000 : ℝ)|=(1516318469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4894089171/10000000000 : ℝ)*x 0 + (1345579891/2500000000 : ℝ)*x 1 + (-121845973/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4894089171/10000000000 : ℝ)^69 ≤ (39444632725189/100000000000000 : ℝ)^53 := by
    have hnat : (4894089171 : ℕ)^69*100000000000000^53 ≤ 39444632725189^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4894089171 10000000000 39444632725189 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345579891/2500000000 : ℝ)^69 ≤ (44642932897737/100000000000000 : ℝ)^53 := by
    have hnat : (1345579891 : ℕ)^69*100000000000000^53 ≤ 44642932897737^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345579891 2500000000 44642932897737 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121845973/500000000 : ℝ)^69 ≤ (198905429601/1250000000000 : ℝ)^53 := by
    have hnat : (121845973 : ℕ)^69*1250000000000^53 ≤ 198905429601^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121845973 500000000 198905429601 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4894089171/10000000000 : ℝ), (1345579891/2500000000 : ℝ), (-121845973/500000000 : ℝ)] ![(39444632725189/100000000000000 : ℝ), (44642932897737/100000000000000 : ℝ), (198905429601/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4894089171/10000000000 : ℝ)|^69 ≤ (39444632725189/100000000000000 : ℝ)^53
        have hw : |(4894089171/10000000000 : ℝ)|=(4894089171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1345579891/2500000000 : ℝ)|^69 ≤ (44642932897737/100000000000000 : ℝ)^53
        have hw : |(1345579891/2500000000 : ℝ)|=(1345579891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121845973/500000000 : ℝ)|^69 ≤ (198905429601/1250000000000 : ℝ)^53
        have hw : |(-121845973/500000000 : ℝ)|=(121845973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1470178781/2500000000 : ℝ)*x 0 + (1023437817/2500000000 : ℝ)*x 1 + (550336287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1470178781/2500000000 : ℝ)^69 ≤ (50098433534327/100000000000000 : ℝ)^53 := by
    have hnat : (1470178781 : ℕ)^69*100000000000000^53 ≤ 50098433534327^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470178781 2500000000 50098433534327 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023437817/2500000000 : ℝ)^69 ≤ (31262668181949/100000000000000 : ℝ)^53 := by
    have hnat : (1023437817 : ℕ)^69*100000000000000^53 ≤ 31262668181949^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023437817 2500000000 31262668181949 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550336287/2000000000 : ℝ)^69 ≤ (931944913327/5000000000000 : ℝ)^53 := by
    have hnat : (550336287 : ℕ)^69*5000000000000^53 ≤ 931944913327^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550336287 2000000000 931944913327 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1470178781/2500000000 : ℝ), (1023437817/2500000000 : ℝ), (550336287/2000000000 : ℝ)] ![(50098433534327/100000000000000 : ℝ), (31262668181949/100000000000000 : ℝ), (931944913327/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1470178781/2500000000 : ℝ)|^69 ≤ (50098433534327/100000000000000 : ℝ)^53
        have hw : |(1470178781/2500000000 : ℝ)|=(1470178781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023437817/2500000000 : ℝ)|^69 ≤ (31262668181949/100000000000000 : ℝ)^53
        have hw : |(1023437817/2500000000 : ℝ)|=(1023437817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550336287/2000000000 : ℝ)|^69 ≤ (931944913327/5000000000000 : ℝ)^53
        have hw : |(550336287/2000000000 : ℝ)|=(550336287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2450244331/10000000000 : ℝ)*x 0 + (278109067/500000000 : ℝ)*x 1 + (587004633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2450244331/10000000000 : ℝ)^69 ≤ (4006450529329/25000000000000 : ℝ)^53 := by
    have hnat : (2450244331 : ℕ)^69*25000000000000^53 ≤ 4006450529329^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450244331 10000000000 4006450529329 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278109067/500000000 : ℝ)^69 ≤ (23297430331239/50000000000000 : ℝ)^53 := by
    have hnat : (278109067 : ℕ)^69*50000000000000^53 ≤ 23297430331239^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278109067 500000000 23297430331239 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587004633/1250000000 : ℝ)^69 ≤ (18689668597503/50000000000000 : ℝ)^53 := by
    have hnat : (587004633 : ℕ)^69*50000000000000^53 ≤ 18689668597503^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587004633 1250000000 18689668597503 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2450244331/10000000000 : ℝ), (278109067/500000000 : ℝ), (587004633/1250000000 : ℝ)] ![(4006450529329/25000000000000 : ℝ), (23297430331239/50000000000000 : ℝ), (18689668597503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2450244331/10000000000 : ℝ)|^69 ≤ (4006450529329/25000000000000 : ℝ)^53
        have hw : |(-2450244331/10000000000 : ℝ)|=(2450244331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278109067/500000000 : ℝ)|^69 ≤ (23297430331239/50000000000000 : ℝ)^53
        have hw : |(278109067/500000000 : ℝ)|=(278109067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587004633/1250000000 : ℝ)|^69 ≤ (18689668597503/50000000000000 : ℝ)^53
        have hw : |(587004633/1250000000 : ℝ)|=(587004633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2439614289/5000000000 : ℝ)*x 0 + (-884384401/5000000000 : ℝ)*x 1 + (5892267619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2439614289/5000000000 : ℝ)^69 ≤ (7857755155771/20000000000000 : ℝ)^53 := by
    have hnat : (2439614289 : ℕ)^69*20000000000000^53 ≤ 7857755155771^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439614289 5000000000 7857755155771 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884384401/5000000000 : ℝ)^69 ≤ (10484624997761/100000000000000 : ℝ)^53 := by
    have hnat : (884384401 : ℕ)^69*100000000000000^53 ≤ 10484624997761^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884384401 5000000000 10484624997761 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5892267619/10000000000 : ℝ)^69 ≤ (50226599205513/100000000000000 : ℝ)^53 := by
    have hnat : (5892267619 : ℕ)^69*100000000000000^53 ≤ 50226599205513^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5892267619 10000000000 50226599205513 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2439614289/5000000000 : ℝ), (-884384401/5000000000 : ℝ), (5892267619/10000000000 : ℝ)] ![(7857755155771/20000000000000 : ℝ), (10484624997761/100000000000000 : ℝ), (50226599205513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2439614289/5000000000 : ℝ)|^69 ≤ (7857755155771/20000000000000 : ℝ)^53
        have hw : |(2439614289/5000000000 : ℝ)|=(2439614289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884384401/5000000000 : ℝ)|^69 ≤ (10484624997761/100000000000000 : ℝ)^53
        have hw : |(-884384401/5000000000 : ℝ)|=(884384401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5892267619/10000000000 : ℝ)|^69 ≤ (50226599205513/100000000000000 : ℝ)^53
        have hw : |(5892267619/10000000000 : ℝ)|=(5892267619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4586643343/10000000000 : ℝ)*x 0 + (5561710723/10000000000 : ℝ)*x 1 + (-2582444873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4586643343/10000000000 : ℝ)^69 ≤ (18124864878181/50000000000000 : ℝ)^53 := by
    have hnat : (4586643343 : ℕ)^69*50000000000000^53 ≤ 18124864878181^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586643343 10000000000 18124864878181 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5561710723/10000000000 : ℝ)^69 ≤ (582371602149/1250000000000 : ℝ)^53 := by
    have hnat : (5561710723 : ℕ)^69*1250000000000^53 ≤ 582371602149^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5561710723 10000000000 582371602149 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582444873/10000000000 : ℝ)^69 ≤ (429013551427/2500000000000 : ℝ)^53 := by
    have hnat : (2582444873 : ℕ)^69*2500000000000^53 ≤ 429013551427^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582444873 10000000000 429013551427 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4586643343/10000000000 : ℝ), (5561710723/10000000000 : ℝ), (-2582444873/10000000000 : ℝ)] ![(18124864878181/50000000000000 : ℝ), (582371602149/1250000000000 : ℝ), (429013551427/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4586643343/10000000000 : ℝ)|^69 ≤ (18124864878181/50000000000000 : ℝ)^53
        have hw : |(4586643343/10000000000 : ℝ)|=(4586643343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5561710723/10000000000 : ℝ)|^69 ≤ (582371602149/1250000000000 : ℝ)^53
        have hw : |(5561710723/10000000000 : ℝ)|=(5561710723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2582444873/10000000000 : ℝ)|^69 ≤ (429013551427/2500000000000 : ℝ)^53
        have hw : |(-2582444873/10000000000 : ℝ)|=(2582444873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s7_s7_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (591058149/1000000000 : ℝ)*x 0 + (1913213539/5000000000 : ℝ)*x 1 + (3008904067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (591058149/1000000000 : ℝ)^69 ≤ (50429932377701/100000000000000 : ℝ)^53 := by
    have hnat : (591058149 : ℕ)^69*100000000000000^53 ≤ 50429932377701^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591058149 1000000000 50429932377701 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913213539/5000000000 : ℝ)^69 ≤ (7157878133539/25000000000000 : ℝ)^53 := by
    have hnat : (1913213539 : ℕ)^69*25000000000000^53 ≤ 7157878133539^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913213539 5000000000 7157878133539 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008904067/10000000000 : ℝ)^69 ≤ (163582461481/781250000000 : ℝ)^53 := by
    have hnat : (3008904067 : ℕ)^69*781250000000^53 ≤ 163582461481^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008904067 10000000000 163582461481 781250000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(591058149/1000000000 : ℝ), (1913213539/5000000000 : ℝ), (3008904067/10000000000 : ℝ)] ![(50429932377701/100000000000000 : ℝ), (7157878133539/25000000000000 : ℝ), (163582461481/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(591058149/1000000000 : ℝ)|^69 ≤ (50429932377701/100000000000000 : ℝ)^53
        have hw : |(591058149/1000000000 : ℝ)|=(591058149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1913213539/5000000000 : ℝ)|^69 ≤ (7157878133539/25000000000000 : ℝ)^53
        have hw : |(1913213539/5000000000 : ℝ)|=(1913213539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008904067/10000000000 : ℝ)|^69 ≤ (163582461481/781250000000 : ℝ)^53
        have hw : |(3008904067/10000000000 : ℝ)|=(3008904067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308055_s7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((21579/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21579/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(179/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(179/800 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21849/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2209/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2209/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1153/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1153/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8939/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8939/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (21579/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2955718599559389/2000000000000000000 : ℝ) := by
    have hpowers : (21579/100000 : ℝ)^17 ≤ (2955718599559389/2000000000000000000 : ℝ)^4 := by
      have hnat : (21579 : ℕ)^17*2000000000000000000^4 ≤ 2955718599559389^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21579 100000 2955718599559389 2000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21579/100000 : ℝ)) (X := (2955718599559389/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s7_corner0a : (2002955718599559389/2000000000000000000 : ℝ) ≤ (10003475352800323/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2002955718599559389/2000000000000000000 : ℝ)^4 ≤ (10003475352800323/10000000000000000 : ℝ)^17 := by
      have hnat : (2002955718599559389 : ℕ)^4*10000000000000000^17 ≤ 10003475352800323^17*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002955718599559389 2000000000000000000 10003475352800323 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003475352800323/10000000000000000 : ℝ)) (X := (2002955718599559389/2000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s7_corner0b : (1002955718599559389/1000000000000000000 : ℝ) ≤ (250173669650351/250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (1002955718599559389/1000000000000000000 : ℝ)^4 ≤ (250173669650351/250000000000000 : ℝ)^17 := by
      have hnat : (1002955718599559389 : ℕ)^4*250000000000000^17 ≤ 250173669650351^17*1000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1002955718599559389 1000000000000000000 250173669650351 250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250173669650351/250000000000000 : ℝ)) (X := (1002955718599559389/1000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1158450933441/719300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3471433213717/2157900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21579/100000 : ℝ)) (alpha := (1158450933441/719300000000000 : ℝ)) (beta := (3471433213717/2157900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21579/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1158450933441/719300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3471433213717/2157900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (179/800 : ℝ) ^ (17/4 : ℝ) ≤ (34476481115436827/20000000000000000000 : ℝ) := by
    have hpowers : (179/800 : ℝ)^17 ≤ (34476481115436827/20000000000000000000 : ℝ)^4 := by
      have hnat : (179 : ℕ)^17*20000000000000000000^4 ≤ 34476481115436827^4*800^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        179 800 34476481115436827 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (179/800 : ℝ)) (X := (34476481115436827/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s7_corner1a : (20034476481115436827/20000000000000000000 : ℝ) ≤ (10004053385925227/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (20034476481115436827/20000000000000000000 : ℝ)^4 ≤ (10004053385925227/10000000000000000 : ℝ)^17 := by
      have hnat : (20034476481115436827 : ℕ)^4*10000000000000000^17 ≤ 10004053385925227^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20034476481115436827 20000000000000000000 10004053385925227 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004053385925227/10000000000000000 : ℝ)) (X := (20034476481115436827/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s7_corner1b : (10034476481115436827/10000000000000000000 : ℝ) ≤ (625506340081377/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10034476481115436827/10000000000000000000 : ℝ)^4 ≤ (625506340081377/625000000000000 : ℝ)^17 := by
      have hnat : (10034476481115436827 : ℕ)^4*625000000000000^17 ≤ 625506340081377^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10034476481115436827 10000000000000000000 625506340081377 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625506340081377/625000000000000 : ℝ)) (X := (10034476481115436827/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(4053385925227/2237500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(809611075361/447500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (179/800 : ℝ)) (alpha := (4053385925227/2237500000000000 : ℝ)) (beta := (809611075361/447500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (179/800 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(4053385925227/2237500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(809611075361/447500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (21849/100000 : ℝ) ^ (17/4 : ℝ) ≤ (155805989873516579/100000000000000000000 : ℝ) := by
    have hpowers : (21849/100000 : ℝ)^17 ≤ (155805989873516579/100000000000000000000 : ℝ)^4 := by
      have hnat : (21849 : ℕ)^17*100000000000000000000^4 ≤ 155805989873516579^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21849 100000 155805989873516579 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21849/100000 : ℝ)) (X := (155805989873516579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s7_corner2a : (100155805989873516579/100000000000000000000 : ℝ) ≤ (10003663841334997/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100155805989873516579/100000000000000000000 : ℝ)^4 ≤ (10003663841334997/10000000000000000 : ℝ)^17 := by
      have hnat : (100155805989873516579 : ℕ)^4*10000000000000000^17 ≤ 10003663841334997^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100155805989873516579 100000000000000000000 10003663841334997 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003663841334997/10000000000000000 : ℝ)) (X := (100155805989873516579/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s7_corner2b : (50155805989873516579/50000000000000000000 : ℝ) ≤ (10007323326738339/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50155805989873516579/50000000000000000000 : ℝ)^4 ≤ (10007323326738339/10000000000000000 : ℝ)^17 := by
      have hnat : (50155805989873516579 : ℕ)^4*10000000000000000^17 ≤ 10007323326738339^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50155805989873516579 50000000000000000000 10007323326738339 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007323326738339/10000000000000000 : ℝ)) (X := (50155805989873516579/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1221280444999/728300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1829742701671/1092450000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21849/100000 : ℝ)) (alpha := (1221280444999/728300000000000 : ℝ)) (beta := (1829742701671/1092450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (21849/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1221280444999/728300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1829742701671/1092450000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-1311329589/5000000000 : ℝ)*X 0 0+(5416069671/10000000000 : ℝ)*X 0 1+(4706039387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((2352545913/5000000000 : ℝ)*X 1 0+(-1913156643/10000000000 : ℝ)*X 1 1+(5954151743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((4706079351/10000000000 : ℝ)*X 2 0+(5415596681/10000000000 : ℝ)*X 2 1+(-2623200223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((2826658257/5000000000 : ℝ)*X 0 0+(4135543393/10000000000 : ℝ)*X 0 1+(2985852831/10000000000 : ℝ)*X 0 2+(2826658257/5000000000 : ℝ)*X 1 0+(4135543393/10000000000 : ℝ)*X 1 1+(2985852831/10000000000 : ℝ)*X 1 2+(2826658257/5000000000 : ℝ)*X 2 0+(4135543393/10000000000 : ℝ)*X 2 1+(2985852831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-161658739/625000000 : ℝ)*X 0 0+(5278657873/10000000000 : ℝ)*X 0 1+(4878123787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((586589463/1250000000 : ℝ)*X 1 0+(-1768104483/10000000000 : ℝ)*X 1 1+(1213422673/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((4693703681/10000000000 : ℝ)*X 2 0+(2781185761/5000000000 : ℝ)*X 2 1+(-1226419919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((1114982469/2000000000 : ℝ)*X 0 0+(55394179/125000000 : ℝ)*X 0 1+(1373876251/5000000000 : ℝ)*X 0 2+(1114982469/2000000000 : ℝ)*X 1 0+(55394179/125000000 : ℝ)*X 1 1+(1373876251/5000000000 : ℝ)*X 1 2+(1114982469/2000000000 : ℝ)*X 2 0+(55394179/125000000 : ℝ)*X 2 1+(1373876251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-487274843/2000000000 : ℝ)*X 0 0+(1345698061/2500000000 : ℝ)*X 0 1+(152938889/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((4599649481/10000000000 : ℝ)*X 1 0+(-473506129/2500000000 : ℝ)*X 1 1+(1516318469/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((4894089171/10000000000 : ℝ)*X 2 0+(1345579891/2500000000 : ℝ)*X 2 1+(-121845973/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((1470178781/2500000000 : ℝ)*X 0 0+(1023437817/2500000000 : ℝ)*X 0 1+(550336287/2000000000 : ℝ)*X 0 2+(1470178781/2500000000 : ℝ)*X 1 0+(1023437817/2500000000 : ℝ)*X 1 1+(550336287/2000000000 : ℝ)*X 1 2+(1470178781/2500000000 : ℝ)*X 2 0+(1023437817/2500000000 : ℝ)*X 2 1+(550336287/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-2450244331/10000000000 : ℝ)*X 0 0+(278109067/500000000 : ℝ)*X 0 1+(587004633/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((2439614289/5000000000 : ℝ)*X 1 0+(-884384401/5000000000 : ℝ)*X 1 1+(5892267619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((4586643343/10000000000 : ℝ)*X 2 0+(5561710723/10000000000 : ℝ)*X 2 1+(-2582444873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((591058149/1000000000 : ℝ)*X 0 0+(1913213539/5000000000 : ℝ)*X 0 1+(3008904067/10000000000 : ℝ)*X 0 2+(591058149/1000000000 : ℝ)*X 1 0+(1913213539/5000000000 : ℝ)*X 1 1+(3008904067/10000000000 : ℝ)*X 1 2+(591058149/1000000000 : ℝ)*X 2 0+(1913213539/5000000000 : ℝ)*X 2 1+(3008904067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((2209/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2209/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1895101744778951744529/223750000000000000000000000 : ℝ) := by norm_num
    linear_combination (511943149783/125000000000 : ℝ)*(base49) + (641067/500000000000 : ℝ)*(base60) + (25837995169413/1000000000000 : ℝ)*(major_s7_0) + (25837995169413/1000000000000 : ℝ)*(major_s7_1) + (25837995169413/1000000000000 : ℝ)*(major_s7_2) + (182133921/1000000000000 : ℝ)*(sp_s7_0) + (531649/20000000000 : ℝ)*(sp_s7_1) + (60358793/200000000000 : ℝ)*(sp_s7_6) + (8797033424941/250000000000 : ℝ)*(sp_s7_7) + (17593763656503/500000000000 : ℝ)*(sp_s7_8) + (17593920759487/500000000000 : ℝ)*(sp_s7_9) + (16487369887929/1000000000000 : ℝ)*(sp_s7_13) + (76193823/100000000000 : ℝ)*(sp_s7_15) + (474314711/1000000000000 : ℝ)*(sp_s7_23) + (8243835840947/500000000000 : ℝ)*(f.failure) + (7037663166737/200000000000 : ℝ)*(f.sum) + (371941393259522551/2036964062500000000000000000000 : ℝ)*base63 + (65761306377479/364150000000000000000000000 : ℝ)*base64 + (119934812798907/447500000000000000000000000 : ℝ)*base67 + (347672991809683/728300000000000000000000000 : ℝ)*base68 + (197287247750052207/1047732380000000000000000000000 : ℝ)*base71 + (536657346302783/719300000000000000000000000 : ℝ)*base72 + (211130608365749/2237500000000000000000000000 : ℝ)*base74 + (77496880821447/719300000000000000000000000 : ℝ)*base76 + (23331023652797959/50294804687500000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (4683/50000000000000000 : ℝ)*base86 + (4683/50000000000000000 : ℝ)*base88 + (4683/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1153/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1153/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (338036584245158806316037776631/29303765003125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1952859788091/500000000000 : ℝ)*(base49) + (634659/250000000000 : ℝ)*(base60) + (12511136329029/500000000000 : ℝ)*(major_s7_0) + (12511136329029/500000000000 : ℝ)*(major_s7_1) + (12511136329029/500000000000 : ℝ)*(major_s7_2) + (49212953/250000000000 : ℝ)*(sp_s7_1) + (33007509/200000000000 : ℝ)*(sp_s7_2) + (96163483/500000000000 : ℝ)*(sp_s7_7) + (26573541/200000000000 : ℝ)*(sp_s7_8) + (6815440821501/200000000000 : ℝ)*(sp_s7_14) + (17038533357477/500000000000 : ℝ)*(sp_s7_15) + (17038615698463/500000000000 : ℝ)*(sp_s7_16) + (3193394136751/200000000000 : ℝ)*(sp_s7_20) + (174352687/1000000000000 : ℝ)*(sp_s7_27) + (7983572518221/500000000000 : ℝ)*(f.failure) + (34077396434471/1000000000000 : ℝ)*(f.sum) + (4500705816272807761/8147856250000000000000000000000 : ℝ)*base62 + (46055424590873/182075000000000000000000000 : ℝ)*base65 + (24877486602531/223750000000000000000000000 : ℝ)*base67 + (119052202119769/364150000000000000000000000 : ℝ)*base68 + (81158510405893/3274163687500000000000000000 : ℝ)*base71 + (3264736526987/44956250000000000000000000 : ℝ)*base73 + (44924194645521/559375000000000000000000000 : ℝ)*base74 + (2638505820257/179825000000000000000000000 : ℝ)*base77 + (184857180272800917/1609433750000000000000000000000 : ℝ)*base78 + (31131/50000000000000000 : ℝ)*base87 + (31131/50000000000000000 : ℝ)*base89 + (31131/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8939/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8939/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (136103163703366773421957659509/14651882501562500000000000000000000 : ℝ) := by norm_num
    linear_combination (279433/1000000000000 : ℝ)*(base39) + (4906039/500000000000 : ℝ)*(base40) + (398928004013/100000000000 : ℝ)*(base49) + (25011931473391/1000000000000 : ℝ)*(major_s7_0) + (25011931473391/1000000000000 : ℝ)*(major_s7_1) + (25011931473391/1000000000000 : ℝ)*(major_s7_2) + (346408111/500000000000 : ℝ)*(sp_s7_0) + (276347553/1000000000000 : ℝ)*(sp_s7_1) + (3916387/7812500000 : ℝ)*(sp_s7_2) + (274151597/500000000000 : ℝ)*(sp_s7_20) + (8515655221641/250000000000 : ℝ)*(sp_s7_21) + (34063037355233/1000000000000 : ℝ)*(sp_s7_22) + (34062812405249/1000000000000 : ℝ)*(sp_s7_23) + (7979998922211/500000000000 : ℝ)*(sp_s7_27) + (498767067113/31250000000 : ℝ)*(f.failure) + (17031656851393/500000000000 : ℝ)*(f.sum) + (2365434835224060803/8147856250000000000000000000000 : ℝ)*base63 + (94085423202989/1092450000000000000000000000 : ℝ)*base64 + (54561360369349/447500000000000000000000000 : ℝ)*base67 + (1443749396569/728300000000000000000000000 : ℝ)*base69 + (757615120558661929/3143197140000000000000000000000 : ℝ)*base70 + (147122432966047/2157900000000000000000000000 : ℝ)*base73 + (1055801982583507/2237500000000000000000000000 : ℝ)*base75 + (17545474133001/719300000000000000000000000 : ℝ)*base77 + (1649815657747131823/4828301250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (383/781250000000000 : ℝ)*base86 + (383/781250000000000 : ℝ)*base88 + (383/781250000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((21579/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21579/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(179/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(179/800 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21849/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2209/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2209/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1153/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1153/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8939/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8939/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308055_s7 p hpa hpb X hX hprev6

#print axioms solution

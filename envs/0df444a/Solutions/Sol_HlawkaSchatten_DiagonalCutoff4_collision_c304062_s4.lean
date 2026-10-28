-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304062_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:31.84069+00:00
-- url     : https://prove2.me/submissions/c83f0873-d131-4f99-9fae-3087b78162c8

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
theorem collision_support_c304062_s4_s4_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759719631/10000000000 : ℝ)*x 0 + (4925197549/10000000000 : ℝ)*x 1 + (-5952186047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759719631/10000000000 : ℝ)^133 ≤ (405915894769/4000000000000 : ℝ)^101 := by
    have hnat : (1759719631 : ℕ)^133*4000000000000^101 ≤ 405915894769^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759719631 10000000000 405915894769 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925197549/10000000000 : ℝ)^133 ≤ (39352626485549/100000000000000 : ℝ)^101 := by
    have hnat : (4925197549 : ℕ)^133*100000000000000^101 ≤ 39352626485549^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925197549 10000000000 39352626485549 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5952186047/10000000000 : ℝ)^133 ≤ (10099895226447/20000000000000 : ℝ)^101 := by
    have hnat : (5952186047 : ℕ)^133*20000000000000^101 ≤ 10099895226447^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5952186047 10000000000 10099895226447 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759719631/10000000000 : ℝ), (4925197549/10000000000 : ℝ), (-5952186047/10000000000 : ℝ)] ![(405915894769/4000000000000 : ℝ), (39352626485549/100000000000000 : ℝ), (10099895226447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759719631/10000000000 : ℝ)|^133 ≤ (405915894769/4000000000000 : ℝ)^101
        have hw : |(-1759719631/10000000000 : ℝ)|=(1759719631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925197549/10000000000 : ℝ)|^133 ≤ (39352626485549/100000000000000 : ℝ)^101
        have hw : |(4925197549/10000000000 : ℝ)|=(4925197549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5952186047/10000000000 : ℝ)|^133 ≤ (10099895226447/20000000000000 : ℝ)^101
        have hw : |(-5952186047/10000000000 : ℝ)|=(5952186047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (38543899/78125000 : ℝ)*x 0 + (-884871759/5000000000 : ℝ)*x 1 + (-5937427601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38543899/78125000 : ℝ)^133 ≤ (9860314519481/25000000000000 : ℝ)^101 := by
    have hnat : (38543899 : ℕ)^133*25000000000000^101 ≤ 9860314519481^101*78125000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38543899 78125000 9860314519481 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884871759/5000000000 : ℝ)^133 ≤ (19968917991/195312500000 : ℝ)^101 := by
    have hnat : (884871759 : ℕ)^133*195312500000^101 ≤ 19968917991^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884871759 5000000000 19968917991 195312500000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5937427601/10000000000 : ℝ)^133 ≤ (50334655887077/100000000000000 : ℝ)^101 := by
    have hnat : (5937427601 : ℕ)^133*100000000000000^101 ≤ 50334655887077^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937427601 10000000000 50334655887077 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(38543899/78125000 : ℝ), (-884871759/5000000000 : ℝ), (-5937427601/10000000000 : ℝ)] ![(9860314519481/25000000000000 : ℝ), (19968917991/195312500000 : ℝ), (50334655887077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(38543899/78125000 : ℝ)|^133 ≤ (9860314519481/25000000000000 : ℝ)^101
        have hw : |(38543899/78125000 : ℝ)|=(38543899/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884871759/5000000000 : ℝ)|^133 ≤ (19968917991/195312500000 : ℝ)^101
        have hw : |(-884871759/5000000000 : ℝ)|=(884871759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5937427601/10000000000 : ℝ)|^133 ≤ (50334655887077/100000000000000 : ℝ)^101
        have hw : |(-5937427601/10000000000 : ℝ)|=(5937427601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5288677199/10000000000 : ℝ)*x 0 + (5298936671/10000000000 : ℝ)*x 1 + (435836831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288677199/10000000000 : ℝ)^133 ≤ (4322098334401/10000000000000 : ℝ)^101 := by
    have hnat : (5288677199 : ℕ)^133*10000000000000^101 ≤ 4322098334401^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288677199 10000000000 4322098334401 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5298936671/10000000000 : ℝ)^133 ≤ (43331425848047/100000000000000 : ℝ)^101 := by
    have hnat : (5298936671 : ℕ)^133*100000000000000^101 ≤ 43331425848047^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5298936671 10000000000 43331425848047 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435836831/2000000000 : ℝ)^133 ≤ (6723795399017/50000000000000 : ℝ)^101 := by
    have hnat : (435836831 : ℕ)^133*50000000000000^101 ≤ 6723795399017^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435836831 2000000000 6723795399017 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288677199/10000000000 : ℝ), (5298936671/10000000000 : ℝ), (435836831/2000000000 : ℝ)] ![(4322098334401/10000000000000 : ℝ), (43331425848047/100000000000000 : ℝ), (6723795399017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288677199/10000000000 : ℝ)|^133 ≤ (4322098334401/10000000000000 : ℝ)^101
        have hw : |(5288677199/10000000000 : ℝ)|=(5288677199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5298936671/10000000000 : ℝ)|^133 ≤ (43331425848047/100000000000000 : ℝ)^101
        have hw : |(5298936671/10000000000 : ℝ)|=(5298936671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(435836831/2000000000 : ℝ)|^133 ≤ (6723795399017/50000000000000 : ℝ)^101
        have hw : |(435836831/2000000000 : ℝ)|=(435836831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2805099157/5000000000 : ℝ)*x 0 + (5585719559/10000000000 : ℝ)*x 1 + (-326061127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2805099157/5000000000 : ℝ)^133 ≤ (23356973203363/50000000000000 : ℝ)^101 := by
    have hnat : (2805099157 : ℕ)^133*50000000000000^101 ≤ 23356973203363^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805099157 5000000000 23356973203363 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5585719559/10000000000 : ℝ)^133 ≤ (2902858047557/6250000000000 : ℝ)^101 := by
    have hnat : (5585719559 : ℕ)^133*6250000000000^101 ≤ 2902858047557^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585719559 10000000000 2902858047557 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326061127/2500000000 : ℝ)^133 ≤ (6840324816003/100000000000000 : ℝ)^101 := by
    have hnat : (326061127 : ℕ)^133*100000000000000^101 ≤ 6840324816003^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326061127 2500000000 6840324816003 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2805099157/5000000000 : ℝ), (5585719559/10000000000 : ℝ), (-326061127/2500000000 : ℝ)] ![(23356973203363/50000000000000 : ℝ), (2902858047557/6250000000000 : ℝ), (6840324816003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2805099157/5000000000 : ℝ)|^133 ≤ (23356973203363/50000000000000 : ℝ)^101
        have hw : |(2805099157/5000000000 : ℝ)|=(2805099157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5585719559/10000000000 : ℝ)|^133 ≤ (2902858047557/6250000000000 : ℝ)^101
        have hw : |(5585719559/10000000000 : ℝ)|=(5585719559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-326061127/2500000000 : ℝ)|^133 ≤ (6840324816003/100000000000000 : ℝ)^101
        have hw : |(-326061127/2500000000 : ℝ)|=(326061127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-53419137/400000000 : ℝ)*x 0 + (4286845383/10000000000 : ℝ)*x 1 + (-6798809379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53419137/400000000 : ℝ)^133 ≤ (7056850810667/100000000000000 : ℝ)^101 := by
    have hnat : (53419137 : ℕ)^133*100000000000000^101 ≤ 7056850810667^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53419137 400000000 7056850810667 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4286845383/10000000000 : ℝ)^133 ≤ (32778375494697/100000000000000 : ℝ)^101 := by
    have hnat : (4286845383 : ℕ)^133*100000000000000^101 ≤ 32778375494697^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286845383 10000000000 32778375494697 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6798809379/10000000000 : ℝ)^133 ≤ (7520596710213/12500000000000 : ℝ)^101 := by
    have hnat : (6798809379 : ℕ)^133*12500000000000^101 ≤ 7520596710213^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6798809379 10000000000 7520596710213 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53419137/400000000 : ℝ), (4286845383/10000000000 : ℝ), (-6798809379/10000000000 : ℝ)] ![(7056850810667/100000000000000 : ℝ), (32778375494697/100000000000000 : ℝ), (7520596710213/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53419137/400000000 : ℝ)|^133 ≤ (7056850810667/100000000000000 : ℝ)^101
        have hw : |(-53419137/400000000 : ℝ)|=(53419137/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4286845383/10000000000 : ℝ)|^133 ≤ (32778375494697/100000000000000 : ℝ)^101
        have hw : |(4286845383/10000000000 : ℝ)|=(4286845383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6798809379/10000000000 : ℝ)|^133 ≤ (7520596710213/12500000000000 : ℝ)^101
        have hw : |(-6798809379/10000000000 : ℝ)|=(6798809379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (914012909/2000000000 : ℝ)*x 0 + (-894548177/10000000000 : ℝ)*x 1 + (-6799877067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914012909/2000000000 : ℝ)^133 ≤ (8914868945433/25000000000000 : ℝ)^101 := by
    have hnat : (914012909 : ℕ)^133*25000000000000^101 ≤ 8914868945433^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914012909 2000000000 8914868945433 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894548177/10000000000 : ℝ)^133 ≤ (166532335611/4000000000000 : ℝ)^101 := by
    have hnat : (894548177 : ℕ)^133*4000000000000^101 ≤ 166532335611^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894548177 10000000000 166532335611 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6799877067/10000000000 : ℝ)^133 ≤ (3761075988447/6250000000000 : ℝ)^101 := by
    have hnat : (6799877067 : ℕ)^133*6250000000000^101 ≤ 3761075988447^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6799877067 10000000000 3761075988447 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(914012909/2000000000 : ℝ), (-894548177/10000000000 : ℝ), (-6799877067/10000000000 : ℝ)] ![(8914868945433/25000000000000 : ℝ), (166532335611/4000000000000 : ℝ), (3761075988447/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(914012909/2000000000 : ℝ)|^133 ≤ (8914868945433/25000000000000 : ℝ)^101
        have hw : |(914012909/2000000000 : ℝ)|=(914012909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894548177/10000000000 : ℝ)|^133 ≤ (166532335611/4000000000000 : ℝ)^101
        have hw : |(-894548177/10000000000 : ℝ)|=(894548177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6799877067/10000000000 : ℝ)|^133 ≤ (3761075988447/6250000000000 : ℝ)^101
        have hw : |(-6799877067/10000000000 : ℝ)|=(6799877067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1184995273/2500000000 : ℝ)*x 0 + (1617202413/2500000000 : ℝ)*x 1 + (607832981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1184995273/2500000000 : ℝ)^133 ≤ (37415570074423/100000000000000 : ℝ)^101 := by
    have hnat : (1184995273 : ℕ)^133*100000000000000^101 ≤ 37415570074423^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184995273 2500000000 37415570074423 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1617202413/2500000000 : ℝ)^133 ≤ (56349172063887/100000000000000 : ℝ)^101 := by
    have hnat : (1617202413 : ℕ)^133*100000000000000^101 ≤ 56349172063887^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617202413 2500000000 56349172063887 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (607832981/5000000000 : ℝ)^133 ≤ (6235257844821/100000000000000 : ℝ)^101 := by
    have hnat : (607832981 : ℕ)^133*100000000000000^101 ≤ 6235257844821^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607832981 5000000000 6235257844821 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1184995273/2500000000 : ℝ), (1617202413/2500000000 : ℝ), (607832981/5000000000 : ℝ)] ![(37415570074423/100000000000000 : ℝ), (56349172063887/100000000000000 : ℝ), (6235257844821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1184995273/2500000000 : ℝ)|^133 ≤ (37415570074423/100000000000000 : ℝ)^101
        have hw : |(1184995273/2500000000 : ℝ)|=(1184995273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1617202413/2500000000 : ℝ)|^133 ≤ (56349172063887/100000000000000 : ℝ)^101
        have hw : |(1617202413/2500000000 : ℝ)|=(1617202413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(607832981/5000000000 : ℝ)|^133 ≤ (6235257844821/100000000000000 : ℝ)^101
        have hw : |(607832981/5000000000 : ℝ)|=(607832981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5081860203/10000000000 : ℝ)*x 0 + (1328882797/2000000000 : ℝ)*x 1 + (-210303777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5081860203/10000000000 : ℝ)^133 ≤ (2050460463873/5000000000000 : ℝ)^101 := by
    have hnat : (5081860203 : ℕ)^133*5000000000000^101 ≤ 2050460463873^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081860203 10000000000 2050460463873 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328882797/2000000000 : ℝ)^133 ≤ (1167442048629/2000000000000 : ℝ)^101 := by
    have hnat : (1328882797 : ℕ)^133*2000000000000^101 ≤ 1167442048629^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328882797 2000000000 1167442048629 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210303777/10000000000 : ℝ)^133 ≤ (309344138943/50000000000000 : ℝ)^101 := by
    have hnat : (210303777 : ℕ)^133*50000000000000^101 ≤ 309344138943^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210303777 10000000000 309344138943 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5081860203/10000000000 : ℝ), (1328882797/2000000000 : ℝ), (-210303777/10000000000 : ℝ)] ![(2050460463873/5000000000000 : ℝ), (1167442048629/2000000000000 : ℝ), (309344138943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5081860203/10000000000 : ℝ)|^133 ≤ (2050460463873/5000000000000 : ℝ)^101
        have hw : |(5081860203/10000000000 : ℝ)|=(5081860203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1328882797/2000000000 : ℝ)|^133 ≤ (1167442048629/2000000000000 : ℝ)^101
        have hw : |(1328882797/2000000000 : ℝ)|=(1328882797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210303777/10000000000 : ℝ)|^133 ≤ (309344138943/50000000000000 : ℝ)^101
        have hw : |(-210303777/10000000000 : ℝ)|=(210303777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-444275961/5000000000 : ℝ)*x 0 + (916154781/2000000000 : ℝ)*x 1 + (-3396790131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444275961/5000000000 : ℝ)^133 ≤ (1031649624973/25000000000000 : ℝ)^101 := by
    have hnat : (444275961 : ℕ)^133*25000000000000^101 ≤ 1031649624973^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444275961 5000000000 1031649624973 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916154781/2000000000 : ℝ)^133 ≤ (7153911110257/20000000000000 : ℝ)^101 := by
    have hnat : (916154781 : ℕ)^133*20000000000000^101 ≤ 7153911110257^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916154781 2000000000 7153911110257 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3396790131/5000000000 : ℝ)^133 ≤ (30051922967181/50000000000000 : ℝ)^101 := by
    have hnat : (3396790131 : ℕ)^133*50000000000000^101 ≤ 30051922967181^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3396790131 5000000000 30051922967181 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444275961/5000000000 : ℝ), (916154781/2000000000 : ℝ), (-3396790131/5000000000 : ℝ)] ![(1031649624973/25000000000000 : ℝ), (7153911110257/20000000000000 : ℝ), (30051922967181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444275961/5000000000 : ℝ)|^133 ≤ (1031649624973/25000000000000 : ℝ)^101
        have hw : |(-444275961/5000000000 : ℝ)|=(444275961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916154781/2000000000 : ℝ)|^133 ≤ (7153911110257/20000000000000 : ℝ)^101
        have hw : |(916154781/2000000000 : ℝ)|=(916154781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3396790131/5000000000 : ℝ)|^133 ≤ (30051922967181/50000000000000 : ℝ)^101
        have hw : |(-3396790131/5000000000 : ℝ)|=(3396790131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4299164337/10000000000 : ℝ)*x 0 + (-1324601061/10000000000 : ℝ)*x 1 + (-6794646649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299164337/10000000000 : ℝ)^133 ≤ (32902469624631/100000000000000 : ℝ)^101 := by
    have hnat : (4299164337 : ℕ)^133*100000000000000^101 ≤ 32902469624631^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299164337 10000000000 32902469624631 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324601061/10000000000 : ℝ)^133 ≤ (6981260484453/100000000000000 : ℝ)^101 := by
    have hnat : (1324601061 : ℕ)^133*100000000000000^101 ≤ 6981260484453^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324601061 10000000000 6981260484453 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6794646649/10000000000 : ℝ)^133 ≤ (60116269877643/100000000000000 : ℝ)^101 := by
    have hnat : (6794646649 : ℕ)^133*100000000000000^101 ≤ 60116269877643^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6794646649 10000000000 60116269877643 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299164337/10000000000 : ℝ), (-1324601061/10000000000 : ℝ), (-6794646649/10000000000 : ℝ)] ![(32902469624631/100000000000000 : ℝ), (6981260484453/100000000000000 : ℝ), (60116269877643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299164337/10000000000 : ℝ)|^133 ≤ (32902469624631/100000000000000 : ℝ)^101
        have hw : |(4299164337/10000000000 : ℝ)|=(4299164337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324601061/10000000000 : ℝ)|^133 ≤ (6981260484453/100000000000000 : ℝ)^101
        have hw : |(-1324601061/10000000000 : ℝ)|=(1324601061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6794646649/10000000000 : ℝ)|^133 ≤ (60116269877643/100000000000000 : ℝ)^101
        have hw : |(-6794646649/10000000000 : ℝ)|=(6794646649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1252768369/2000000000 : ℝ)*x 0 + (1240006749/2500000000 : ℝ)*x 1 + (305223273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1252768369/2000000000 : ℝ)^133 ≤ (2700495833967/5000000000000 : ℝ)^101 := by
    have hnat : (1252768369 : ℕ)^133*5000000000000^101 ≤ 2700495833967^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252768369 2000000000 2700495833967 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240006749/2500000000 : ℝ)^133 ≤ (19859748322387/50000000000000 : ℝ)^101 := by
    have hnat : (1240006749 : ℕ)^133*50000000000000^101 ≤ 19859748322387^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240006749 2500000000 19859748322387 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305223273/2500000000 : ℝ)^133 ≤ (6270586667291/100000000000000 : ℝ)^101 := by
    have hnat : (305223273 : ℕ)^133*100000000000000^101 ≤ 6270586667291^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305223273 2500000000 6270586667291 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1252768369/2000000000 : ℝ), (1240006749/2500000000 : ℝ), (305223273/2500000000 : ℝ)] ![(2700495833967/5000000000000 : ℝ), (19859748322387/50000000000000 : ℝ), (6270586667291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1252768369/2000000000 : ℝ)|^133 ≤ (2700495833967/5000000000000 : ℝ)^101
        have hw : |(1252768369/2000000000 : ℝ)|=(1252768369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1240006749/2500000000 : ℝ)|^133 ≤ (19859748322387/50000000000000 : ℝ)^101
        have hw : |(1240006749/2500000000 : ℝ)|=(1240006749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305223273/2500000000 : ℝ)|^133 ≤ (6270586667291/100000000000000 : ℝ)^101
        have hw : |(305223273/2500000000 : ℝ)|=(305223273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7048354949/10000000000 : ℝ)*x 0 + (462745011/1000000000 : ℝ)*x 1 + (-27617087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7048354949/10000000000 : ℝ)^133 ≤ (63089510536403/100000000000000 : ℝ)^101 := by
    have hnat : (7048354949 : ℕ)^133*100000000000000^101 ≤ 63089510536403^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7048354949 10000000000 63089510536403 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462745011/1000000000 : ℝ)^133 ≤ (18125141735343/50000000000000 : ℝ)^101 := by
    have hnat : (462745011 : ℕ)^133*50000000000000^101 ≤ 18125141735343^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462745011 1000000000 18125141735343 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27617087/1250000000 : ℝ)^133 ≤ (825257473/125000000000 : ℝ)^101 := by
    have hnat : (27617087 : ℕ)^133*125000000000^101 ≤ 825257473^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27617087 1250000000 825257473 125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7048354949/10000000000 : ℝ), (462745011/1000000000 : ℝ), (-27617087/1250000000 : ℝ)] ![(63089510536403/100000000000000 : ℝ), (18125141735343/50000000000000 : ℝ), (825257473/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7048354949/10000000000 : ℝ)|^133 ≤ (63089510536403/100000000000000 : ℝ)^101
        have hw : |(7048354949/10000000000 : ℝ)|=(7048354949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462745011/1000000000 : ℝ)|^133 ≤ (18125141735343/50000000000000 : ℝ)^101
        have hw : |(462745011/1000000000 : ℝ)|=(462745011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27617087/1250000000 : ℝ)|^133 ≤ (825257473/125000000000 : ℝ)^101
        have hw : |(-27617087/1250000000 : ℝ)|=(27617087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-543975181/10000000000 : ℝ)*x 0 + (5760417183/10000000000 : ℝ)*x 1 + (-366235041/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543975181/10000000000 : ℝ)^133 ≤ (216257151747/10000000000000 : ℝ)^101 := by
    have hnat : (543975181 : ℕ)^133*10000000000000^101 ≤ 216257151747^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543975181 10000000000 216257151747 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5760417183/10000000000 : ℝ)^133 ≤ (9673600558723/20000000000000 : ℝ)^101 := by
    have hnat : (5760417183 : ℕ)^133*20000000000000^101 ≤ 9673600558723^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5760417183 10000000000 9673600558723 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366235041/625000000 : ℝ)^133 ≤ (49469425673061/100000000000000 : ℝ)^101 := by
    have hnat : (366235041 : ℕ)^133*100000000000000^101 ≤ 49469425673061^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366235041 625000000 49469425673061 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543975181/10000000000 : ℝ), (5760417183/10000000000 : ℝ), (-366235041/625000000 : ℝ)] ![(216257151747/10000000000000 : ℝ), (9673600558723/20000000000000 : ℝ), (49469425673061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543975181/10000000000 : ℝ)|^133 ≤ (216257151747/10000000000000 : ℝ)^101
        have hw : |(-543975181/10000000000 : ℝ)|=(543975181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5760417183/10000000000 : ℝ)|^133 ≤ (9673600558723/20000000000000 : ℝ)^101
        have hw : |(5760417183/10000000000 : ℝ)|=(5760417183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-366235041/625000000 : ℝ)|^133 ≤ (49469425673061/100000000000000 : ℝ)^101
        have hw : |(-366235041/625000000 : ℝ)|=(366235041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6248121641/10000000000 : ℝ)*x 0 + (-206661051/2000000000 : ℝ)*x 1 + (-127341393/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6248121641/10000000000 : ℝ)^133 ≤ (26915747346141/50000000000000 : ℝ)^101 := by
    have hnat : (6248121641 : ℕ)^133*50000000000000^101 ≤ 26915747346141^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6248121641 10000000000 26915747346141 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206661051/2000000000 : ℝ)^133 ≤ (5033905266081/100000000000000 : ℝ)^101 := by
    have hnat : (206661051 : ℕ)^133*100000000000000^101 ≤ 5033905266081^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206661051 2000000000 5033905266081 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127341393/250000000 : ℝ)^133 ≤ (4113460002913/10000000000000 : ℝ)^101 := by
    have hnat : (127341393 : ℕ)^133*10000000000000^101 ≤ 4113460002913^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127341393 250000000 4113460002913 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6248121641/10000000000 : ℝ), (-206661051/2000000000 : ℝ), (-127341393/250000000 : ℝ)] ![(26915747346141/50000000000000 : ℝ), (5033905266081/100000000000000 : ℝ), (4113460002913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6248121641/10000000000 : ℝ)|^133 ≤ (26915747346141/50000000000000 : ℝ)^101
        have hw : |(6248121641/10000000000 : ℝ)|=(6248121641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206661051/2000000000 : ℝ)|^133 ≤ (5033905266081/100000000000000 : ℝ)^101
        have hw : |(-206661051/2000000000 : ℝ)|=(206661051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127341393/250000000 : ℝ)|^133 ≤ (4113460002913/10000000000000 : ℝ)^101
        have hw : |(-127341393/250000000 : ℝ)|=(127341393/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4458033741/10000000000 : ℝ)*x 0 + (1227934407/2000000000 : ℝ)*x 1 + (210930501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458033741/10000000000 : ℝ)^133 ≤ (34512851957287/100000000000000 : ℝ)^101 := by
    have hnat : (4458033741 : ℕ)^133*100000000000000^101 ≤ 34512851957287^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458033741 10000000000 34512851957287 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1227934407/2000000000 : ℝ)^133 ≤ (26302247238843/50000000000000 : ℝ)^101 := by
    have hnat : (1227934407 : ℕ)^133*50000000000000^101 ≤ 26302247238843^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227934407 2000000000 26302247238843 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210930501/1000000000 : ℝ)^133 ≤ (12882653553491/100000000000000 : ℝ)^101 := by
    have hnat : (210930501 : ℕ)^133*100000000000000^101 ≤ 12882653553491^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210930501 1000000000 12882653553491 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458033741/10000000000 : ℝ), (1227934407/2000000000 : ℝ), (210930501/1000000000 : ℝ)] ![(34512851957287/100000000000000 : ℝ), (26302247238843/50000000000000 : ℝ), (12882653553491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458033741/10000000000 : ℝ)|^133 ≤ (34512851957287/100000000000000 : ℝ)^101
        have hw : |(4458033741/10000000000 : ℝ)|=(4458033741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1227934407/2000000000 : ℝ)|^133 ≤ (26302247238843/50000000000000 : ℝ)^101
        have hw : |(1227934407/2000000000 : ℝ)|=(1227934407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210930501/1000000000 : ℝ)|^133 ≤ (12882653553491/100000000000000 : ℝ)^101
        have hw : |(210930501/1000000000 : ℝ)|=(210930501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s4_s4_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7457933139/10000000000 : ℝ)*x 0 + (4035120277/10000000000 : ℝ)*x 1 + (-467466259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7457933139/10000000000 : ℝ)^133 ≤ (67961035262189/100000000000000 : ℝ)^101 := by
    have hnat : (7457933139 : ℕ)^133*100000000000000^101 ≤ 67961035262189^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7457933139 10000000000 67961035262189 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4035120277/10000000000 : ℝ)^133 ≤ (30267693747873/100000000000000 : ℝ)^101 := by
    have hnat : (4035120277 : ℕ)^133*100000000000000^101 ≤ 30267693747873^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035120277 10000000000 30267693747873 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467466259/10000000000 : ℝ)^133 ≤ (110704436553/6250000000000 : ℝ)^101 := by
    have hnat : (467466259 : ℕ)^133*6250000000000^101 ≤ 110704436553^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467466259 10000000000 110704436553 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7457933139/10000000000 : ℝ), (4035120277/10000000000 : ℝ), (-467466259/10000000000 : ℝ)] ![(67961035262189/100000000000000 : ℝ), (30267693747873/100000000000000 : ℝ), (110704436553/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7457933139/10000000000 : ℝ)|^133 ≤ (67961035262189/100000000000000 : ℝ)^101
        have hw : |(7457933139/10000000000 : ℝ)|=(7457933139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4035120277/10000000000 : ℝ)|^133 ≤ (30267693747873/100000000000000 : ℝ)^101
        have hw : |(4035120277/10000000000 : ℝ)|=(4035120277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467466259/10000000000 : ℝ)|^133 ≤ (110704436553/6250000000000 : ℝ)^101
        have hw : |(-467466259/10000000000 : ℝ)|=(467466259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304062_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((2346/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2346/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75139/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75139/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28669/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28669/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27493/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27493/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55371/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9447/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (2346/3125 : ℝ) ^ (33/8 : ℝ) ≤ (15322043711974862137/50000000000000000000 : ℝ) := by
    have hpowers : (2346/3125 : ℝ)^33 ≤ (15322043711974862137/50000000000000000000 : ℝ)^8 := by
      have hnat : (2346 : ℕ)^33*50000000000000000000^8 ≤ 15322043711974862137^8*3125^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2346 3125 15322043711974862137 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2346/3125 : ℝ)) (X := (15322043711974862137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (65322043711974862137/50000000000000000000 : ℝ) ≤ (1066947308070563/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (65322043711974862137/50000000000000000000 : ℝ)^8 ≤ (1066947308070563/1000000000000000 : ℝ)^33 := by
      have hnat : (65322043711974862137 : ℕ)^8*1000000000000000^33 ≤ 1066947308070563^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65322043711974862137 50000000000000000000 1066947308070563 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1066947308070563/1000000000000000 : ℝ)) (X := (65322043711974862137/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (40322043711974862137/25000000000000000000 : ℝ) ≤ (11228658802699011/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (40322043711974862137/25000000000000000000 : ℝ)^8 ≤ (11228658802699011/10000000000000000 : ℝ)^33 := by
      have hnat : (40322043711974862137 : ℕ)^8*10000000000000000^33 ≤ 11228658802699011^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40322043711974862137 25000000000000000000 11228658802699011 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11228658802699011/10000000000000000 : ℝ)) (X := (40322043711974862137/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(66947308070563/750720000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(559185721993381/7507200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (2346/3125 : ℝ)) (alpha := (66947308070563/750720000000000 : ℝ)) (beta := (559185721993381/7507200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2346/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(66947308070563/750720000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(559185721993381/7507200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (75139/100000 : ℝ) ^ (33/8 : ℝ) ≤ (1922316250197805337/6250000000000000000 : ℝ) := by
    have hpowers : (75139/100000 : ℝ)^33 ≤ (1922316250197805337/6250000000000000000 : ℝ)^8 := by
      have hnat : (75139 : ℕ)^33*6250000000000000000^8 ≤ 1922316250197805337^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75139 100000 1922316250197805337 6250000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75139/100000 : ℝ)) (X := (1922316250197805337/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (8172316250197805337/6250000000000000000 : ℝ) ≤ (10671709020464733/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (8172316250197805337/6250000000000000000 : ℝ)^8 ≤ (10671709020464733/10000000000000000 : ℝ)^33 := by
      have hnat : (8172316250197805337 : ℕ)^8*10000000000000000^33 ≤ 10671709020464733^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8172316250197805337 6250000000000000000 10671709020464733 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10671709020464733/10000000000000000 : ℝ)) (X := (8172316250197805337/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (5047316250197805337/3125000000000000000 : ℝ) ≤ (5616235055674241/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5047316250197805337/3125000000000000000 : ℝ)^8 ≤ (5616235055674241/5000000000000000 : ℝ)^33 := by
      have hnat : (5047316250197805337 : ℕ)^8*5000000000000000^33 ≤ 5616235055674241^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5047316250197805337 3125000000000000000 5616235055674241 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5616235055674241/5000000000000000 : ℝ)) (X := (5047316250197805337/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(671709020464733/7513900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(560761090883749/7513900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (75139/100000 : ℝ)) (alpha := (671709020464733/7513900000000000 : ℝ)) (beta := (560761090883749/7513900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75139/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(671709020464733/7513900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(560761090883749/7513900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (28669/50000 : ℝ) ^ (33/8 : ℝ) ≤ (2016533654196979899/20000000000000000000 : ℝ) := by
    have hpowers : (28669/50000 : ℝ)^33 ≤ (2016533654196979899/20000000000000000000 : ℝ)^8 := by
      have hnat : (28669 : ℕ)^33*20000000000000000000^8 ≤ 2016533654196979899^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28669 50000 2016533654196979899 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28669/50000 : ℝ)) (X := (2016533654196979899/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (22016533654196979899/20000000000000000000 : ℝ) ≤ (10235608925039731/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (22016533654196979899/20000000000000000000 : ℝ)^8 ≤ (10235608925039731/10000000000000000 : ℝ)^33 := by
      have hnat : (22016533654196979899 : ℕ)^8*10000000000000000^33 ≤ 10235608925039731^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22016533654196979899 20000000000000000000 10235608925039731 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10235608925039731/10000000000000000 : ℝ)) (X := (22016533654196979899/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (12016533654196979899/10000000000000000000 : ℝ) ≤ (10455394252117787/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12016533654196979899/10000000000000000000 : ℝ)^8 ≤ (10455394252117787/10000000000000000 : ℝ)^33 := by
      have hnat : (12016533654196979899 : ℕ)^8*10000000000000000^33 ≤ 10455394252117787^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12016533654196979899 10000000000000000000 10455394252117787 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10455394252117787/10000000000000000 : ℝ)) (X := (12016533654196979899/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(235608925039731/5733800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(27473165884757/716725000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (28669/50000 : ℝ)) (alpha := (235608925039731/5733800000000000 : ℝ)) (beta := (27473165884757/716725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28669/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(235608925039731/5733800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(27473165884757/716725000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1759719631/10000000000 : ℝ)*X 0 0+(4925197549/10000000000 : ℝ)*X 0 1+(-5952186047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((38543899/78125000 : ℝ)*X 1 0+(-884871759/5000000000 : ℝ)*X 1 1+(-5937427601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((5288677199/10000000000 : ℝ)*X 2 0+(5298936671/10000000000 : ℝ)*X 2 1+(435836831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((2805099157/5000000000 : ℝ)*X 0 0+(5585719559/10000000000 : ℝ)*X 0 1+(-326061127/2500000000 : ℝ)*X 0 2+(2805099157/5000000000 : ℝ)*X 1 0+(5585719559/10000000000 : ℝ)*X 1 1+(-326061127/2500000000 : ℝ)*X 1 2+(2805099157/5000000000 : ℝ)*X 2 0+(5585719559/10000000000 : ℝ)*X 2 1+(-326061127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-53419137/400000000 : ℝ)*X 0 0+(4286845383/10000000000 : ℝ)*X 0 1+(-6798809379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((914012909/2000000000 : ℝ)*X 1 0+(-894548177/10000000000 : ℝ)*X 1 1+(-6799877067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1184995273/2500000000 : ℝ)*X 2 0+(1617202413/2500000000 : ℝ)*X 2 1+(607832981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((5081860203/10000000000 : ℝ)*X 0 0+(1328882797/2000000000 : ℝ)*X 0 1+(-210303777/10000000000 : ℝ)*X 0 2+(5081860203/10000000000 : ℝ)*X 1 0+(1328882797/2000000000 : ℝ)*X 1 1+(-210303777/10000000000 : ℝ)*X 1 2+(5081860203/10000000000 : ℝ)*X 2 0+(1328882797/2000000000 : ℝ)*X 2 1+(-210303777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-444275961/5000000000 : ℝ)*X 0 0+(916154781/2000000000 : ℝ)*X 0 1+(-3396790131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4299164337/10000000000 : ℝ)*X 1 0+(-1324601061/10000000000 : ℝ)*X 1 1+(-6794646649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1252768369/2000000000 : ℝ)*X 2 0+(1240006749/2500000000 : ℝ)*X 2 1+(305223273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((7048354949/10000000000 : ℝ)*X 0 0+(462745011/1000000000 : ℝ)*X 0 1+(-27617087/1250000000 : ℝ)*X 0 2+(7048354949/10000000000 : ℝ)*X 1 0+(462745011/1000000000 : ℝ)*X 1 1+(-27617087/1250000000 : ℝ)*X 1 2+(7048354949/10000000000 : ℝ)*X 2 0+(462745011/1000000000 : ℝ)*X 2 1+(-27617087/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-543975181/10000000000 : ℝ)*X 0 0+(5760417183/10000000000 : ℝ)*X 0 1+(-366235041/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6248121641/10000000000 : ℝ)*X 1 0+(-206661051/2000000000 : ℝ)*X 1 1+(-127341393/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4458033741/10000000000 : ℝ)*X 2 0+(1227934407/2000000000 : ℝ)*X 2 1+(210930501/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((7457933139/10000000000 : ℝ)*X 0 0+(4035120277/10000000000 : ℝ)*X 0 1+(-467466259/10000000000 : ℝ)*X 0 2+(7457933139/10000000000 : ℝ)*X 1 0+(4035120277/10000000000 : ℝ)*X 1 1+(-467466259/10000000000 : ℝ)*X 1 2+(7457933139/10000000000 : ℝ)*X 2 0+(4035120277/10000000000 : ℝ)*X 2 1+(-467466259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((27493/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27493/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (46643986959833201698779639/13463499943750000000000000000000 : ℝ) := by norm_num
    linear_combination (1451189/1000000000000 : ℝ)*(base39) + (749123/1000000000000 : ℝ)*(base49) + (29519443387/250000000000 : ℝ)*(base60) + (2313079458547/500000000000 : ℝ)*(major_s4_0) + (2313079458547/500000000000 : ℝ)*(major_s4_1) + (2313079458547/500000000000 : ℝ)*(major_s4_2) + (658589/1000000000000 : ℝ)*(sp_s4_0) + (839039/250000000000 : ℝ)*(sp_s4_1) + (3101104303341/500000000000 : ℝ)*(sp_s4_7) + (620218887867/100000000000 : ℝ)*(sp_s4_8) + (6202187993027/1000000000000 : ℝ)*(sp_s4_9) + (3050107414087/1000000000000 : ℝ)*(sp_s4_13) + (3406089/200000000000 : ℝ)*(sp_s4_15) + (5318061/250000000000 : ℝ)*(sp_s4_23) + (3050107414087/1000000000000 : ℝ)*(f.failure) + (6202209265271/1000000000000 : ℝ)*(f.sum) + (47930822870815512241/215415999100000000000000000000000 : ℝ)*base63 + (34076462242963/716725000000000000000000000 : ℝ)*base65 + (882464870639097/3756950000000000000000000000 : ℝ)*base66 + (2552346611657337/2866900000000000000000000000 : ℝ)*base69 + (31542244642991640919/53805979200000000000000000000000 : ℝ)*base70 + (1099895868474593/3753600000000000000000000000 : ℝ)*base72 + (490621657158349/939237500000000000000000000 : ℝ)*base75 + (200821465895257/375360000000000000000000000 : ℝ)*base77 + (265255905125443866589/282041750400000000000000000000000 : ℝ)*base79 + (433/12500000000000000 : ℝ)*base87 + (433/12500000000000000 : ℝ)*base89 + (433/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55371/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3308722101309807466756287417/215415999100000000000000000000000 : ℝ) := by norm_num
    linear_combination (4059119/1000000000000 : ℝ)*(base18) + (3573953/1000000000000 : ℝ)*(base60) + (4649081502979/1000000000000 : ℝ)*(major_s4_0) + (4649081502979/1000000000000 : ℝ)*(major_s4_1) + (4649081502979/1000000000000 : ℝ)*(major_s4_2) + (49663177/1000000000000 : ℝ)*(sp_s4_2) + (710253/125000000000 : ℝ)*(sp_s4_6) + (46366661/500000000000 : ℝ)*(sp_s4_7) + (3913509/100000000000 : ℝ)*(sp_s4_8) + (194776389913/31250000000 : ℝ)*(sp_s4_14) + (6232894016329/1000000000000 : ℝ)*(sp_s4_15) + (6232887547361/1000000000000 : ℝ)*(sp_s4_16) + (38313779813/12500000000 : ℝ)*(sp_s4_20) + (112608459/1000000000000 : ℝ)*(sp_s4_27) + (3065220675523/1000000000000 : ℝ)*(f.failure) + (3116468605269/500000000000 : ℝ)*(f.sum) + (7366672570121346477/430831998200000000000000000000000 : ℝ)*base63 + (67947430601719/1433450000000000000000000000 : ℝ)*base64 + (1822240841946959/7513900000000000000000000000 : ℝ)*base66 + (760100204035049/5733800000000000000000000000 : ℝ)*base69 + (25583408539334270503/107611958400000000000000000000000 : ℝ)*base70 + (2584532360603921/7507200000000000000000000000 : ℝ)*base72 + (1522085740554257/7513900000000000000000000000 : ℝ)*base75 + (73808852704873/750720000000000000000000000 : ℝ)*base77 + (59901398447788304653/564083500800000000000000000000000 : ℝ)*base79 + (3057/12500000000000000 : ℝ)*base87 + (3057/12500000000000000 : ℝ)*base89 + (3057/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9447/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1416110800862096887660005088073/539056996147840000000000000000000000 : ℝ) := by norm_num
    linear_combination (318429/125000000000 : ℝ)*(base11) + (178379951763/500000000000 : ℝ)*(base39) + (316877/1000000000000 : ℝ)*(base59) + (3468634930049/1000000000000 : ℝ)*(major_s4_0) + (3468634930049/1000000000000 : ℝ)*(major_s4_1) + (3468634930049/1000000000000 : ℝ)*(major_s4_2) + (146629/25000000000 : ℝ)*(sp_s4_0) + (456627/250000000000 : ℝ)*(sp_s4_1) + (3202569/500000000000 : ℝ)*(sp_s4_2) + (3828709/250000000000 : ℝ)*(sp_s4_9) + (2325164474807/500000000000 : ℝ)*(sp_s4_21) + (2325167767849/500000000000 : ℝ)*(sp_s4_22) + (4650315642231/1000000000000 : ℝ)*(sp_s4_23) + (2286931622217/1000000000000 : ℝ)*(sp_s4_27) + (2286931622217/1000000000000 : ℝ)*(f.failure) + (930067472441/200000000000 : ℝ)*(f.sum) + (4785360026464647793/430831998200000000000000000000000 : ℝ)*base62 + (896317213734109/1433450000000000000000000000 : ℝ)*base64 + (357377922978431/7513900000000000000000000000 : ℝ)*base67 + (1227123634243841/5733800000000000000000000000 : ℝ)*base68 + (24402858509391350093/107611958400000000000000000000000 : ℝ)*base70 + (1779021136826789/7507200000000000000000000000 : ℝ)*base73 + (2161901858817797/7513900000000000000000000000 : ℝ)*base75 + (315460060633379/750720000000000000000000000 : ℝ)*base77 + (64004993609595156143/564083500800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (397/12500000000000000 : ℝ)*base86 + (397/12500000000000000 : ℝ)*base88 + (397/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((2346/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2346/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75139/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75139/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28669/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28669/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27493/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27493/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55371/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9447/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304062_s4 p hpa hpb X hX hprev3

#print axioms solution

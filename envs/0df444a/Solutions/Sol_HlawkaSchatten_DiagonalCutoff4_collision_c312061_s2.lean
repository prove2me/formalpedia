-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312061_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:50.798374+00:00
-- url     : https://prove2.me/submissions/361af1a0-958c-43d8-9c57-439fea882759

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
theorem collision_support_c312061_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912869761/10000000000 : ℝ)*x 0 + (2267610277/5000000000 : ℝ)*x 1 + (2984936981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912869761/10000000000 : ℝ)^73 ≤ (1503014764873/12500000000000 : ℝ)^57 := by
    have hnat : (1912869761 : ℕ)^73*12500000000000^57 ≤ 1503014764873^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912869761 10000000000 1503014764873 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267610277/5000000000 : ℝ)^73 ≤ (36324946564473/100000000000000 : ℝ)^57 := by
    have hnat : (2267610277 : ℕ)^73*100000000000000^57 ≤ 36324946564473^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267610277 5000000000 36324946564473 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2984936981/5000000000 : ℝ)^73 ≤ (25825467654933/50000000000000 : ℝ)^57 := by
    have hnat : (2984936981 : ℕ)^73*50000000000000^57 ≤ 25825467654933^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2984936981 5000000000 25825467654933 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912869761/10000000000 : ℝ), (2267610277/5000000000 : ℝ), (2984936981/5000000000 : ℝ)] ![(1503014764873/12500000000000 : ℝ), (36324946564473/100000000000000 : ℝ), (25825467654933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912869761/10000000000 : ℝ)|^73 ≤ (1503014764873/12500000000000 : ℝ)^57
        have hw : |(-1912869761/10000000000 : ℝ)|=(1912869761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2267610277/5000000000 : ℝ)|^73 ≤ (36324946564473/100000000000000 : ℝ)^57
        have hw : |(2267610277/5000000000 : ℝ)|=(2267610277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2984936981/5000000000 : ℝ)|^73 ≤ (25825467654933/50000000000000 : ℝ)^57
        have hw : |(2984936981/5000000000 : ℝ)|=(2984936981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (941557893/2000000000 : ℝ)*x 0 + (-971461631/5000000000 : ℝ)*x 1 + (2893297213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941557893/2000000000 : ℝ)^73 ≤ (47630617599/125000000000 : ℝ)^57 := by
    have hnat : (941557893 : ℕ)^73*125000000000^57 ≤ 47630617599^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941557893 2000000000 47630617599 125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971461631/5000000000 : ℝ)^73 ≤ (12266591424517/100000000000000 : ℝ)^57 := by
    have hnat : (971461631 : ℕ)^73*100000000000000^57 ≤ 12266591424517^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971461631 5000000000 12266591424517 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2893297213/5000000000 : ℝ)^73 ≤ (24814457240977/50000000000000 : ℝ)^57 := by
    have hnat : (2893297213 : ℕ)^73*50000000000000^57 ≤ 24814457240977^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893297213 5000000000 24814457240977 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(941557893/2000000000 : ℝ), (-971461631/5000000000 : ℝ), (2893297213/5000000000 : ℝ)] ![(47630617599/125000000000 : ℝ), (12266591424517/100000000000000 : ℝ), (24814457240977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(941557893/2000000000 : ℝ)|^73 ≤ (47630617599/125000000000 : ℝ)^57
        have hw : |(941557893/2000000000 : ℝ)|=(941557893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971461631/5000000000 : ℝ)|^73 ≤ (12266591424517/100000000000000 : ℝ)^57
        have hw : |(-971461631/5000000000 : ℝ)|=(971461631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2893297213/5000000000 : ℝ)|^73 ≤ (24814457240977/50000000000000 : ℝ)^57
        have hw : |(2893297213/5000000000 : ℝ)|=(2893297213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2397288481/5000000000 : ℝ)*x 0 + (1280932953/2000000000 : ℝ)*x 1 + (-88434697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2397288481/5000000000 : ℝ)^73 ≤ (39006442371451/100000000000000 : ℝ)^57 := by
    have hnat : (2397288481 : ℕ)^73*100000000000000^57 ≤ 39006442371451^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397288481 5000000000 39006442371451 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280932953/2000000000 : ℝ)^73 ≤ (56517065407523/100000000000000 : ℝ)^57 := by
    have hnat : (1280932953 : ℕ)^73*100000000000000^57 ≤ 56517065407523^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280932953 2000000000 56517065407523 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88434697/1000000000 : ℝ)^73 ≤ (2238246108817/50000000000000 : ℝ)^57 := by
    have hnat : (88434697 : ℕ)^73*50000000000000^57 ≤ 2238246108817^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88434697 1000000000 2238246108817 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2397288481/5000000000 : ℝ), (1280932953/2000000000 : ℝ), (-88434697/1000000000 : ℝ)] ![(39006442371451/100000000000000 : ℝ), (56517065407523/100000000000000 : ℝ), (2238246108817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2397288481/5000000000 : ℝ)|^73 ≤ (39006442371451/100000000000000 : ℝ)^57
        have hw : |(2397288481/5000000000 : ℝ)|=(2397288481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1280932953/2000000000 : ℝ)|^73 ≤ (56517065407523/100000000000000 : ℝ)^57
        have hw : |(1280932953/2000000000 : ℝ)|=(1280932953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88434697/1000000000 : ℝ)|^73 ≤ (2238246108817/50000000000000 : ℝ)^57
        have hw : |(-88434697/1000000000 : ℝ)|=(88434697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6295865961/10000000000 : ℝ)*x 0 + (2813535417/10000000000 : ℝ)*x 1 + (3387747169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6295865961/10000000000 : ℝ)^73 ≤ (27645216568191/50000000000000 : ℝ)^57 := by
    have hnat : (6295865961 : ℕ)^73*50000000000000^57 ≤ 27645216568191^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6295865961 10000000000 27645216568191 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2813535417/10000000000 : ℝ)^73 ≤ (9854317921679/50000000000000 : ℝ)^57 := by
    have hnat : (2813535417 : ℕ)^73*50000000000000^57 ≤ 9854317921679^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813535417 10000000000 9854317921679 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3387747169/10000000000 : ℝ)^73 ≤ (5000186199987/20000000000000 : ℝ)^57 := by
    have hnat : (3387747169 : ℕ)^73*20000000000000^57 ≤ 5000186199987^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3387747169 10000000000 5000186199987 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6295865961/10000000000 : ℝ), (2813535417/10000000000 : ℝ), (3387747169/10000000000 : ℝ)] ![(27645216568191/50000000000000 : ℝ), (9854317921679/50000000000000 : ℝ), (5000186199987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6295865961/10000000000 : ℝ)|^73 ≤ (27645216568191/50000000000000 : ℝ)^57
        have hw : |(6295865961/10000000000 : ℝ)|=(6295865961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2813535417/10000000000 : ℝ)|^73 ≤ (9854317921679/50000000000000 : ℝ)^57
        have hw : |(2813535417/10000000000 : ℝ)|=(2813535417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3387747169/10000000000 : ℝ)|^73 ≤ (5000186199987/20000000000000 : ℝ)^57
        have hw : |(3387747169/10000000000 : ℝ)|=(3387747169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-909882463/5000000000 : ℝ)*x 0 + (946728129/2500000000 : ℝ)*x 1 + (3350428831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (909882463/5000000000 : ℝ)^73 ≤ (11279771031181/100000000000000 : ℝ)^57 := by
    have hnat : (909882463 : ℕ)^73*100000000000000^57 ≤ 11279771031181^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909882463 5000000000 11279771031181 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946728129/2500000000 : ℝ)^73 ≤ (2883428643803/10000000000000 : ℝ)^57 := by
    have hnat : (946728129 : ℕ)^73*10000000000000^57 ≤ 2883428643803^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946728129 2500000000 2883428643803 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3350428831/5000000000 : ℝ)^73 ≤ (3742871407239/6250000000000 : ℝ)^57 := by
    have hnat : (3350428831 : ℕ)^73*6250000000000^57 ≤ 3742871407239^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3350428831 5000000000 3742871407239 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-909882463/5000000000 : ℝ), (946728129/2500000000 : ℝ), (3350428831/5000000000 : ℝ)] ![(11279771031181/100000000000000 : ℝ), (2883428643803/10000000000000 : ℝ), (3742871407239/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-909882463/5000000000 : ℝ)|^73 ≤ (11279771031181/100000000000000 : ℝ)^57
        have hw : |(-909882463/5000000000 : ℝ)|=(909882463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(946728129/2500000000 : ℝ)|^73 ≤ (2883428643803/10000000000000 : ℝ)^57
        have hw : |(946728129/2500000000 : ℝ)|=(946728129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3350428831/5000000000 : ℝ)|^73 ≤ (3742871407239/6250000000000 : ℝ)^57
        have hw : |(3350428831/5000000000 : ℝ)|=(3350428831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2094292329/5000000000 : ℝ)*x 0 + (-1324419917/10000000000 : ℝ)*x 1 + (6683120509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094292329/5000000000 : ℝ)^73 ≤ (32808088293957/100000000000000 : ℝ)^57 := by
    have hnat : (2094292329 : ℕ)^73*100000000000000^57 ≤ 32808088293957^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094292329 5000000000 32808088293957 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324419917/10000000000 : ℝ)^73 ≤ (375445395169/5000000000000 : ℝ)^57 := by
    have hnat : (1324419917 : ℕ)^73*5000000000000^57 ≤ 375445395169^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324419917 10000000000 375445395169 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6683120509/10000000000 : ℝ)^73 ≤ (59683003786693/100000000000000 : ℝ)^57 := by
    have hnat : (6683120509 : ℕ)^73*100000000000000^57 ≤ 59683003786693^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6683120509 10000000000 59683003786693 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094292329/5000000000 : ℝ), (-1324419917/10000000000 : ℝ), (6683120509/10000000000 : ℝ)] ![(32808088293957/100000000000000 : ℝ), (375445395169/5000000000000 : ℝ), (59683003786693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094292329/5000000000 : ℝ)|^73 ≤ (32808088293957/100000000000000 : ℝ)^57
        have hw : |(2094292329/5000000000 : ℝ)|=(2094292329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324419917/10000000000 : ℝ)|^73 ≤ (375445395169/5000000000000 : ℝ)^57
        have hw : |(-1324419917/10000000000 : ℝ)|=(1324419917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6683120509/10000000000 : ℝ)|^73 ≤ (59683003786693/100000000000000 : ℝ)^57
        have hw : |(6683120509/10000000000 : ℝ)|=(6683120509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (855330937/2000000000 : ℝ)*x 0 + (7235945557/10000000000 : ℝ)*x 1 + (-86524773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855330937/2000000000 : ℝ)^73 ≤ (33694148255153/100000000000000 : ℝ)^57 := by
    have hnat : (855330937 : ℕ)^73*100000000000000^57 ≤ 33694148255153^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855330937 2000000000 33694148255153 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7235945557/10000000000 : ℝ)^73 ≤ (33038884559549/50000000000000 : ℝ)^57 := by
    have hnat : (7235945557 : ℕ)^73*50000000000000^57 ≤ 33038884559549^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7235945557 10000000000 33038884559549 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86524773/10000000000 : ℝ)^73 ≤ (22808261263/10000000000000 : ℝ)^57 := by
    have hnat : (86524773 : ℕ)^73*10000000000000^57 ≤ 22808261263^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86524773 10000000000 22808261263 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855330937/2000000000 : ℝ), (7235945557/10000000000 : ℝ), (-86524773/10000000000 : ℝ)] ![(33694148255153/100000000000000 : ℝ), (33038884559549/50000000000000 : ℝ), (22808261263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855330937/2000000000 : ℝ)|^73 ≤ (33694148255153/100000000000000 : ℝ)^57
        have hw : |(855330937/2000000000 : ℝ)|=(855330937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7235945557/10000000000 : ℝ)|^73 ≤ (33038884559549/50000000000000 : ℝ)^57
        have hw : |(7235945557/10000000000 : ℝ)|=(7235945557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86524773/10000000000 : ℝ)|^73 ≤ (22808261263/10000000000000 : ℝ)^57
        have hw : |(-86524773/10000000000 : ℝ)|=(86524773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6011981043/10000000000 : ℝ)*x 0 + (4511452741/10000000000 : ℝ)*x 1 + (377012403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6011981043/10000000000 : ℝ)^73 ≤ (814343214259/1562500000000 : ℝ)^57 := by
    have hnat : (6011981043 : ℕ)^73*1562500000000^57 ≤ 814343214259^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011981043 10000000000 814343214259 1562500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511452741/10000000000 : ℝ)^73 ≤ (36081320450827/100000000000000 : ℝ)^57 := by
    have hnat : (4511452741 : ℕ)^73*100000000000000^57 ≤ 36081320450827^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511452741 10000000000 36081320450827 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377012403/2000000000 : ℝ)^73 ≤ (11800713827807/100000000000000 : ℝ)^57 := by
    have hnat : (377012403 : ℕ)^73*100000000000000^57 ≤ 11800713827807^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377012403 2000000000 11800713827807 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6011981043/10000000000 : ℝ), (4511452741/10000000000 : ℝ), (377012403/2000000000 : ℝ)] ![(814343214259/1562500000000 : ℝ), (36081320450827/100000000000000 : ℝ), (11800713827807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6011981043/10000000000 : ℝ)|^73 ≤ (814343214259/1562500000000 : ℝ)^57
        have hw : |(6011981043/10000000000 : ℝ)|=(6011981043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511452741/10000000000 : ℝ)|^73 ≤ (36081320450827/100000000000000 : ℝ)^57
        have hw : |(4511452741/10000000000 : ℝ)|=(4511452741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377012403/2000000000 : ℝ)|^73 ≤ (11800713827807/100000000000000 : ℝ)^57
        have hw : |(377012403/2000000000 : ℝ)|=(377012403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-798826189/10000000000 : ℝ)*x 0 + (113298181/250000000 : ℝ)*x 1 + (334575827/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798826189/10000000000 : ℝ)^73 ≤ (982446108447/25000000000000 : ℝ)^57 := by
    have hnat : (798826189 : ℕ)^73*25000000000000^57 ≤ 982446108447^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798826189 10000000000 982446108447 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113298181/250000000 : ℝ)^73 ≤ (36291167824573/100000000000000 : ℝ)^57 := by
    have hnat : (113298181 : ℕ)^73*100000000000000^57 ≤ 36291167824573^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113298181 250000000 36291167824573 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334575827/500000000 : ℝ)^73 ≤ (29889523863001/50000000000000 : ℝ)^57 := by
    have hnat : (334575827 : ℕ)^73*50000000000000^57 ≤ 29889523863001^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334575827 500000000 29889523863001 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-798826189/10000000000 : ℝ), (113298181/250000000 : ℝ), (334575827/500000000 : ℝ)] ![(982446108447/25000000000000 : ℝ), (36291167824573/100000000000000 : ℝ), (29889523863001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-798826189/10000000000 : ℝ)|^73 ≤ (982446108447/25000000000000 : ℝ)^57
        have hw : |(-798826189/10000000000 : ℝ)|=(798826189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113298181/250000000 : ℝ)|^73 ≤ (36291167824573/100000000000000 : ℝ)^57
        have hw : |(113298181/250000000 : ℝ)|=(113298181/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(334575827/500000000 : ℝ)|^73 ≤ (29889523863001/50000000000000 : ℝ)^57
        have hw : |(334575827/500000000 : ℝ)|=(334575827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4186409303/10000000000 : ℝ)*x 0 + (-1342101417/10000000000 : ℝ)*x 1 + (6673780223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186409303/10000000000 : ℝ)^73 ≤ (6557253604887/20000000000000 : ℝ)^57 := by
    have hnat : (4186409303 : ℕ)^73*20000000000000^57 ≤ 6557253604887^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186409303 10000000000 6557253604887 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342101417/10000000000 : ℝ)^73 ≤ (763753385217/10000000000000 : ℝ)^57 := by
    have hnat : (1342101417 : ℕ)^73*10000000000000^57 ≤ 763753385217^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342101417 10000000000 763753385217 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6673780223/10000000000 : ℝ)^73 ≤ (14894049527619/25000000000000 : ℝ)^57 := by
    have hnat : (6673780223 : ℕ)^73*25000000000000^57 ≤ 14894049527619^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6673780223 10000000000 14894049527619 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186409303/10000000000 : ℝ), (-1342101417/10000000000 : ℝ), (6673780223/10000000000 : ℝ)] ![(6557253604887/20000000000000 : ℝ), (763753385217/10000000000000 : ℝ), (14894049527619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186409303/10000000000 : ℝ)|^73 ≤ (6557253604887/20000000000000 : ℝ)^57
        have hw : |(4186409303/10000000000 : ℝ)|=(4186409303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342101417/10000000000 : ℝ)|^73 ≤ (763753385217/10000000000000 : ℝ)^57
        have hw : |(-1342101417/10000000000 : ℝ)|=(1342101417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6673780223/10000000000 : ℝ)|^73 ≤ (14894049527619/25000000000000 : ℝ)^57
        have hw : |(6673780223/10000000000 : ℝ)|=(6673780223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3003933351/5000000000 : ℝ)*x 0 + (5607249587/10000000000 : ℝ)*x 1 + (-23966267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3003933351/5000000000 : ℝ)^73 ≤ (26036145468693/50000000000000 : ℝ)^57 := by
    have hnat : (3003933351 : ℕ)^73*50000000000000^57 ≤ 26036145468693^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003933351 5000000000 26036145468693 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607249587/10000000000 : ℝ)^73 ≤ (23833813936929/50000000000000 : ℝ)^57 := by
    have hnat : (5607249587 : ℕ)^73*50000000000000^57 ≤ 23833813936929^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607249587 10000000000 23833813936929 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23966267/2500000000 : ℝ)^73 ≤ (130040586043/50000000000000 : ℝ)^57 := by
    have hnat : (23966267 : ℕ)^73*50000000000000^57 ≤ 130040586043^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23966267 2500000000 130040586043 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3003933351/5000000000 : ℝ), (5607249587/10000000000 : ℝ), (-23966267/2500000000 : ℝ)] ![(26036145468693/50000000000000 : ℝ), (23833813936929/50000000000000 : ℝ), (130040586043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3003933351/5000000000 : ℝ)|^73 ≤ (26036145468693/50000000000000 : ℝ)^57
        have hw : |(3003933351/5000000000 : ℝ)|=(3003933351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607249587/10000000000 : ℝ)|^73 ≤ (23833813936929/50000000000000 : ℝ)^57
        have hw : |(5607249587/10000000000 : ℝ)|=(5607249587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23966267/2500000000 : ℝ)|^73 ≤ (130040586043/50000000000000 : ℝ)^57
        have hw : |(-23966267/2500000000 : ℝ)|=(23966267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7677870381/10000000000 : ℝ)*x 0 + (1238057747/5000000000 : ℝ)*x 1 + (953451/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7677870381/10000000000 : ℝ)^73 ≤ (17822460841721/25000000000000 : ℝ)^57 := by
    have hnat : (7677870381 : ℕ)^73*25000000000000^57 ≤ 17822460841721^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7677870381 10000000000 17822460841721 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238057747/5000000000 : ℝ)^73 ≤ (8367030064077/50000000000000 : ℝ)^57 := by
    have hnat : (1238057747 : ℕ)^73*50000000000000^57 ≤ 8367030064077^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238057747 5000000000 8367030064077 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953451/5000000 : ℝ)^73 ≤ (11976096487397/100000000000000 : ℝ)^57 := by
    have hnat : (953451 : ℕ)^73*100000000000000^57 ≤ 11976096487397^57*5000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953451 5000000 11976096487397 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7677870381/10000000000 : ℝ), (1238057747/5000000000 : ℝ), (953451/5000000 : ℝ)] ![(17822460841721/25000000000000 : ℝ), (8367030064077/50000000000000 : ℝ), (11976096487397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7677870381/10000000000 : ℝ)|^73 ≤ (17822460841721/25000000000000 : ℝ)^57
        have hw : |(7677870381/10000000000 : ℝ)|=(7677870381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1238057747/5000000000 : ℝ)|^73 ≤ (8367030064077/50000000000000 : ℝ)^57
        have hw : |(1238057747/5000000000 : ℝ)|=(1238057747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(953451/5000000 : ℝ)|^73 ≤ (11976096487397/100000000000000 : ℝ)^57
        have hw : |(953451/5000000 : ℝ)|=(953451/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-353798339/5000000000 : ℝ)*x 0 + (1108084273/2000000000 : ℝ)*x 1 + (2896270803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353798339/5000000000 : ℝ)^73 ≤ (168224265859/5000000000000 : ℝ)^57 := by
    have hnat : (353798339 : ℕ)^73*5000000000000^57 ≤ 168224265859^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353798339 5000000000 168224265859 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108084273/2000000000 : ℝ)^73 ≤ (9388253411139/20000000000000 : ℝ)^57 := by
    have hnat : (1108084273 : ℕ)^73*20000000000000^57 ≤ 9388253411139^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108084273 2000000000 9388253411139 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2896270803/5000000000 : ℝ)^73 ≤ (49694247608893/100000000000000 : ℝ)^57 := by
    have hnat : (2896270803 : ℕ)^73*100000000000000^57 ≤ 49694247608893^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896270803 5000000000 49694247608893 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353798339/5000000000 : ℝ), (1108084273/2000000000 : ℝ), (2896270803/5000000000 : ℝ)] ![(168224265859/5000000000000 : ℝ), (9388253411139/20000000000000 : ℝ), (49694247608893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353798339/5000000000 : ℝ)|^73 ≤ (168224265859/5000000000000 : ℝ)^57
        have hw : |(-353798339/5000000000 : ℝ)|=(353798339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108084273/2000000000 : ℝ)|^73 ≤ (9388253411139/20000000000000 : ℝ)^57
        have hw : |(1108084273/2000000000 : ℝ)|=(1108084273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2896270803/5000000000 : ℝ)|^73 ≤ (49694247608893/100000000000000 : ℝ)^57
        have hw : |(2896270803/5000000000 : ℝ)|=(2896270803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1502756269/2500000000 : ℝ)*x 0 + (-73063431/1000000000 : ℝ)*x 1 + (1325901997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1502756269/2500000000 : ℝ)^73 ≤ (52107352397293/100000000000000 : ℝ)^57 := by
    have hnat : (1502756269 : ℕ)^73*100000000000000^57 ≤ 52107352397293^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502756269 2500000000 52107352397293 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73063431/1000000000 : ℝ)^73 ≤ (87635220791/2500000000000 : ℝ)^57 := by
    have hnat : (73063431 : ℕ)^73*2500000000000^57 ≤ 87635220791^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73063431 1000000000 87635220791 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1325901997/2500000000 : ℝ)^73 ≤ (22193619381953/50000000000000 : ℝ)^57 := by
    have hnat : (1325901997 : ℕ)^73*50000000000000^57 ≤ 22193619381953^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325901997 2500000000 22193619381953 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1502756269/2500000000 : ℝ), (-73063431/1000000000 : ℝ), (1325901997/2500000000 : ℝ)] ![(52107352397293/100000000000000 : ℝ), (87635220791/2500000000000 : ℝ), (22193619381953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1502756269/2500000000 : ℝ)|^73 ≤ (52107352397293/100000000000000 : ℝ)^57
        have hw : |(1502756269/2500000000 : ℝ)|=(1502756269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73063431/1000000000 : ℝ)|^73 ≤ (87635220791/2500000000000 : ℝ)^57
        have hw : |(-73063431/1000000000 : ℝ)|=(73063431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1325901997/2500000000 : ℝ)|^73 ≤ (22193619381953/50000000000000 : ℝ)^57
        have hw : |(1325901997/2500000000 : ℝ)|=(1325901997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4066204497/10000000000 : ℝ)*x 0 + (1807145199/2500000000 : ℝ)*x 1 + (-547576713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4066204497/10000000000 : ℝ)^73 ≤ (15792756819487/50000000000000 : ℝ)^57 := by
    have hnat : (4066204497 : ℕ)^73*50000000000000^57 ≤ 15792756819487^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4066204497 10000000000 15792756819487 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1807145199/2500000000 : ℝ)^73 ≤ (16497912246841/25000000000000 : ℝ)^57 := by
    have hnat : (1807145199 : ℕ)^73*25000000000000^57 ≤ 16497912246841^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807145199 2500000000 16497912246841 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547576713/10000000000 : ℝ)^73 ≤ (484567470399/20000000000000 : ℝ)^57 := by
    have hnat : (547576713 : ℕ)^73*20000000000000^57 ≤ 484567470399^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547576713 10000000000 484567470399 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4066204497/10000000000 : ℝ), (1807145199/2500000000 : ℝ), (-547576713/10000000000 : ℝ)] ![(15792756819487/50000000000000 : ℝ), (16497912246841/25000000000000 : ℝ), (484567470399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4066204497/10000000000 : ℝ)|^73 ≤ (15792756819487/50000000000000 : ℝ)^57
        have hw : |(4066204497/10000000000 : ℝ)|=(4066204497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1807145199/2500000000 : ℝ)|^73 ≤ (16497912246841/25000000000000 : ℝ)^57
        have hw : |(1807145199/2500000000 : ℝ)|=(1807145199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547576713/10000000000 : ℝ)|^73 ≤ (484567470399/20000000000000 : ℝ)^57
        have hw : |(-547576713/10000000000 : ℝ)|=(547576713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2041218023/2500000000 : ℝ)*x 0 + (1816939631/10000000000 : ℝ)*x 1 + (465334901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041218023/2500000000 : ℝ)^73 ≤ (77131792402189/100000000000000 : ℝ)^57 := by
    have hnat : (2041218023 : ℕ)^73*100000000000000^57 ≤ 77131792402189^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041218023 2500000000 77131792402189 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1816939631/10000000000 : ℝ)^73 ≤ (1407168449669/12500000000000 : ℝ)^57 := by
    have hnat : (1816939631 : ℕ)^73*12500000000000^57 ≤ 1407168449669^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816939631 10000000000 1407168449669 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465334901/2500000000 : ℝ)^73 ≤ (2902714996301/25000000000000 : ℝ)^57 := by
    have hnat : (465334901 : ℕ)^73*25000000000000^57 ≤ 2902714996301^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465334901 2500000000 2902714996301 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2041218023/2500000000 : ℝ), (1816939631/10000000000 : ℝ), (465334901/2500000000 : ℝ)] ![(77131792402189/100000000000000 : ℝ), (1407168449669/12500000000000 : ℝ), (2902714996301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2041218023/2500000000 : ℝ)|^73 ≤ (77131792402189/100000000000000 : ℝ)^57
        have hw : |(2041218023/2500000000 : ℝ)|=(2041218023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1816939631/10000000000 : ℝ)|^73 ≤ (1407168449669/12500000000000 : ℝ)^57
        have hw : |(1816939631/10000000000 : ℝ)|=(1816939631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(465334901/2500000000 : ℝ)|^73 ≤ (2902714996301/25000000000000 : ℝ)^57
        have hw : |(465334901/2500000000 : ℝ)|=(465334901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312061_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((68561/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68561/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6981/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6981/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32457/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32457/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43551/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43551/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(50089/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45181/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45181/100000 : ℝ)*X 1 2) := by
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
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (68561/100000 : ℝ) ^ (9/2 : ℝ) ≤ (9147810291518035729/50000000000000000000 : ℝ) := by
    have hpowers : (68561/100000 : ℝ)^9 ≤ (9147810291518035729/50000000000000000000 : ℝ)^2 := by
      have hnat : (68561 : ℕ)^9*50000000000000000000^2 ≤ 9147810291518035729^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68561 100000 9147810291518035729 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68561/100000 : ℝ)) (X := (9147810291518035729/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (59147810291518035729/50000000000000000000 : ℝ) ≤ (1297553496560391/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (59147810291518035729/50000000000000000000 : ℝ)^2 ≤ (1297553496560391/1250000000000000 : ℝ)^9 := by
      have hnat : (59147810291518035729 : ℕ)^2*1250000000000000^9 ≤ 1297553496560391^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59147810291518035729 50000000000000000000 1297553496560391 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1297553496560391/1250000000000000 : ℝ)) (X := (59147810291518035729/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (34147810291518035729/25000000000000000000 : ℝ) ≤ (10717511716744401/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (34147810291518035729/25000000000000000000 : ℝ)^2 ≤ (10717511716744401/10000000000000000 : ℝ)^9 := by
      have hnat : (34147810291518035729 : ℕ)^2*10000000000000000^9 ≤ 10717511716744401^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34147810291518035729 25000000000000000000 10717511716744401 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10717511716744401/10000000000000000 : ℝ)) (X := (34147810291518035729/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(47553496560391/857012500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(337083744261273/6856100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (68561/100000 : ℝ)) (alpha := (47553496560391/857012500000000 : ℝ)) (beta := (337083744261273/6856100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68561/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(47553496560391/857012500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(337083744261273/6856100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (6981/10000 : ℝ) ^ (9/2 : ℝ) ≤ (793760279025162221/4000000000000000000 : ℝ) := by
    have hpowers : (6981/10000 : ℝ)^9 ≤ (793760279025162221/4000000000000000000 : ℝ)^2 := by
      have hnat : (6981 : ℕ)^9*4000000000000000000^2 ≤ 793760279025162221^2*10000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6981 10000 793760279025162221 4000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6981/10000 : ℝ)) (X := (793760279025162221/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (4793760279025162221/4000000000000000000 : ℝ) ≤ (5205234480027779/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (4793760279025162221/4000000000000000000 : ℝ)^2 ≤ (5205234480027779/5000000000000000 : ℝ)^9 := by
      have hnat : (4793760279025162221 : ℕ)^2*5000000000000000^9 ≤ 5205234480027779^9*4000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4793760279025162221 4000000000000000000 5205234480027779 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5205234480027779/5000000000000000 : ℝ)) (X := (4793760279025162221/4000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (2793760279025162221/2000000000000000000 : ℝ) ≤ (1346379840502237/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2793760279025162221/2000000000000000000 : ℝ)^2 ≤ (1346379840502237/1250000000000000 : ℝ)^9 := by
      have hnat : (2793760279025162221 : ℕ)^2*1250000000000000^9 ≤ 1346379840502237^9*2000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2793760279025162221 2000000000000000000 1346379840502237 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1346379840502237/1250000000000000 : ℝ)) (X := (2793760279025162221/2000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(68411493342593/1163500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(180284881981169/3490500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (6981/10000 : ℝ)) (alpha := (68411493342593/1163500000000000 : ℝ)) (beta := (180284881981169/3490500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6981/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(68411493342593/1163500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(180284881981169/3490500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (32457/50000 : ℝ) ^ (9/2 : ℝ) ≤ (14306146573677849473/100000000000000000000 : ℝ) := by
    have hpowers : (32457/50000 : ℝ)^9 ≤ (14306146573677849473/100000000000000000000 : ℝ)^2 := by
      have hnat : (32457 : ℕ)^9*100000000000000000000^2 ≤ 14306146573677849473^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32457 50000 14306146573677849473 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32457/50000 : ℝ)) (X := (14306146573677849473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (114306146573677849473/100000000000000000000 : ℝ) ≤ (10301592157599227/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (114306146573677849473/100000000000000000000 : ℝ)^2 ≤ (10301592157599227/10000000000000000 : ℝ)^9 := by
      have hnat : (114306146573677849473 : ℕ)^2*10000000000000000^9 ≤ 10301592157599227^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114306146573677849473 100000000000000000000 10301592157599227 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10301592157599227/10000000000000000 : ℝ)) (X := (114306146573677849473/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (64306146573677849473/50000000000000000000 : ℝ) ≤ (2643778123569011/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (64306146573677849473/50000000000000000000 : ℝ)^2 ≤ (2643778123569011/2500000000000000 : ℝ)^9 := by
      have hnat : (64306146573677849473 : ℕ)^2*2500000000000000^9 ≤ 2643778123569011^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64306146573677849473 50000000000000000000 2643778123569011 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2643778123569011/2500000000000000 : ℝ)) (X := (64306146573677849473/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(301592157599227/6491400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(91173445558939/2163800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (32457/50000 : ℝ)) (alpha := (301592157599227/6491400000000000 : ℝ)) (beta := (91173445558939/2163800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (32457/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(301592157599227/6491400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(91173445558939/2163800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1912869761/10000000000 : ℝ)*X 0 0+(2267610277/5000000000 : ℝ)*X 0 1+(2984936981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((941557893/2000000000 : ℝ)*X 1 0+(-971461631/5000000000 : ℝ)*X 1 1+(2893297213/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2397288481/5000000000 : ℝ)*X 2 0+(1280932953/2000000000 : ℝ)*X 2 1+(-88434697/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6295865961/10000000000 : ℝ)*X 0 0+(2813535417/10000000000 : ℝ)*X 0 1+(3387747169/10000000000 : ℝ)*X 0 2+(6295865961/10000000000 : ℝ)*X 1 0+(2813535417/10000000000 : ℝ)*X 1 1+(3387747169/10000000000 : ℝ)*X 1 2+(6295865961/10000000000 : ℝ)*X 2 0+(2813535417/10000000000 : ℝ)*X 2 1+(3387747169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-909882463/5000000000 : ℝ)*X 0 0+(946728129/2500000000 : ℝ)*X 0 1+(3350428831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2094292329/5000000000 : ℝ)*X 1 0+(-1324419917/10000000000 : ℝ)*X 1 1+(6683120509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((855330937/2000000000 : ℝ)*X 2 0+(7235945557/10000000000 : ℝ)*X 2 1+(-86524773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((6011981043/10000000000 : ℝ)*X 0 0+(4511452741/10000000000 : ℝ)*X 0 1+(377012403/2000000000 : ℝ)*X 0 2+(6011981043/10000000000 : ℝ)*X 1 0+(4511452741/10000000000 : ℝ)*X 1 1+(377012403/2000000000 : ℝ)*X 1 2+(6011981043/10000000000 : ℝ)*X 2 0+(4511452741/10000000000 : ℝ)*X 2 1+(377012403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-798826189/10000000000 : ℝ)*X 0 0+(113298181/250000000 : ℝ)*X 0 1+(334575827/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4186409303/10000000000 : ℝ)*X 1 0+(-1342101417/10000000000 : ℝ)*X 1 1+(6673780223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3003933351/5000000000 : ℝ)*X 2 0+(5607249587/10000000000 : ℝ)*X 2 1+(-23966267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7677870381/10000000000 : ℝ)*X 0 0+(1238057747/5000000000 : ℝ)*X 0 1+(953451/5000000 : ℝ)*X 0 2+(7677870381/10000000000 : ℝ)*X 1 0+(1238057747/5000000000 : ℝ)*X 1 1+(953451/5000000 : ℝ)*X 1 2+(7677870381/10000000000 : ℝ)*X 2 0+(1238057747/5000000000 : ℝ)*X 2 1+(953451/5000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-353798339/5000000000 : ℝ)*X 0 0+(1108084273/2000000000 : ℝ)*X 0 1+(2896270803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1502756269/2500000000 : ℝ)*X 1 0+(-73063431/1000000000 : ℝ)*X 1 1+(1325901997/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4066204497/10000000000 : ℝ)*X 2 0+(1807145199/2500000000 : ℝ)*X 2 1+(-547576713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2041218023/2500000000 : ℝ)*X 0 0+(1816939631/10000000000 : ℝ)*X 0 1+(465334901/2500000000 : ℝ)*X 0 2+(2041218023/2500000000 : ℝ)*X 1 0+(1816939631/10000000000 : ℝ)*X 1 1+(465334901/2500000000 : ℝ)*X 1 2+(2041218023/2500000000 : ℝ)*X 2 0+(1816939631/10000000000 : ℝ)*X 2 1+(465334901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((43551/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43551/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3491146646177673523022061057759/431519728773250000000000000000000000 : ℝ) := by norm_num
    linear_combination (244253/100000000000 : ℝ)*(base19) + (42968772531/62500000000 : ℝ)*(base59) + (945191/1000000000000 : ℝ)*(base60) + (4376910425889/1000000000000 : ℝ)*(major_s2_0) + (4376910425889/1000000000000 : ℝ)*(major_s2_1) + (4376910425889/1000000000000 : ℝ)*(major_s2_2) + (40411889/1000000000000 : ℝ)*(sp_s2_0) + (14844483/500000000000 : ℝ)*(sp_s2_6) + (245260288137/40000000000 : ℝ)*(sp_s2_7) + (3064073064973/500000000000 : ℝ)*(sp_s2_8) + (6131451529077/1000000000000 : ℝ)*(sp_s2_9) + (262224085071/100000000000 : ℝ)*(sp_s2_13) + (1699521419/500000000000 : ℝ)*(sp_s2_15) + (96086237/1000000000000 : ℝ)*(sp_s2_23) + (655567634919/250000000000 : ℝ)*(f.failure) + (3065773807657/500000000000 : ℝ)*(f.sum) + (11663794689736142461/25175813000000000000000000000000 : ℝ)*base63 + (928028910899789/2163800000000000000000000000 : ℝ)*base65 + (460355951622453/1163500000000000000000000000 : ℝ)*base66 + (246340308104161/2163800000000000000000000000 : ℝ)*base69 + (22622273907873081809/29670458360000000000000000000000 : ℝ)*base71 + (2752030786431423/6856100000000000000000000000 : ℝ)*base72 + (469360057786323/1163500000000000000000000000 : ℝ)*base74 + (1747864649546369/3428050000000000000000000000 : ℝ)*base76 + (276856093566183019/39885361750000000000000000000000 : ℝ)*base78 + (10047/25000000000000000 : ℝ)*base87 + (10047/25000000000000000 : ℝ)*base89 + (10047/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(50089/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8031562698244991008383473449241/863039457546500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1101247/1000000000000 : ℝ)*(base19) + (139589/500000000000 : ℝ)*(base39) + (5874863/1000000000000 : ℝ)*(base53) + (109168107941/500000000000 : ℝ)*(base59) + (4118139938297/1000000000000 : ℝ)*(major_s2_0) + (4118139938297/1000000000000 : ℝ)*(major_s2_1) + (4118134063433/1000000000000 : ℝ)*(major_s2_2) + (2391029/500000000000 : ℝ)*(sp_s2_6) + (7034207/250000000000 : ℝ)*(sp_s2_7) + (576900537673/100000000000 : ℝ)*(sp_s2_14) + (5769032412311/1000000000000 : ℝ)*(sp_s2_15) + (5769039388421/1000000000000 : ℝ)*(sp_s2_16) + (38549157457/15625000000 : ℝ)*(sp_s2_20) + (17305363/200000000000 : ℝ)*(sp_s2_27) + (2467237386121/1000000000000 : ℝ)*(f.failure) + (5769039388421/1000000000000 : ℝ)*(f.sum) + (17621233695377025179/75527439000000000000000000000000 : ℝ)*base63 + (518969085650233/2163800000000000000000000000 : ℝ)*base65 + (1295534700042707/3490500000000000000000000000 : ℝ)*base66 + (2964481822493831/6491400000000000000000000000 : ℝ)*base69 + (14833825335059655779/148352291800000000000000000000000 : ℝ)*base70 + (84099422583931/6856100000000000000000000000 : ℝ)*base73 + (824849033904321/1163500000000000000000000000 : ℝ)*base75 + (937932337147029/1714025000000000000000000000 : ℝ)*base77 + (45482785221493269439/119656085250000000000000000000000 : ℝ)*base79 + (85527/100000000000000000 : ℝ)*base86 + (85527/100000000000000000 : ℝ)*base88 + (14473/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45181/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45181/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5170636506577814447145320867161/431519728773250000000000000000000000 : ℝ) := by norm_num
    linear_combination (6964617/500000000000 : ℝ)*(base11) + (493667/50000000000 : ℝ)*(base15) + (57945841927/250000000000 : ℝ)*(base40) + (255834836529/1000000000000 : ℝ)*(base59) + (1755709085917/500000000000 : ℝ)*(major_s2_0) + (1755709085917/500000000000 : ℝ)*(major_s2_1) + (1755709085917/500000000000 : ℝ)*(major_s2_2) + (1827179/1000000000000 : ℝ)*(sp_s2_1) + (138171/40000000000 : ℝ)*(sp_s2_2) + (64518187/1000000000000 : ℝ)*(sp_s2_9) + (1229769211811/250000000000 : ℝ)*(sp_s2_21) + (4919079075959/1000000000000 : ℝ)*(sp_s2_22) + (307438925251/62500000000 : ℝ)*(sp_s2_23) + (420748314611/200000000000 : ℝ)*(sp_s2_27) + (420748314611/200000000000 : ℝ)*(f.failure) + (2459545388239/500000000000 : ℝ)*(f.sum) + (9473423059211991199/37763719500000000000000000000000 : ℝ)*base63 + (44105541027413/1081900000000000000000000000 : ℝ)*base64 + (435524204336873/1745250000000000000000000000 : ℝ)*base67 + (1741324405828129/3245700000000000000000000000 : ℝ)*base69 + (3016315966420441103/14835229180000000000000000000000 : ℝ)*base71 + (796827606727289/3428050000000000000000000000 : ℝ)*base72 + (106951902883403/290875000000000000000000000 : ℝ)*base75 + (1243502785553501/3428050000000000000000000000 : ℝ)*base77 + (15017548197791902817/119656085250000000000000000000000 : ℝ)*base78 + (14157/20000000000000000 : ℝ)*base86 + (14157/20000000000000000 : ℝ)*base88 + (14157/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((68561/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68561/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6981/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6981/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32457/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32457/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43551/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43551/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(50089/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45181/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45181/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312061_s2 p hpa hpb X hX hprev1

#print axioms solution

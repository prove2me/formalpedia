-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314050_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:08.19731+00:00
-- url     : https://prove2.me/submissions/279fee7f-b1bb-4e0a-a52b-e647bcf3c366

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
theorem collision_support_c314050_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (881602577/2500000000 : ℝ)*x 0 + (-859516207/2500000000 : ℝ)*x 1 + (-5549581499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881602577/2500000000 : ℝ)^19 ≤ (26706784389727/100000000000000 : ℝ)^15 := by
    have hnat : (881602577 : ℕ)^19*100000000000000^15 ≤ 26706784389727^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881602577 2500000000 26706784389727 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859516207/2500000000 : ℝ)^19 ≤ (12931070580719/50000000000000 : ℝ)^15 := by
    have hnat : (859516207 : ℕ)^19*50000000000000^15 ≤ 12931070580719^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859516207 2500000000 12931070580719 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5549581499/10000000000 : ℝ)^19 ≤ (9486214886803/20000000000000 : ℝ)^15 := by
    have hnat : (5549581499 : ℕ)^19*20000000000000^15 ≤ 9486214886803^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549581499 10000000000 9486214886803 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(881602577/2500000000 : ℝ), (-859516207/2500000000 : ℝ), (-5549581499/10000000000 : ℝ)] ![(26706784389727/100000000000000 : ℝ), (12931070580719/50000000000000 : ℝ), (9486214886803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(881602577/2500000000 : ℝ)|^19 ≤ (26706784389727/100000000000000 : ℝ)^15
        have hw : |(881602577/2500000000 : ℝ)|=(881602577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-859516207/2500000000 : ℝ)|^19 ≤ (12931070580719/50000000000000 : ℝ)^15
        have hw : |(-859516207/2500000000 : ℝ)|=(859516207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5549581499/10000000000 : ℝ)|^19 ≤ (9486214886803/20000000000000 : ℝ)^15
        have hw : |(-5549581499/10000000000 : ℝ)|=(5549581499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (305357163/500000000 : ℝ)*x 0 + (4939605709/10000000000 : ℝ)*x 1 + (1016757137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (305357163/500000000 : ℝ)^19 ≤ (1338653810081/2500000000000 : ℝ)^15 := by
    have hnat : (305357163 : ℕ)^19*2500000000000^15 ≤ 1338653810081^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305357163 500000000 1338653810081 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4939605709/10000000000 : ℝ)^19 ≤ (20463514832163/50000000000000 : ℝ)^15 := by
    have hnat : (4939605709 : ℕ)^19*50000000000000^15 ≤ 20463514832163^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939605709 10000000000 20463514832163 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016757137/10000000000 : ℝ)^19 ≤ (1381704481213/25000000000000 : ℝ)^15 := by
    have hnat : (1016757137 : ℕ)^19*25000000000000^15 ≤ 1381704481213^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016757137 10000000000 1381704481213 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(305357163/500000000 : ℝ), (4939605709/10000000000 : ℝ), (1016757137/10000000000 : ℝ)] ![(1338653810081/2500000000000 : ℝ), (20463514832163/50000000000000 : ℝ), (1381704481213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(305357163/500000000 : ℝ)|^19 ≤ (1338653810081/2500000000000 : ℝ)^15
        have hw : |(305357163/500000000 : ℝ)|=(305357163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4939605709/10000000000 : ℝ)|^19 ≤ (20463514832163/50000000000000 : ℝ)^15
        have hw : |(4939605709/10000000000 : ℝ)|=(4939605709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016757137/10000000000 : ℝ)|^19 ≤ (1381704481213/25000000000000 : ℝ)^15
        have hw : |(1016757137/10000000000 : ℝ)|=(1016757137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3381455109/10000000000 : ℝ)*x 0 + (3313311099/5000000000 : ℝ)*x 1 + (-2271210847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3381455109/10000000000 : ℝ)^19 ≤ (5064787814017/20000000000000 : ℝ)^15 := by
    have hnat : (3381455109 : ℕ)^19*20000000000000^15 ≤ 5064787814017^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3381455109 10000000000 5064787814017 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3313311099/5000000000 : ℝ)^19 ≤ (59379536126893/100000000000000 : ℝ)^15 := by
    have hnat : (3313311099 : ℕ)^19*100000000000000^15 ≤ 59379536126893^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3313311099 5000000000 59379536126893 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271210847/10000000000 : ℝ)^19 ≤ (7648262390727/50000000000000 : ℝ)^15 := by
    have hnat : (2271210847 : ℕ)^19*50000000000000^15 ≤ 7648262390727^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271210847 10000000000 7648262390727 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3381455109/10000000000 : ℝ), (3313311099/5000000000 : ℝ), (-2271210847/10000000000 : ℝ)] ![(5064787814017/20000000000000 : ℝ), (59379536126893/100000000000000 : ℝ), (7648262390727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3381455109/10000000000 : ℝ)|^19 ≤ (5064787814017/20000000000000 : ℝ)^15
        have hw : |(3381455109/10000000000 : ℝ)|=(3381455109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3313311099/5000000000 : ℝ)|^19 ≤ (59379536126893/100000000000000 : ℝ)^15
        have hw : |(3313311099/5000000000 : ℝ)|=(3313311099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271210847/10000000000 : ℝ)|^19 ≤ (7648262390727/50000000000000 : ℝ)^15
        have hw : |(-2271210847/10000000000 : ℝ)|=(2271210847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1305351973/5000000000 : ℝ)*x 0 + (2329831283/10000000000 : ℝ)*x 1 + (-7199321053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305351973/5000000000 : ℝ)^19 ≤ (2281058055797/12500000000000 : ℝ)^15 := by
    have hnat : (1305351973 : ℕ)^19*12500000000000^15 ≤ 2281058055797^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305351973 5000000000 2281058055797 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2329831283/10000000000 : ℝ)^19 ≤ (7899161671593/50000000000000 : ℝ)^15 := by
    have hnat : (2329831283 : ℕ)^19*50000000000000^15 ≤ 7899161671593^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329831283 10000000000 7899161671593 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7199321053/10000000000 : ℝ)^19 ≤ (65953212193761/100000000000000 : ℝ)^15 := by
    have hnat : (7199321053 : ℕ)^19*100000000000000^15 ≤ 65953212193761^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7199321053 10000000000 65953212193761 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1305351973/5000000000 : ℝ), (2329831283/10000000000 : ℝ), (-7199321053/10000000000 : ℝ)] ![(2281058055797/12500000000000 : ℝ), (7899161671593/50000000000000 : ℝ), (65953212193761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1305351973/5000000000 : ℝ)|^19 ≤ (2281058055797/12500000000000 : ℝ)^15
        have hw : |(-1305351973/5000000000 : ℝ)|=(1305351973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2329831283/10000000000 : ℝ)|^19 ≤ (7899161671593/50000000000000 : ℝ)^15
        have hw : |(2329831283/10000000000 : ℝ)|=(2329831283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7199321053/10000000000 : ℝ)|^19 ≤ (65953212193761/100000000000000 : ℝ)^15
        have hw : |(-7199321053/10000000000 : ℝ)|=(7199321053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (13276951/40000000 : ℝ)*x 0 + (-1404147201/5000000000 : ℝ)*x 1 + (-1252003319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13276951/40000000 : ℝ)^19 ≤ (24735190383441/100000000000000 : ℝ)^15 := by
    have hnat : (13276951 : ℕ)^19*100000000000000^15 ≤ 24735190383441^15*40000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13276951 40000000 24735190383441 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404147201/5000000000 : ℝ)^19 ≤ (10007616958523/50000000000000 : ℝ)^15 := by
    have hnat : (1404147201 : ℕ)^19*50000000000000^15 ≤ 10007616958523^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404147201 5000000000 10007616958523 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252003319/2000000000 : ℝ)^19 ≤ (13812393922469/25000000000000 : ℝ)^15 := by
    have hnat : (1252003319 : ℕ)^19*25000000000000^15 ≤ 13812393922469^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252003319 2000000000 13812393922469 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13276951/40000000 : ℝ), (-1404147201/5000000000 : ℝ), (-1252003319/2000000000 : ℝ)] ![(24735190383441/100000000000000 : ℝ), (10007616958523/50000000000000 : ℝ), (13812393922469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13276951/40000000 : ℝ)|^19 ≤ (24735190383441/100000000000000 : ℝ)^15
        have hw : |(13276951/40000000 : ℝ)|=(13276951/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1404147201/5000000000 : ℝ)|^19 ≤ (10007616958523/50000000000000 : ℝ)^15
        have hw : |(-1404147201/5000000000 : ℝ)|=(1404147201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1252003319/2000000000 : ℝ)|^19 ≤ (13812393922469/25000000000000 : ℝ)^15
        have hw : |(-1252003319/2000000000 : ℝ)|=(1252003319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (585459579/1000000000 : ℝ)*x 0 + (5576883391/10000000000 : ℝ)*x 1 + (366220773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (585459579/1000000000 : ℝ)^19 ≤ (50757017366453/100000000000000 : ℝ)^15 := by
    have hnat : (585459579 : ℕ)^19*100000000000000^15 ≤ 50757017366453^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585459579 1000000000 50757017366453 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5576883391/10000000000 : ℝ)^19 ≤ (23863418176707/50000000000000 : ℝ)^15 := by
    have hnat : (5576883391 : ℕ)^19*50000000000000^15 ≤ 23863418176707^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576883391 10000000000 23863418176707 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366220773/10000000000 : ℝ)^19 ≤ (758073134701/50000000000000 : ℝ)^15 := by
    have hnat : (366220773 : ℕ)^19*50000000000000^15 ≤ 758073134701^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366220773 10000000000 758073134701 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(585459579/1000000000 : ℝ), (5576883391/10000000000 : ℝ), (366220773/10000000000 : ℝ)] ![(50757017366453/100000000000000 : ℝ), (23863418176707/50000000000000 : ℝ), (758073134701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(585459579/1000000000 : ℝ)|^19 ≤ (50757017366453/100000000000000 : ℝ)^15
        have hw : |(585459579/1000000000 : ℝ)|=(585459579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5576883391/10000000000 : ℝ)|^19 ≤ (23863418176707/50000000000000 : ℝ)^15
        have hw : |(5576883391/10000000000 : ℝ)|=(5576883391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(366220773/10000000000 : ℝ)|^19 ≤ (758073134701/50000000000000 : ℝ)^15
        have hw : |(366220773/10000000000 : ℝ)|=(366220773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (656196697/2500000000 : ℝ)*x 0 + (4127198357/5000000000 : ℝ)*x 1 + (-132072133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656196697/2500000000 : ℝ)^19 ≤ (18373241057497/100000000000000 : ℝ)^15 := by
    have hnat : (656196697 : ℕ)^19*100000000000000^15 ≤ 18373241057497^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656196697 2500000000 18373241057497 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127198357/5000000000 : ℝ)^19 ≤ (78427449965809/100000000000000 : ℝ)^15 := by
    have hnat : (4127198357 : ℕ)^19*100000000000000^15 ≤ 78427449965809^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127198357 5000000000 78427449965809 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132072133/2000000000 : ℝ)^19 ≤ (799827239191/25000000000000 : ℝ)^15 := by
    have hnat : (132072133 : ℕ)^19*25000000000000^15 ≤ 799827239191^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132072133 2000000000 799827239191 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656196697/2500000000 : ℝ), (4127198357/5000000000 : ℝ), (-132072133/2000000000 : ℝ)] ![(18373241057497/100000000000000 : ℝ), (78427449965809/100000000000000 : ℝ), (799827239191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656196697/2500000000 : ℝ)|^19 ≤ (18373241057497/100000000000000 : ℝ)^15
        have hw : |(656196697/2500000000 : ℝ)|=(656196697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127198357/5000000000 : ℝ)|^19 ≤ (78427449965809/100000000000000 : ℝ)^15
        have hw : |(4127198357/5000000000 : ℝ)|=(4127198357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132072133/2000000000 : ℝ)|^19 ≤ (799827239191/25000000000000 : ℝ)^15
        have hw : |(-132072133/2000000000 : ℝ)|=(132072133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-58890429/250000000 : ℝ)*x 0 + (129598193/500000000 : ℝ)*x 1 + (-71944911/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58890429/250000000 : ℝ)^19 ≤ (8010063694759/50000000000000 : ℝ)^15 := by
    have hnat : (58890429 : ℕ)^19*50000000000000^15 ≤ 8010063694759^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58890429 250000000 8010063694759 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129598193/500000000 : ℝ)^19 ≤ (9041351022161/50000000000000 : ℝ)^15 := by
    have hnat : (129598193 : ℕ)^19*50000000000000^15 ≤ 9041351022161^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129598193 500000000 9041351022161 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71944911/100000000 : ℝ)^19 ≤ (65897170558279/100000000000000 : ℝ)^15 := by
    have hnat : (71944911 : ℕ)^19*100000000000000^15 ≤ 65897170558279^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71944911 100000000 65897170558279 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58890429/250000000 : ℝ), (129598193/500000000 : ℝ), (-71944911/100000000 : ℝ)] ![(8010063694759/50000000000000 : ℝ), (9041351022161/50000000000000 : ℝ), (65897170558279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58890429/250000000 : ℝ)|^19 ≤ (8010063694759/50000000000000 : ℝ)^15
        have hw : |(-58890429/250000000 : ℝ)|=(58890429/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129598193/500000000 : ℝ)|^19 ≤ (9041351022161/50000000000000 : ℝ)^15
        have hw : |(129598193/500000000 : ℝ)|=(129598193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71944911/100000000 : ℝ)|^19 ≤ (65897170558279/100000000000000 : ℝ)^15
        have hw : |(-71944911/100000000 : ℝ)|=(71944911/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2891810759/10000000000 : ℝ)*x 0 + (-202783869/625000000 : ℝ)*x 1 + (-6255186989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2891810759/10000000000 : ℝ)^19 ≤ (20772168377933/100000000000000 : ℝ)^15 := by
    have hnat : (2891810759 : ℕ)^19*100000000000000^15 ≤ 20772168377933^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891810759 10000000000 20772168377933 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202783869/625000000 : ℝ)^19 ≤ (24032242126243/100000000000000 : ℝ)^15 := by
    have hnat : (202783869 : ℕ)^19*100000000000000^15 ≤ 24032242126243^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202783869 625000000 24032242126243 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6255186989/10000000000 : ℝ)^19 ≤ (13798897370531/25000000000000 : ℝ)^15 := by
    have hnat : (6255186989 : ℕ)^19*25000000000000^15 ≤ 13798897370531^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6255186989 10000000000 13798897370531 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2891810759/10000000000 : ℝ), (-202783869/625000000 : ℝ), (-6255186989/10000000000 : ℝ)] ![(20772168377933/100000000000000 : ℝ), (24032242126243/100000000000000 : ℝ), (13798897370531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2891810759/10000000000 : ℝ)|^19 ≤ (20772168377933/100000000000000 : ℝ)^15
        have hw : |(2891810759/10000000000 : ℝ)|=(2891810759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-202783869/625000000 : ℝ)|^19 ≤ (24032242126243/100000000000000 : ℝ)^15
        have hw : |(-202783869/625000000 : ℝ)|=(202783869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6255186989/10000000000 : ℝ)|^19 ≤ (13798897370531/25000000000000 : ℝ)^15
        have hw : |(-6255186989/10000000000 : ℝ)|=(6255186989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1352363133/2000000000 : ℝ)*x 0 + (576749591/1250000000 : ℝ)*x 1 + (185524743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352363133/2000000000 : ℝ)^19 ≤ (1903692955469/3125000000000 : ℝ)^15 := by
    have hnat : (1352363133 : ℕ)^19*3125000000000^15 ≤ 1903692955469^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352363133 2000000000 1903692955469 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576749591/1250000000 : ℝ)^19 ≤ (18770156563799/50000000000000 : ℝ)^15 := by
    have hnat : (576749591 : ℕ)^19*50000000000000^15 ≤ 18770156563799^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576749591 1250000000 18770156563799 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185524743/5000000000 : ℝ)^19 ≤ (154151228489/10000000000000 : ℝ)^15 := by
    have hnat : (185524743 : ℕ)^19*10000000000000^15 ≤ 154151228489^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185524743 5000000000 154151228489 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352363133/2000000000 : ℝ), (576749591/1250000000 : ℝ), (185524743/5000000000 : ℝ)] ![(1903692955469/3125000000000 : ℝ), (18770156563799/50000000000000 : ℝ), (154151228489/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352363133/2000000000 : ℝ)|^19 ≤ (1903692955469/3125000000000 : ℝ)^15
        have hw : |(1352363133/2000000000 : ℝ)|=(1352363133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(576749591/1250000000 : ℝ)|^19 ≤ (18770156563799/50000000000000 : ℝ)^15
        have hw : |(576749591/1250000000 : ℝ)|=(576749591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185524743/5000000000 : ℝ)|^19 ≤ (154151228489/10000000000000 : ℝ)^15
        have hw : |(185524743/5000000000 : ℝ)|=(185524743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2547334529/5000000000 : ℝ)*x 0 + (6162976747/10000000000 : ℝ)*x 1 + (-672152309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2547334529/5000000000 : ℝ)^19 ≤ (42561171389499/100000000000000 : ℝ)^15 := by
    have hnat : (2547334529 : ℕ)^19*100000000000000^15 ≤ 42561171389499^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547334529 5000000000 42561171389499 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6162976747/10000000000 : ℝ)^19 ≤ (54166985914721/100000000000000 : ℝ)^15 := by
    have hnat : (6162976747 : ℕ)^19*100000000000000^15 ≤ 54166985914721^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6162976747 10000000000 54166985914721 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672152309/10000000000 : ℝ)^19 ≤ (1635921340701/50000000000000 : ℝ)^15 := by
    have hnat : (672152309 : ℕ)^19*50000000000000^15 ≤ 1635921340701^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672152309 10000000000 1635921340701 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2547334529/5000000000 : ℝ), (6162976747/10000000000 : ℝ), (-672152309/10000000000 : ℝ)] ![(42561171389499/100000000000000 : ℝ), (54166985914721/100000000000000 : ℝ), (1635921340701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2547334529/5000000000 : ℝ)|^19 ≤ (42561171389499/100000000000000 : ℝ)^15
        have hw : |(2547334529/5000000000 : ℝ)|=(2547334529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6162976747/10000000000 : ℝ)|^19 ≤ (54166985914721/100000000000000 : ℝ)^15
        have hw : |(6162976747/10000000000 : ℝ)|=(6162976747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-672152309/10000000000 : ℝ)|^19 ≤ (1635921340701/50000000000000 : ℝ)^15
        have hw : |(-672152309/10000000000 : ℝ)|=(672152309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2983369169/10000000000 : ℝ)*x 0 + (587292657/2000000000 : ℝ)*x 1 + (-6434910973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2983369169/10000000000 : ℝ)^19 ≤ (4321742220467/20000000000000 : ℝ)^15 := by
    have hnat : (2983369169 : ℕ)^19*20000000000000^15 ≤ 4321742220467^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983369169 10000000000 4321742220467 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (587292657/2000000000 : ℝ)^19 ≤ (1323704806699/6250000000000 : ℝ)^15 := by
    have hnat : (587292657 : ℕ)^19*6250000000000^15 ≤ 1323704806699^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587292657 2000000000 1323704806699 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6434910973/10000000000 : ℝ)^19 ≤ (14303002994817/25000000000000 : ℝ)^15 := by
    have hnat : (6434910973 : ℕ)^19*25000000000000^15 ≤ 14303002994817^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6434910973 10000000000 14303002994817 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2983369169/10000000000 : ℝ), (587292657/2000000000 : ℝ), (-6434910973/10000000000 : ℝ)] ![(4321742220467/20000000000000 : ℝ), (1323704806699/6250000000000 : ℝ), (14303002994817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2983369169/10000000000 : ℝ)|^19 ≤ (4321742220467/20000000000000 : ℝ)^15
        have hw : |(-2983369169/10000000000 : ℝ)|=(2983369169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(587292657/2000000000 : ℝ)|^19 ≤ (1323704806699/6250000000000 : ℝ)^15
        have hw : |(587292657/2000000000 : ℝ)|=(587292657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6434910973/10000000000 : ℝ)|^19 ≤ (14303002994817/25000000000000 : ℝ)^15
        have hw : |(-6434910973/10000000000 : ℝ)|=(6434910973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (891190921/2500000000 : ℝ)*x 0 + (-1730311031/5000000000 : ℝ)*x 1 + (-2747803161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891190921/2500000000 : ℝ)^19 ≤ (13537618808491/50000000000000 : ℝ)^15 := by
    have hnat : (891190921 : ℕ)^19*50000000000000^15 ≤ 13537618808491^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891190921 2500000000 13537618808491 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730311031/5000000000 : ℝ)^19 ≤ (13038629828569/50000000000000 : ℝ)^15 := by
    have hnat : (1730311031 : ℕ)^19*50000000000000^15 ≤ 13038629828569^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730311031 5000000000 13038629828569 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747803161/5000000000 : ℝ)^19 ≤ (46847502708767/100000000000000 : ℝ)^15 := by
    have hnat : (2747803161 : ℕ)^19*100000000000000^15 ≤ 46847502708767^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747803161 5000000000 46847502708767 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891190921/2500000000 : ℝ), (-1730311031/5000000000 : ℝ), (-2747803161/5000000000 : ℝ)] ![(13537618808491/50000000000000 : ℝ), (13038629828569/50000000000000 : ℝ), (46847502708767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891190921/2500000000 : ℝ)|^19 ≤ (13537618808491/50000000000000 : ℝ)^15
        have hw : |(891190921/2500000000 : ℝ)|=(891190921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1730311031/5000000000 : ℝ)|^19 ≤ (13038629828569/50000000000000 : ℝ)^15
        have hw : |(-1730311031/5000000000 : ℝ)|=(1730311031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2747803161/5000000000 : ℝ)|^19 ≤ (46847502708767/100000000000000 : ℝ)^15
        have hw : |(-2747803161/5000000000 : ℝ)|=(2747803161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (885962301/1250000000 : ℝ)*x 0 + (4078782133/10000000000 : ℝ)*x 1 + (166218221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (885962301/1250000000 : ℝ)^19 ≤ (4041289612651/6250000000000 : ℝ)^15 := by
    have hnat : (885962301 : ℕ)^19*6250000000000^15 ≤ 4041289612651^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885962301 1250000000 4041289612651 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4078782133/10000000000 : ℝ)^19 ≤ (4014042718807/12500000000000 : ℝ)^15 := by
    have hnat : (4078782133 : ℕ)^19*12500000000000^15 ≤ 4014042718807^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078782133 10000000000 4014042718807 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166218221/2500000000 : ℝ)^19 ≤ (806756107971/25000000000000 : ℝ)^15 := by
    have hnat : (166218221 : ℕ)^19*25000000000000^15 ≤ 806756107971^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166218221 2500000000 806756107971 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(885962301/1250000000 : ℝ), (4078782133/10000000000 : ℝ), (166218221/2500000000 : ℝ)] ![(4041289612651/6250000000000 : ℝ), (4014042718807/12500000000000 : ℝ), (806756107971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(885962301/1250000000 : ℝ)|^19 ≤ (4041289612651/6250000000000 : ℝ)^15
        have hw : |(885962301/1250000000 : ℝ)|=(885962301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4078782133/10000000000 : ℝ)|^19 ≤ (4014042718807/12500000000000 : ℝ)^15
        have hw : |(4078782133/10000000000 : ℝ)|=(4078782133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166218221/2500000000 : ℝ)|^19 ≤ (806756107971/25000000000000 : ℝ)^15
        have hw : |(166218221/2500000000 : ℝ)|=(166218221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314050_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1123554783/10000000000 : ℝ)*x 0 + (8838226631/10000000000 : ℝ)*x 1 + (-694742077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123554783/10000000000 : ℝ)^19 ≤ (1568048154451/25000000000000 : ℝ)^15 := by
    have hnat : (1123554783 : ℕ)^19*25000000000000^15 ≤ 1568048154451^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123554783 10000000000 1568048154451 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8838226631/10000000000 : ℝ)^19 ≤ (1336234032483/1562500000000 : ℝ)^15 := by
    have hnat : (8838226631 : ℕ)^19*1562500000000^15 ≤ 1336234032483^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8838226631 10000000000 1336234032483 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694742077/5000000000 : ℝ)^19 ≤ (1641765859351/20000000000000 : ℝ)^15 := by
    have hnat : (694742077 : ℕ)^19*20000000000000^15 ≤ 1641765859351^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694742077 5000000000 1641765859351 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123554783/10000000000 : ℝ), (8838226631/10000000000 : ℝ), (-694742077/5000000000 : ℝ)] ![(1568048154451/25000000000000 : ℝ), (1336234032483/1562500000000 : ℝ), (1641765859351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123554783/10000000000 : ℝ)|^19 ≤ (1568048154451/25000000000000 : ℝ)^15
        have hw : |(1123554783/10000000000 : ℝ)|=(1123554783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8838226631/10000000000 : ℝ)|^19 ≤ (1336234032483/1562500000000 : ℝ)^15
        have hw : |(8838226631/10000000000 : ℝ)|=(8838226631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-694742077/5000000000 : ℝ)|^19 ≤ (1641765859351/20000000000000 : ℝ)^15
        have hw : |(-694742077/5000000000 : ℝ)|=(694742077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314050_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((20533/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20533/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75521/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75521/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-13781/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-13781/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3069/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3069/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43099/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43099/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5081/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5081/20000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (20533/25000 : ℝ) ^ (37/8 : ℝ) ≤ (4023646726649419983/10000000000000000000 : ℝ) := by
    have hpowers : (20533/25000 : ℝ)^37 ≤ (4023646726649419983/10000000000000000000 : ℝ)^8 := by
      have hnat : (20533 : ℕ)^37*10000000000000000000^8 ≤ 4023646726649419983^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20533 25000 4023646726649419983 10000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20533/25000 : ℝ)) (X := (4023646726649419983/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (14023646726649419983/10000000000000000000 : ℝ) ≤ (5379274741292879/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (14023646726649419983/10000000000000000000 : ℝ)^8 ≤ (5379274741292879/5000000000000000 : ℝ)^37 := by
      have hnat : (14023646726649419983 : ℕ)^8*5000000000000000^37 ≤ 5379274741292879^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14023646726649419983 10000000000000000000 5379274741292879 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5379274741292879/5000000000000000 : ℝ)) (X := (14023646726649419983/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (9023646726649419983/5000000000000000000 : ℝ) ≤ (11361624969488513/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (9023646726649419983/5000000000000000000 : ℝ)^8 ≤ (11361624969488513/10000000000000000 : ℝ)^37 := by
      have hnat : (9023646726649419983 : ℕ)^8*10000000000000000^37 ≤ 11361624969488513^37*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9023646726649419983 5000000000000000000 11361624969488513 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11361624969488513/10000000000000000 : ℝ)) (X := (9023646726649419983/5000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(379274741292879/4106600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(120615097380551/1642640000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (20533/25000 : ℝ)) (alpha := (379274741292879/4106600000000000 : ℝ)) (beta := (120615097380551/1642640000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20533/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(379274741292879/4106600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(120615097380551/1642640000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75521/100000 : ℝ) ^ (37/8 : ℝ) ≤ (13646876606077794257/50000000000000000000 : ℝ) := by
    have hpowers : (75521/100000 : ℝ)^37 ≤ (13646876606077794257/50000000000000000000 : ℝ)^8 := by
      have hnat : (75521 : ℕ)^37*50000000000000000000^8 ≤ 13646876606077794257^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75521 100000 13646876606077794257 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75521/100000 : ℝ)) (X := (13646876606077794257/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (63646876606077794257/50000000000000000000 : ℝ) ≤ (5267820852934281/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (63646876606077794257/50000000000000000000 : ℝ)^8 ≤ (5267820852934281/5000000000000000 : ℝ)^37 := by
      have hnat : (63646876606077794257 : ℕ)^8*5000000000000000^37 ≤ 5267820852934281^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63646876606077794257 50000000000000000000 5267820852934281 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5267820852934281/5000000000000000 : ℝ)) (X := (63646876606077794257/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (38646876606077794257/25000000000000000000 : ℝ) ≤ (5493796591127013/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (38646876606077794257/25000000000000000000 : ℝ)^8 ≤ (5493796591127013/5000000000000000 : ℝ)^37 := by
      have hnat : (38646876606077794257 : ℕ)^8*5000000000000000^37 ≤ 5493796591127013^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38646876606077794257 25000000000000000000 5493796591127013 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5493796591127013/5000000000000000 : ℝ)) (X := (38646876606077794257/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(267820852934281/3776050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(56493934548183/944012500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (75521/100000 : ℝ)) (alpha := (267820852934281/3776050000000000 : ℝ)) (beta := (56493934548183/944012500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75521/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(267820852934281/3776050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(56493934548183/944012500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13781/20000 : ℝ) ^ (37/8 : ℝ) ≤ (17861159917102121209/100000000000000000000 : ℝ) := by
    have hpowers : (13781/20000 : ℝ)^37 ≤ (17861159917102121209/100000000000000000000 : ℝ)^8 := by
      have hnat : (13781 : ℕ)^37*100000000000000000000^8 ≤ 17861159917102121209^8*20000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13781 20000 17861159917102121209 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13781/20000 : ℝ)) (X := (17861159917102121209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (117861159917102121209/100000000000000000000 : ℝ) ≤ (518085585665697/500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (117861159917102121209/100000000000000000000 : ℝ)^8 ≤ (518085585665697/500000000000000 : ℝ)^37 := by
      have hnat : (117861159917102121209 : ℕ)^8*500000000000000^37 ≤ 518085585665697^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117861159917102121209 100000000000000000000 518085585665697 500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (518085585665697/500000000000000 : ℝ)) (X := (117861159917102121209/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (67861159917102121209/50000000000000000000 : ℝ) ≤ (5341353987580311/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (67861159917102121209/50000000000000000000 : ℝ)^8 ≤ (5341353987580311/5000000000000000 : ℝ)^37 := by
      have hnat : (67861159917102121209 : ℕ)^8*5000000000000000^37 ≤ 5341353987580311^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67861159917102121209 50000000000000000000 5341353987580311 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5341353987580311/5000000000000000 : ℝ)) (X := (67861159917102121209/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(18085585665697/344525000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(160498130923341/3445250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (13781/20000 : ℝ)) (alpha := (18085585665697/344525000000000 : ℝ)) (beta := (160498130923341/3445250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13781/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(18085585665697/344525000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(160498130923341/3445250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((881602577/2500000000 : ℝ)*X 1 0+(-859516207/2500000000 : ℝ)*X 1 1+(-5549581499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((305357163/500000000 : ℝ)*X 2 0+(4939605709/10000000000 : ℝ)*X 2 1+(1016757137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3381455109/10000000000 : ℝ)*X 0 0+(3313311099/5000000000 : ℝ)*X 0 1+(-2271210847/10000000000 : ℝ)*X 0 2+(3381455109/10000000000 : ℝ)*X 1 0+(3313311099/5000000000 : ℝ)*X 1 1+(-2271210847/10000000000 : ℝ)*X 1 2+(3381455109/10000000000 : ℝ)*X 2 0+(3313311099/5000000000 : ℝ)*X 2 1+(-2271210847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1305351973/5000000000 : ℝ)*X 0 0+(2329831283/10000000000 : ℝ)*X 0 1+(-7199321053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((13276951/40000000 : ℝ)*X 1 0+(-1404147201/5000000000 : ℝ)*X 1 1+(-1252003319/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((585459579/1000000000 : ℝ)*X 2 0+(5576883391/10000000000 : ℝ)*X 2 1+(366220773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((656196697/2500000000 : ℝ)*X 0 0+(4127198357/5000000000 : ℝ)*X 0 1+(-132072133/2000000000 : ℝ)*X 0 2+(656196697/2500000000 : ℝ)*X 1 0+(4127198357/5000000000 : ℝ)*X 1 1+(-132072133/2000000000 : ℝ)*X 1 2+(656196697/2500000000 : ℝ)*X 2 0+(4127198357/5000000000 : ℝ)*X 2 1+(-132072133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-58890429/250000000 : ℝ)*X 0 0+(129598193/500000000 : ℝ)*X 0 1+(-71944911/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2891810759/10000000000 : ℝ)*X 1 0+(-202783869/625000000 : ℝ)*X 1 1+(-6255186989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1352363133/2000000000 : ℝ)*X 2 0+(576749591/1250000000 : ℝ)*X 2 1+(185524743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2547334529/5000000000 : ℝ)*X 0 0+(6162976747/10000000000 : ℝ)*X 0 1+(-672152309/10000000000 : ℝ)*X 0 2+(2547334529/5000000000 : ℝ)*X 1 0+(6162976747/10000000000 : ℝ)*X 1 1+(-672152309/10000000000 : ℝ)*X 1 2+(2547334529/5000000000 : ℝ)*X 2 0+(6162976747/10000000000 : ℝ)*X 2 1+(-672152309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2983369169/10000000000 : ℝ)*X 0 0+(587292657/2000000000 : ℝ)*X 0 1+(-6434910973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((891190921/2500000000 : ℝ)*X 1 0+(-1730311031/5000000000 : ℝ)*X 1 1+(-2747803161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((885962301/1250000000 : ℝ)*X 2 0+(4078782133/10000000000 : ℝ)*X 2 1+(166218221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1123554783/10000000000 : ℝ)*X 0 0+(8838226631/10000000000 : ℝ)*X 0 1+(-694742077/5000000000 : ℝ)*X 0 2+(1123554783/10000000000 : ℝ)*X 1 0+(8838226631/10000000000 : ℝ)*X 1 1+(-694742077/5000000000 : ℝ)*X 1 2+(1123554783/10000000000 : ℝ)*X 2 0+(8838226631/10000000000 : ℝ)*X 2 1+(-694742077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314050_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3069/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3069/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (264647116329844483280906261689587/21369820382233000000000000000000000000 : ℝ) := by norm_num
    linear_combination (318471/250000000000 : ℝ)*(base12) + (930949/250000000000 : ℝ)*(base59) + (264582600087/200000000000 : ℝ)*(base60) + (5598297122629/1000000000000 : ℝ)*(major_s1_0) + (5598297122629/1000000000000 : ℝ)*(major_s1_1) + (5598297122629/1000000000000 : ℝ)*(major_s1_2) + (18023759/500000000000 : ℝ)*(sp_s1_2) + (234549/500000000000 : ℝ)*(sp_s1_6) + (7943070125461/1000000000000 : ℝ)*(sp_s1_7) + (317719600897/40000000000 : ℝ)*(sp_s1_8) + (7943035351827/1000000000000 : ℝ)*(sp_s1_9) + (3253488604871/1000000000000 : ℝ)*(sp_s1_13) + (2034423/25000000000 : ℝ)*(sp_s1_15) + (29643887/1000000000000 : ℝ)*(sp_s1_27) + (3253518717857/1000000000000 : ℝ)*(f.failure) + (1588614279869/200000000000 : ℝ)*(f.sum) + (6245989949514483449/26018872525000000000000000000000 : ℝ)*base63 + (2855319094041039/3445250000000000000000000000 : ℝ)*base65 + (78471750697873/236003125000000000000000000 : ℝ)*base66 + (146104800986369/689050000000000000000000000 : ℝ)*base69 + (241833853772821908403/282965273000000000000000000000000 : ℝ)*base71 + (66200768842377/328528000000000000000000000 : ℝ)*base72 + (113830037111043/472006250000000000000000000 : ℝ)*base75 + (3130637006453651/4106600000000000000000000000 : ℝ)*base77 + (64475714274851326657/620269077200000000000000000000000 : ℝ)*base78 + (36133/100000000000000000 : ℝ)*base87 + (36133/100000000000000000 : ℝ)*base89 + (36133/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43099/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43099/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (267872350453917348613678388685399/21369820382233000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9271829/1000000000000 : ℝ)*(base12) + (1305451/500000000000 : ℝ)*(base39) + (2607429/1000000000000 : ℝ)*(base59) + (261309500793/200000000000 : ℝ)*(base60) + (5418617940557/1000000000000 : ℝ)*(major_s1_0) + (5418617940557/1000000000000 : ℝ)*(major_s1_1) + (5418617940557/1000000000000 : ℝ)*(major_s1_2) + (4283877/500000000000 : ℝ)*(sp_s1_1) + (149999069/1000000000000 : ℝ)*(sp_s1_7) + (1921994116053/250000000000 : ℝ)*(sp_s1_14) + (7688127167357/1000000000000 : ℝ)*(sp_s1_15) + (3844005858531/500000000000 : ℝ)*(sp_s1_16) + (3149095967639/1000000000000 : ℝ)*(sp_s1_20) + (124018049/1000000000000 : ℝ)*(sp_s1_23) + (3149095967639/1000000000000 : ℝ)*(f.failure) + (7688135735111/1000000000000 : ℝ)*(f.sum) + (26420303723016591181/52037745050000000000000000000000 : ℝ)*base62 + (399643656773563/3445250000000000000000000000 : ℝ)*base64 + (44289652012881/59000781250000000000000000 : ℝ)*base66 + (288236134135043/689050000000000000000000000 : ℝ)*base68 + (57711338031970246501/282965273000000000000000000000000 : ℝ)*base70 + (519278025646187/1642640000000000000000000000 : ℝ)*base73 + (57588680085303/3776050000000000000000000000 : ℝ)*base74 + (239925827022843/4106600000000000000000000000 : ℝ)*base77 + (165572347501925429759/620269077200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (24909/100000000000000000 : ℝ)*base86 + (24909/100000000000000000 : ℝ)*base88 + (24909/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5081/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5081/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31940573616057880649562885567999/10684910191116500000000000000000000000 : ℝ) := by norm_num
    linear_combination (41403/250000000000 : ℝ)*(base8) + (23409/25000000000 : ℝ)*(base11) + (14063/20000000000 : ℝ)*(base50) + (223558231201/500000000000 : ℝ)*(base60) + (1922177722137/500000000000 : ℝ)*(major_s1_0) + (1922177722137/500000000000 : ℝ)*(major_s1_1) + (1922177722137/500000000000 : ℝ)*(major_s1_2) + (1079547/250000000000 : ℝ)*(sp_s1_2) + (16329881/1000000000000 : ℝ)*(sp_s1_13) + (4752191/250000000000 : ℝ)*(sp_s1_16) + (681814336387/125000000000 : ℝ)*(sp_s1_21) + (1363628948267/250000000000 : ℝ)*(sp_s1_22) + (1363623116529/250000000000 : ℝ)*(sp_s1_23) + (2234177769157/1000000000000 : ℝ)*(sp_s1_27) + (1117097049519/500000000000 : ℝ)*(f.failure) + (1363628948267/250000000000 : ℝ)*(f.sum) + (6655635995484302937/52037745050000000000000000000000 : ℝ)*base62 + (1460169957951591/3445250000000000000000000000 : ℝ)*base64 + (2354290094691713/3776050000000000000000000000 : ℝ)*base66 + (127651564683211/689050000000000000000000000 : ℝ)*base68 + (28210696142608016791/141482636500000000000000000000000 : ℝ)*base70 + (4858374622513/164264000000000000000000000 : ℝ)*base72 + (50268870699659/3776050000000000000000000000 : ℝ)*base75 + (307339149413133/2053300000000000000000000000 : ℝ)*base77 + (13202584392832619801/310134538600000000000000000000000 : ℝ)*base78 + (15189/50000000000000000 : ℝ)*base86 + (15189/50000000000000000 : ℝ)*base88 + (15189/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((20533/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20533/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75521/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75521/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-13781/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-13781/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3069/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3069/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43099/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43099/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5081/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5081/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314050_s1 p hpa hpb X hX hprev0

#print axioms solution

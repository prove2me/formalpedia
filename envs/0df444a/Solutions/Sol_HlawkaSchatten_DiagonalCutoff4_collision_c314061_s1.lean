-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:47:47.734993+00:00
-- url     : https://prove2.me/submissions/dd63a29f-1f32-4824-835d-ce6d8117d400

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
theorem collision_support_c314061_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-749053567/5000000000 : ℝ)*x 0 + (4609747701/10000000000 : ℝ)*x 1 + (3065017267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749053567/5000000000 : ℝ)^75 ≤ (4476424690229/50000000000000 : ℝ)^59 := by
    have hnat : (749053567 : ℕ)^75*50000000000000^59 ≤ 4476424690229^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749053567 5000000000 4476424690229 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4609747701/10000000000 : ℝ)^75 ≤ (1494620562519/4000000000000 : ℝ)^59 := by
    have hnat : (4609747701 : ℕ)^75*4000000000000^59 ≤ 1494620562519^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609747701 10000000000 1494620562519 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3065017267/5000000000 : ℝ)^75 ≤ (53681636534273/100000000000000 : ℝ)^59 := by
    have hnat : (3065017267 : ℕ)^75*100000000000000^59 ≤ 53681636534273^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3065017267 5000000000 53681636534273 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749053567/5000000000 : ℝ), (4609747701/10000000000 : ℝ), (3065017267/5000000000 : ℝ)] ![(4476424690229/50000000000000 : ℝ), (1494620562519/4000000000000 : ℝ), (53681636534273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749053567/5000000000 : ℝ)|^75 ≤ (4476424690229/50000000000000 : ℝ)^59
        have hw : |(-749053567/5000000000 : ℝ)|=(749053567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4609747701/10000000000 : ℝ)|^75 ≤ (1494620562519/4000000000000 : ℝ)^59
        have hw : |(4609747701/10000000000 : ℝ)|=(4609747701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3065017267/5000000000 : ℝ)|^75 ≤ (53681636534273/100000000000000 : ℝ)^59
        have hw : |(3065017267/5000000000 : ℝ)|=(3065017267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2374251063/5000000000 : ℝ)*x 0 + (-735903479/5000000000 : ℝ)*x 1 + (120374209/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2374251063/5000000000 : ℝ)^75 ≤ (38801023563553/100000000000000 : ℝ)^59 := by
    have hnat : (2374251063 : ℕ)^75*100000000000000^59 ≤ 38801023563553^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374251063 5000000000 38801023563553 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735903479/5000000000 : ℝ)^75 ≤ (8753531241737/100000000000000 : ℝ)^59 := by
    have hnat : (735903479 : ℕ)^75*100000000000000^59 ≤ 8753531241737^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735903479 5000000000 8753531241737 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120374209/200000000 : ℝ)^75 ≤ (26222722590483/50000000000000 : ℝ)^59 := by
    have hnat : (120374209 : ℕ)^75*50000000000000^59 ≤ 26222722590483^59*200000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120374209 200000000 26222722590483 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2374251063/5000000000 : ℝ), (-735903479/5000000000 : ℝ), (120374209/200000000 : ℝ)] ![(38801023563553/100000000000000 : ℝ), (8753531241737/100000000000000 : ℝ), (26222722590483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2374251063/5000000000 : ℝ)|^75 ≤ (38801023563553/100000000000000 : ℝ)^59
        have hw : |(2374251063/5000000000 : ℝ)|=(2374251063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735903479/5000000000 : ℝ)|^75 ≤ (8753531241737/100000000000000 : ℝ)^59
        have hw : |(-735903479/5000000000 : ℝ)|=(735903479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(120374209/200000000 : ℝ)|^75 ≤ (26222722590483/50000000000000 : ℝ)^59
        have hw : |(120374209/200000000 : ℝ)|=(120374209/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-925015093/5000000000 : ℝ)*x 0 + (1402601347/5000000000 : ℝ)*x 1 + (1854746747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925015093/5000000000 : ℝ)^75 ≤ (182922728909/1562500000000 : ℝ)^59 := by
    have hnat : (925015093 : ℕ)^75*1562500000000^59 ≤ 182922728909^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925015093 5000000000 182922728909 1562500000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402601347/5000000000 : ℝ)^75 ≤ (19872826292377/100000000000000 : ℝ)^59 := by
    have hnat : (1402601347 : ℕ)^75*100000000000000^59 ≤ 19872826292377^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402601347 5000000000 19872826292377 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1854746747/2500000000 : ℝ)^75 ≤ (17105029761313/25000000000000 : ℝ)^59 := by
    have hnat : (1854746747 : ℕ)^75*25000000000000^59 ≤ 17105029761313^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854746747 2500000000 17105029761313 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925015093/5000000000 : ℝ), (1402601347/5000000000 : ℝ), (1854746747/2500000000 : ℝ)] ![(182922728909/1562500000000 : ℝ), (19872826292377/100000000000000 : ℝ), (17105029761313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925015093/5000000000 : ℝ)|^75 ≤ (182922728909/1562500000000 : ℝ)^59
        have hw : |(-925015093/5000000000 : ℝ)|=(925015093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402601347/5000000000 : ℝ)|^75 ≤ (19872826292377/100000000000000 : ℝ)^59
        have hw : |(1402601347/5000000000 : ℝ)|=(1402601347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1854746747/2500000000 : ℝ)|^75 ≤ (17105029761313/25000000000000 : ℝ)^59
        have hw : |(1854746747/2500000000 : ℝ)|=(1854746747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (211493/625000 : ℝ)*x 0 + (-138166967/1250000000 : ℝ)*x 1 + (7442341107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211493/625000 : ℝ)^75 ≤ (25223187888617/100000000000000 : ℝ)^59 := by
    have hnat : (211493 : ℕ)^75*100000000000000^59 ≤ 25223187888617^59*625000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211493 625000 25223187888617 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138166967/1250000000 : ℝ)^75 ≤ (1520697456333/25000000000000 : ℝ)^59 := by
    have hnat : (138166967 : ℕ)^75*25000000000000^59 ≤ 1520697456333^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138166967 1250000000 1520697456333 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7442341107/10000000000 : ℝ)^75 ≤ (6869402227061/10000000000000 : ℝ)^59 := by
    have hnat : (7442341107 : ℕ)^75*10000000000000^59 ≤ 6869402227061^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7442341107 10000000000 6869402227061 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211493/625000 : ℝ), (-138166967/1250000000 : ℝ), (7442341107/10000000000 : ℝ)] ![(25223187888617/100000000000000 : ℝ), (1520697456333/25000000000000 : ℝ), (6869402227061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211493/625000 : ℝ)|^75 ≤ (25223187888617/100000000000000 : ℝ)^59
        have hw : |(211493/625000 : ℝ)|=(211493/625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138166967/1250000000 : ℝ)|^75 ≤ (1520697456333/25000000000000 : ℝ)^59
        have hw : |(-138166967/1250000000 : ℝ)|=(138166967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7442341107/10000000000 : ℝ)|^75 ≤ (6869402227061/10000000000000 : ℝ)^59
        have hw : |(7442341107/10000000000 : ℝ)|=(7442341107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3464182559/10000000000 : ℝ)*x 0 + (986479057/1250000000 : ℝ)*x 1 + (-1372371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3464182559/10000000000 : ℝ)^75 ≤ (12993218653147/50000000000000 : ℝ)^59 := by
    have hnat : (3464182559 : ℕ)^75*50000000000000^59 ≤ 12993218653147^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464182559 10000000000 12993218653147 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986479057/1250000000 : ℝ)^75 ≤ (578207759861/781250000000 : ℝ)^59 := by
    have hnat : (986479057 : ℕ)^75*781250000000^59 ≤ 578207759861^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986479057 1250000000 578207759861 781250000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372371/5000000000 : ℝ)^75 ≤ (371177333/12500000000000 : ℝ)^59 := by
    have hnat : (1372371 : ℕ)^75*12500000000000^59 ≤ 371177333^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372371 5000000000 371177333 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3464182559/10000000000 : ℝ), (986479057/1250000000 : ℝ), (-1372371/5000000000 : ℝ)] ![(12993218653147/50000000000000 : ℝ), (578207759861/781250000000 : ℝ), (371177333/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3464182559/10000000000 : ℝ)|^75 ≤ (12993218653147/50000000000000 : ℝ)^59
        have hw : |(3464182559/10000000000 : ℝ)|=(3464182559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(986479057/1250000000 : ℝ)|^75 ≤ (578207759861/781250000000 : ℝ)^59
        have hw : |(986479057/1250000000 : ℝ)|=(986479057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372371/5000000000 : ℝ)|^75 ≤ (371177333/12500000000000 : ℝ)^59
        have hw : |(-1372371/5000000000 : ℝ)|=(1372371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (17853881/39062500 : ℝ)*x 0 + (6040941743/10000000000 : ℝ)*x 1 + (1678581941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17853881/39062500 : ℝ)^75 ≤ (36962537747287/100000000000000 : ℝ)^59 := by
    have hnat : (17853881 : ℕ)^75*100000000000000^59 ≤ 36962537747287^59*39062500^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17853881 39062500 36962537747287 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6040941743/10000000000 : ℝ)^75 ≤ (10538363914287/20000000000000 : ℝ)^59 := by
    have hnat : (6040941743 : ℕ)^75*20000000000000^59 ≤ 10538363914287^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6040941743 10000000000 10538363914287 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678581941/10000000000 : ℝ)^75 ≤ (10345642673453/100000000000000 : ℝ)^59 := by
    have hnat : (1678581941 : ℕ)^75*100000000000000^59 ≤ 10345642673453^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678581941 10000000000 10345642673453 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17853881/39062500 : ℝ), (6040941743/10000000000 : ℝ), (1678581941/10000000000 : ℝ)] ![(36962537747287/100000000000000 : ℝ), (10538363914287/20000000000000 : ℝ), (10345642673453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17853881/39062500 : ℝ)|^75 ≤ (36962537747287/100000000000000 : ℝ)^59
        have hw : |(17853881/39062500 : ℝ)|=(17853881/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6040941743/10000000000 : ℝ)|^75 ≤ (10538363914287/20000000000000 : ℝ)^59
        have hw : |(6040941743/10000000000 : ℝ)|=(6040941743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1678581941/10000000000 : ℝ)|^75 ≤ (10345642673453/100000000000000 : ℝ)^59
        have hw : |(1678581941/10000000000 : ℝ)|=(1678581941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-393999301/5000000000 : ℝ)*x 0 + (3182744267/10000000000 : ℝ)*x 1 + (7782606321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393999301/5000000000 : ℝ)^75 ≤ (395619883383/10000000000000 : ℝ)^59 := by
    have hnat : (393999301 : ℕ)^75*10000000000000^59 ≤ 395619883383^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393999301 5000000000 395619883383 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3182744267/10000000000 : ℝ)^75 ≤ (4666575697267/20000000000000 : ℝ)^59 := by
    have hnat : (3182744267 : ℕ)^75*20000000000000^59 ≤ 4666575697267^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182744267 10000000000 4666575697267 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7782606321/10000000000 : ℝ)^75 ≤ (9088865333093/12500000000000 : ℝ)^59 := by
    have hnat : (7782606321 : ℕ)^75*12500000000000^59 ≤ 9088865333093^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7782606321 10000000000 9088865333093 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393999301/5000000000 : ℝ), (3182744267/10000000000 : ℝ), (7782606321/10000000000 : ℝ)] ![(395619883383/10000000000000 : ℝ), (4666575697267/20000000000000 : ℝ), (9088865333093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393999301/5000000000 : ℝ)|^75 ≤ (395619883383/10000000000000 : ℝ)^59
        have hw : |(-393999301/5000000000 : ℝ)|=(393999301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3182744267/10000000000 : ℝ)|^75 ≤ (4666575697267/20000000000000 : ℝ)^59
        have hw : |(3182744267/10000000000 : ℝ)|=(3182744267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7782606321/10000000000 : ℝ)|^75 ≤ (9088865333093/12500000000000 : ℝ)^59
        have hw : |(7782606321/10000000000 : ℝ)|=(7782606321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1235466493/5000000000 : ℝ)*x 0 + (-102820453/625000000 : ℝ)*x 1 + (487949563/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1235466493/5000000000 : ℝ)^75 ≤ (8456352889649/50000000000000 : ℝ)^59 := by
    have hnat : (1235466493 : ℕ)^75*50000000000000^59 ≤ 8456352889649^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235466493 5000000000 8456352889649 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102820453/625000000 : ℝ)^75 ≤ (1260530735659/12500000000000 : ℝ)^59 := by
    have hnat : (102820453 : ℕ)^75*12500000000000^59 ≤ 1260530735659^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102820453 625000000 1260530735659 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487949563/625000000 : ℝ)^75 ≤ (73003048327831/100000000000000 : ℝ)^59 := by
    have hnat : (487949563 : ℕ)^75*100000000000000^59 ≤ 73003048327831^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487949563 625000000 73003048327831 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1235466493/5000000000 : ℝ), (-102820453/625000000 : ℝ), (487949563/625000000 : ℝ)] ![(8456352889649/50000000000000 : ℝ), (1260530735659/12500000000000 : ℝ), (73003048327831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1235466493/5000000000 : ℝ)|^75 ≤ (8456352889649/50000000000000 : ℝ)^59
        have hw : |(1235466493/5000000000 : ℝ)|=(1235466493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102820453/625000000 : ℝ)|^75 ≤ (1260530735659/12500000000000 : ℝ)^59
        have hw : |(-102820453/625000000 : ℝ)|=(102820453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(487949563/625000000 : ℝ)|^75 ≤ (73003048327831/100000000000000 : ℝ)^59
        have hw : |(487949563/625000000 : ℝ)|=(487949563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3491219251/5000000000 : ℝ)*x 0 + (906979567/2000000000 : ℝ)*x 1 + (-29302451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3491219251/5000000000 : ℝ)^75 ≤ (12668755684749/20000000000000 : ℝ)^59 := by
    have hnat : (3491219251 : ℕ)^75*20000000000000^59 ≤ 12668755684749^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3491219251 5000000000 12668755684749 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906979567/2000000000 : ℝ)^75 ≤ (36595970781781/100000000000000 : ℝ)^59 := by
    have hnat : (906979567 : ℕ)^75*100000000000000^59 ≤ 36595970781781^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906979567 2000000000 36595970781781 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29302451/10000000000 : ℝ)^75 ≤ (15062694051/25000000000000 : ℝ)^59 := by
    have hnat : (29302451 : ℕ)^75*25000000000000^59 ≤ 15062694051^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29302451 10000000000 15062694051 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3491219251/5000000000 : ℝ), (906979567/2000000000 : ℝ), (-29302451/10000000000 : ℝ)] ![(12668755684749/20000000000000 : ℝ), (36595970781781/100000000000000 : ℝ), (15062694051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3491219251/5000000000 : ℝ)|^75 ≤ (12668755684749/20000000000000 : ℝ)^59
        have hw : |(3491219251/5000000000 : ℝ)|=(3491219251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906979567/2000000000 : ℝ)|^75 ≤ (36595970781781/100000000000000 : ℝ)^59
        have hw : |(906979567/2000000000 : ℝ)|=(906979567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29302451/10000000000 : ℝ)|^75 ≤ (15062694051/25000000000000 : ℝ)^59
        have hw : |(-29302451/10000000000 : ℝ)|=(29302451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8019623331/10000000000 : ℝ)*x 0 + (456190547/2000000000 : ℝ)*x 1 + (764314429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8019623331/10000000000 : ℝ)^75 ≤ (1888434107589/2500000000000 : ℝ)^59 := by
    have hnat : (8019623331 : ℕ)^75*2500000000000^59 ≤ 1888434107589^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8019623331 10000000000 1888434107589 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456190547/2000000000 : ℝ)^75 ≤ (7638641547709/50000000000000 : ℝ)^59 := by
    have hnat : (456190547 : ℕ)^75*50000000000000^59 ≤ 7638641547709^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456190547 2000000000 7638641547709 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764314429/5000000000 : ℝ)^75 ≤ (9185352582249/100000000000000 : ℝ)^59 := by
    have hnat : (764314429 : ℕ)^75*100000000000000^59 ≤ 9185352582249^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764314429 5000000000 9185352582249 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8019623331/10000000000 : ℝ), (456190547/2000000000 : ℝ), (764314429/5000000000 : ℝ)] ![(1888434107589/2500000000000 : ℝ), (7638641547709/50000000000000 : ℝ), (9185352582249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8019623331/10000000000 : ℝ)|^75 ≤ (1888434107589/2500000000000 : ℝ)^59
        have hw : |(8019623331/10000000000 : ℝ)|=(8019623331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456190547/2000000000 : ℝ)|^75 ≤ (7638641547709/50000000000000 : ℝ)^59
        have hw : |(456190547/2000000000 : ℝ)|=(456190547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(764314429/5000000000 : ℝ)|^75 ≤ (9185352582249/100000000000000 : ℝ)^59
        have hw : |(764314429/5000000000 : ℝ)|=(764314429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-114244839/2500000000 : ℝ)*x 0 + (3141944931/5000000000 : ℝ)*x 1 + (2556259351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114244839/2500000000 : ℝ)^75 ≤ (61848436697/3125000000000 : ℝ)^59 := by
    have hnat : (114244839 : ℕ)^75*3125000000000^59 ≤ 61848436697^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114244839 2500000000 61848436697 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3141944931/5000000000 : ℝ)^75 ≤ (55400143176503/100000000000000 : ℝ)^59 := by
    have hnat : (3141944931 : ℕ)^75*100000000000000^59 ≤ 55400143176503^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3141944931 5000000000 55400143176503 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2556259351/5000000000 : ℝ)^75 ≤ (106551767091/250000000000 : ℝ)^59 := by
    have hnat : (2556259351 : ℕ)^75*250000000000^59 ≤ 106551767091^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556259351 5000000000 106551767091 250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114244839/2500000000 : ℝ), (3141944931/5000000000 : ℝ), (2556259351/5000000000 : ℝ)] ![(61848436697/3125000000000 : ℝ), (55400143176503/100000000000000 : ℝ), (106551767091/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114244839/2500000000 : ℝ)|^75 ≤ (61848436697/3125000000000 : ℝ)^59
        have hw : |(-114244839/2500000000 : ℝ)|=(114244839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3141944931/5000000000 : ℝ)|^75 ≤ (55400143176503/100000000000000 : ℝ)^59
        have hw : |(3141944931/5000000000 : ℝ)|=(3141944931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2556259351/5000000000 : ℝ)|^75 ≤ (106551767091/250000000000 : ℝ)^59
        have hw : |(2556259351/5000000000 : ℝ)|=(2556259351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3437046959/5000000000 : ℝ)*x 0 + (-190427801/5000000000 : ℝ)*x 1 + (2254625559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3437046959/5000000000 : ℝ)^75 ≤ (31048491604189/50000000000000 : ℝ)^59 := by
    have hnat : (3437046959 : ℕ)^75*50000000000000^59 ≤ 31048491604189^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3437046959 5000000000 31048491604189 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190427801/5000000000 : ℝ)^75 ≤ (392483864433/25000000000000 : ℝ)^59 := by
    have hnat : (190427801 : ℕ)^75*25000000000000^59 ≤ 392483864433^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190427801 5000000000 392483864433 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254625559/5000000000 : ℝ)^75 ≤ (18166540660137/50000000000000 : ℝ)^59 := by
    have hnat : (2254625559 : ℕ)^75*50000000000000^59 ≤ 18166540660137^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254625559 5000000000 18166540660137 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3437046959/5000000000 : ℝ), (-190427801/5000000000 : ℝ), (2254625559/5000000000 : ℝ)] ![(31048491604189/50000000000000 : ℝ), (392483864433/25000000000000 : ℝ), (18166540660137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3437046959/5000000000 : ℝ)|^75 ≤ (31048491604189/50000000000000 : ℝ)^59
        have hw : |(3437046959/5000000000 : ℝ)|=(3437046959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190427801/5000000000 : ℝ)|^75 ≤ (392483864433/25000000000000 : ℝ)^59
        have hw : |(-190427801/5000000000 : ℝ)|=(190427801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254625559/5000000000 : ℝ)|^75 ≤ (18166540660137/50000000000000 : ℝ)^59
        have hw : |(2254625559/5000000000 : ℝ)|=(2254625559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1349946853/5000000000 : ℝ)*x 0 + (4154254903/5000000000 : ℝ)*x 1 + (-471167971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349946853/5000000000 : ℝ)^75 ≤ (18929345276279/100000000000000 : ℝ)^59 := by
    have hnat : (1349946853 : ℕ)^75*100000000000000^59 ≤ 18929345276279^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349946853 5000000000 18929345276279 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154254903/5000000000 : ℝ)^75 ≤ (15802612774891/20000000000000 : ℝ)^59 := by
    have hnat : (4154254903 : ℕ)^75*20000000000000^59 ≤ 15802612774891^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154254903 5000000000 15802612774891 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471167971/10000000000 : ℝ)^75 ≤ (2057590837913/100000000000000 : ℝ)^59 := by
    have hnat : (471167971 : ℕ)^75*100000000000000^59 ≤ 2057590837913^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471167971 10000000000 2057590837913 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349946853/5000000000 : ℝ), (4154254903/5000000000 : ℝ), (-471167971/10000000000 : ℝ)] ![(18929345276279/100000000000000 : ℝ), (15802612774891/20000000000000 : ℝ), (2057590837913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349946853/5000000000 : ℝ)|^75 ≤ (18929345276279/100000000000000 : ℝ)^59
        have hw : |(1349946853/5000000000 : ℝ)|=(1349946853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154254903/5000000000 : ℝ)|^75 ≤ (15802612774891/20000000000000 : ℝ)^59
        have hw : |(4154254903/5000000000 : ℝ)|=(4154254903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471167971/10000000000 : ℝ)|^75 ≤ (2057590837913/100000000000000 : ℝ)^59
        have hw : |(-471167971/10000000000 : ℝ)|=(471167971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8539202853/10000000000 : ℝ)*x 0 + (1592194411/10000000000 : ℝ)*x 1 + (1440042821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8539202853/10000000000 : ℝ)^75 ≤ (81812307220839/100000000000000 : ℝ)^59 := by
    have hnat : (8539202853 : ℕ)^75*100000000000000^59 ≤ 81812307220839^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8539202853 10000000000 81812307220839 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1592194411/10000000000 : ℝ)^75 ≤ (967360291771/10000000000000 : ℝ)^59 := by
    have hnat : (1592194411 : ℕ)^75*10000000000000^59 ≤ 967360291771^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592194411 10000000000 967360291771 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1440042821/10000000000 : ℝ)^75 ≤ (8514089840223/100000000000000 : ℝ)^59 := by
    have hnat : (1440042821 : ℕ)^75*100000000000000^59 ≤ 8514089840223^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440042821 10000000000 8514089840223 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8539202853/10000000000 : ℝ), (1592194411/10000000000 : ℝ), (1440042821/10000000000 : ℝ)] ![(81812307220839/100000000000000 : ℝ), (967360291771/10000000000000 : ℝ), (8514089840223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8539202853/10000000000 : ℝ)|^75 ≤ (81812307220839/100000000000000 : ℝ)^59
        have hw : |(8539202853/10000000000 : ℝ)|=(8539202853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1592194411/10000000000 : ℝ)|^75 ≤ (967360291771/10000000000000 : ℝ)^59
        have hw : |(1592194411/10000000000 : ℝ)|=(1592194411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1440042821/10000000000 : ℝ)|^75 ≤ (8514089840223/100000000000000 : ℝ)^59
        have hw : |(1440042821/10000000000 : ℝ)|=(1440042821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314061_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((5173/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5173/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81341/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15663/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15663/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31811/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31811/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58623/100000 : ℝ)*X 1 2) := by
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
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (5173/6250 : ℝ) ^ (37/8 : ℝ) ≤ (20848935547546180087/50000000000000000000 : ℝ) := by
    have hpowers : (5173/6250 : ℝ)^37 ≤ (20848935547546180087/50000000000000000000 : ℝ)^8 := by
      have hnat : (5173 : ℕ)^37*50000000000000000000^8 ≤ 20848935547546180087^8*6250^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5173 6250 20848935547546180087 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5173/6250 : ℝ)) (X := (20848935547546180087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (70848935547546180087/50000000000000000000 : ℝ) ≤ (10782692134303661/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (70848935547546180087/50000000000000000000 : ℝ)^8 ≤ (10782692134303661/10000000000000000 : ℝ)^37 := by
      have hnat : (70848935547546180087 : ℕ)^8*10000000000000000^37 ≤ 10782692134303661^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70848935547546180087 50000000000000000000 10782692134303661 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10782692134303661/10000000000000000 : ℝ)) (X := (70848935547546180087/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (45848935547546180087/25000000000000000000 : ℝ) ≤ (1425144954970647/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (45848935547546180087/25000000000000000000 : ℝ)^8 ≤ (1425144954970647/1250000000000000 : ℝ)^37 := by
      have hnat : (45848935547546180087 : ℕ)^8*1250000000000000^37 ≤ 1425144954970647^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45848935547546180087 25000000000000000000 1425144954970647 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1425144954970647/1250000000000000 : ℝ)) (X := (45848935547546180087/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(782692134303661/8276800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(123693501092303/1655360000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (5173/6250 : ℝ)) (alpha := (782692134303661/8276800000000000 : ℝ)) (beta := (123693501092303/1655360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5173/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(782692134303661/8276800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(123693501092303/1655360000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (81341/100000 : ℝ) ^ (37/8 : ℝ) ≤ (4809406480001176967/12500000000000000000 : ℝ) := by
    have hpowers : (81341/100000 : ℝ)^37 ≤ (4809406480001176967/12500000000000000000 : ℝ)^8 := by
      have hnat : (81341 : ℕ)^37*12500000000000000000^8 ≤ 4809406480001176967^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81341 100000 4809406480001176967 12500000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81341/100000 : ℝ)) (X := (4809406480001176967/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (17309406480001176967/12500000000000000000 : ℝ) ≤ (10729190448497103/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (17309406480001176967/12500000000000000000 : ℝ)^8 ≤ (10729190448497103/10000000000000000 : ℝ)^37 := by
      have hnat : (17309406480001176967 : ℕ)^8*10000000000000000^37 ≤ 10729190448497103^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17309406480001176967 12500000000000000000 10729190448497103 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10729190448497103/10000000000000000 : ℝ)) (X := (17309406480001176967/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11059406480001176967/6250000000000000000 : ℝ) ≤ (2262661434818699/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (11059406480001176967/6250000000000000000 : ℝ)^8 ≤ (2262661434818699/2000000000000000 : ℝ)^37 := by
      have hnat : (11059406480001176967 : ℕ)^8*2000000000000000^37 ≤ 2262661434818699^37*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11059406480001176967 6250000000000000000 2262661434818699 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2262661434818699/2000000000000000 : ℝ)) (X := (11059406480001176967/6250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(729190448497103/8134100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(73014590699549/1016762500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (81341/100000 : ℝ)) (alpha := (729190448497103/8134100000000000 : ℝ)) (beta := (73014590699549/1016762500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (81341/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(729190448497103/8134100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(73014590699549/1016762500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (15663/20000 : ℝ) ^ (37/8 : ℝ) ≤ (403592342146519567/1250000000000000000 : ℝ) := by
    have hpowers : (15663/20000 : ℝ)^37 ≤ (403592342146519567/1250000000000000000 : ℝ)^8 := by
      have hnat : (15663 : ℕ)^37*1250000000000000000^8 ≤ 403592342146519567^8*20000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15663 20000 403592342146519567 1250000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15663/20000 : ℝ)) (X := (403592342146519567/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1653592342146519567/1250000000000000000 : ℝ) ≤ (2124732460340019/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1653592342146519567/1250000000000000000 : ℝ)^8 ≤ (2124732460340019/2000000000000000 : ℝ)^37 := by
      have hnat : (1653592342146519567 : ℕ)^8*2000000000000000^37 ≤ 2124732460340019^37*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1653592342146519567 1250000000000000000 2124732460340019 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2124732460340019/2000000000000000 : ℝ)) (X := (1653592342146519567/1250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1028592342146519567/625000000000000000 : ℝ) ≤ (445493363501899/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1028592342146519567/625000000000000000 : ℝ)^8 ≤ (445493363501899/400000000000000 : ℝ)^37 := by
      have hnat : (1028592342146519567 : ℕ)^8*400000000000000^37 ≤ 445493363501899^37*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1028592342146519567 625000000000000000 445493363501899 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (445493363501899/400000000000000 : ℝ)) (X := (1028592342146519567/625000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(124732460340019/1566300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(25683589292369/391575000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (15663/20000 : ℝ)) (alpha := (124732460340019/1566300000000000 : ℝ)) (beta := (25683589292369/391575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15663/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(124732460340019/1566300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(25683589292369/391575000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-749053567/5000000000 : ℝ)*X 0 0+(4609747701/10000000000 : ℝ)*X 0 1+(3065017267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2374251063/5000000000 : ℝ)*X 1 0+(-735903479/5000000000 : ℝ)*X 1 1+(120374209/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-925015093/5000000000 : ℝ)*X 0 0+(1402601347/5000000000 : ℝ)*X 0 1+(1854746747/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((211493/625000 : ℝ)*X 1 0+(-138166967/1250000000 : ℝ)*X 1 1+(7442341107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3464182559/10000000000 : ℝ)*X 2 0+(986479057/1250000000 : ℝ)*X 2 1+(-1372371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((17853881/39062500 : ℝ)*X 0 0+(6040941743/10000000000 : ℝ)*X 0 1+(1678581941/10000000000 : ℝ)*X 0 2+(17853881/39062500 : ℝ)*X 1 0+(6040941743/10000000000 : ℝ)*X 1 1+(1678581941/10000000000 : ℝ)*X 1 2+(17853881/39062500 : ℝ)*X 2 0+(6040941743/10000000000 : ℝ)*X 2 1+(1678581941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-393999301/5000000000 : ℝ)*X 0 0+(3182744267/10000000000 : ℝ)*X 0 1+(7782606321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1235466493/5000000000 : ℝ)*X 1 0+(-102820453/625000000 : ℝ)*X 1 1+(487949563/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3491219251/5000000000 : ℝ)*X 2 0+(906979567/2000000000 : ℝ)*X 2 1+(-29302451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8019623331/10000000000 : ℝ)*X 0 0+(456190547/2000000000 : ℝ)*X 0 1+(764314429/5000000000 : ℝ)*X 0 2+(8019623331/10000000000 : ℝ)*X 1 0+(456190547/2000000000 : ℝ)*X 1 1+(764314429/5000000000 : ℝ)*X 1 2+(8019623331/10000000000 : ℝ)*X 2 0+(456190547/2000000000 : ℝ)*X 2 1+(764314429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-114244839/2500000000 : ℝ)*X 0 0+(3141944931/5000000000 : ℝ)*X 0 1+(2556259351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3437046959/5000000000 : ℝ)*X 1 0+(-190427801/5000000000 : ℝ)*X 1 1+(2254625559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1349946853/5000000000 : ℝ)*X 2 0+(4154254903/5000000000 : ℝ)*X 2 1+(-471167971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8539202853/10000000000 : ℝ)*X 0 0+(1592194411/10000000000 : ℝ)*X 0 1+(1440042821/10000000000 : ℝ)*X 0 2+(8539202853/10000000000 : ℝ)*X 1 0+(1592194411/10000000000 : ℝ)*X 1 1+(1440042821/10000000000 : ℝ)*X 1 2+(8539202853/10000000000 : ℝ)*X 2 0+(1592194411/10000000000 : ℝ)*X 2 1+(1440042821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((30849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10819450883737017455024110739337/878750672181200000000000000000000000 : ℝ) := by norm_num
    linear_combination (703120074607/1000000000000 : ℝ)*(base7) + (142801/125000000000 : ℝ)*(base40) + (535621/1000000000000 : ℝ)*(base50) + (67120303353/500000000000 : ℝ)*(base59) + (1196455834017/500000000000 : ℝ)*(major_s1_0) + (1196455834017/500000000000 : ℝ)*(major_s1_1) + (1196455834017/500000000000 : ℝ)*(major_s1_2) + (10346717/1000000000000 : ℝ)*(sp_s1_0) + (2983228458757/1000000000000 : ℝ)*(sp_s1_7) + (745813674107/250000000000 : ℝ)*(sp_s1_8) + (2983275725671/1000000000000 : ℝ)*(sp_s1_9) + (209378990359/100000000000 : ℝ)*(sp_s1_13) + (18460099/500000000000 : ℝ)*(sp_s1_14) + (21029243/1000000000000 : ℝ)*(sp_s1_15) + (173833728623/125000000000 : ℝ)*(f.failure) + (2983275725671/1000000000000 : ℝ)*(f.sum) + (2536682118588194583/5308517012500000000000000000000 : ℝ)*base63 + (66754607401519/261050000000000000000000000 : ℝ)*base64 + (1053716871528723/2033525000000000000000000000 : ℝ)*base66 + (116844385464451/261050000000000000000000000 : ℝ)*base69 + (498298021624643021/4321317280000000000000000000000 : ℝ)*base71 + (79916859808911/827680000000000000000000000 : ℝ)*base73 + (1224274323758403/2033525000000000000000000000 : ℝ)*base75 + (3803409135847597/4138400000000000000000000000 : ℝ)*base77 + (132268180796619234113/336621594400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (5987/12500000000000000 : ℝ)*base87 + (5987/12500000000000000 : ℝ)*base89 + (5987/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31811/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31811/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1003136493398873923577731875323/175750134436240000000000000000000000 : ℝ) := by norm_num
    linear_combination (381555163737/500000000000 : ℝ)*(base7) + (2814101/1000000000000 : ℝ)*(base19) + (185187/250000000000 : ℝ)*(base40) + (1908323/1000000000000 : ℝ)*(base53) + (9979/500000000000 : ℝ)*(base59) + (953560657783/500000000000 : ℝ)*(major_s1_0) + (953560657783/500000000000 : ℝ)*(major_s1_1) + (476779851811/250000000000 : ℝ)*(major_s1_2) + (1474773/40000000000 : ℝ)*(sp_s1_8) + (1129438608783/500000000000 : ℝ)*(sp_s1_14) + (112941876707/50000000000 : ℝ)*(sp_s1_15) + (2258879125889/1000000000000 : ℝ)*(sp_s1_16) + (1871443336599/1000000000000 : ℝ)*(sp_s1_20) + (2765181/200000000000 : ℝ)*(sp_s1_27) + (1108346835029/1000000000000 : ℝ)*(f.failure) + (2258879125889/1000000000000 : ℝ)*(f.sum) + (3926021563413915421/12740440830000000000000000000000 : ℝ)*base62 + (248534192205401/391575000000000000000000000 : ℝ)*base64 + (935535588444671/4067050000000000000000000000 : ℝ)*base67 + (115628201802373/195787500000000000000000000 : ℝ)*base68 + (1871889729479935973/64819759200000000000000000000000 : ℝ)*base71 + (103852844962407/827680000000000000000000000 : ℝ)*base72 + (3824167079910311/4067050000000000000000000000 : ℝ)*base74 + (907357211960837/4138400000000000000000000000 : ℝ)*base76 + (152933564359973311127/336621594400000000000000000000000 : ℝ)*base78 + (5001/100000000000000000 : ℝ)*base87 + (5001/100000000000000000 : ℝ)*base89 + (94999/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58623/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16360689223888485824158323/2404439960000000000000000000000 : ℝ) := by norm_num
    linear_combination (572095247667/1000000000000 : ℝ)*(base7) + (504283/200000000000 : ℝ)*(base11) + (29458918147/200000000000 : ℝ)*(base40) + (22073/10000000000 : ℝ)*(base43) + (25422401599/1000000000000 : ℝ)*(base59) + (946341777031/500000000000 : ℝ)*(major_s1_0) + (946340673381/500000000000 : ℝ)*(major_s1_1) + (946341777031/500000000000 : ℝ)*(major_s1_2) + (850263/1000000000000 : ℝ)*(sp_s1_1) + (30295207/500000000000 : ℝ)*(sp_s1_9) + (2350282003431/1000000000000 : ℝ)*(sp_s1_21) + (2350285881883/1000000000000 : ℝ)*(sp_s1_22) + (2350223934433/1000000000000 : ℝ)*(sp_s1_23) + (1672051401339/1000000000000 : ℝ)*(sp_s1_27) + (137494519209/125000000000 : ℝ)*(f.failure) + (1175143366073/500000000000 : ℝ)*(f.sum) + (9136783174938374407/63702204150000000000000000000000 : ℝ)*base62 + (209586059168179/783150000000000000000000000 : ℝ)*base65 + (1600004283619247/4067050000000000000000000000 : ℝ)*base67 + (88434869027101/195787500000000000000000000 : ℝ)*base69 + (1437546716595835753/1851993120000000000000000000000 : ℝ)*base70 + (108225891689087/118240000000000000000000000 : ℝ)*base73 + (31988266478011/508381250000000000000000000 : ℝ)*base75 + (359556095435107/591200000000000000000000000 : ℝ)*base76 + (19929591614125700383/48088799200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1579/12500000000000000 : ℝ)*base86 + (1579/12500000000000000 : ℝ)*base88 + (1579/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((5173/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5173/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81341/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15663/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15663/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31811/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31811/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58623/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314061_s1 p hpa hpb X hX hprev0

#print axioms solution

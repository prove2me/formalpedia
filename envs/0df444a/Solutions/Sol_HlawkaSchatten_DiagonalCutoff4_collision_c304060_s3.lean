-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304060_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:47:14.246207+00:00
-- url     : https://prove2.me/submissions/0d322990-5b4d-444c-8eed-58f725df2807

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
theorem collision_support_c304060_s3_s3_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (565425579/1250000000 : ℝ)*x 0 + (-824773503/5000000000 : ℝ)*x 1 + (-639460161/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565425579/1250000000 : ℝ)^133 ≤ (17590410628549/50000000000000 : ℝ)^101 := by
    have hnat : (565425579 : ℕ)^133*50000000000000^101 ≤ 17590410628549^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565425579 1250000000 17590410628549 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824773503/5000000000 : ℝ)^133 ≤ (232992018469/2500000000000 : ℝ)^101 := by
    have hnat : (824773503 : ℕ)^133*2500000000000^101 ≤ 232992018469^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824773503 5000000000 232992018469 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639460161/1000000000 : ℝ)^133 ≤ (55499497978041/100000000000000 : ℝ)^101 := by
    have hnat : (639460161 : ℕ)^133*100000000000000^101 ≤ 55499497978041^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639460161 1000000000 55499497978041 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565425579/1250000000 : ℝ), (-824773503/5000000000 : ℝ), (-639460161/1000000000 : ℝ)] ![(17590410628549/50000000000000 : ℝ), (232992018469/2500000000000 : ℝ), (55499497978041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565425579/1250000000 : ℝ)|^133 ≤ (17590410628549/50000000000000 : ℝ)^101
        have hw : |(565425579/1250000000 : ℝ)|=(565425579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-824773503/5000000000 : ℝ)|^133 ≤ (232992018469/2500000000000 : ℝ)^101
        have hw : |(-824773503/5000000000 : ℝ)|=(824773503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-639460161/1000000000 : ℝ)|^133 ≤ (55499497978041/100000000000000 : ℝ)^101
        have hw : |(-639460161/1000000000 : ℝ)|=(639460161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2384882137/5000000000 : ℝ)*x 0 + (6208042543/10000000000 : ℝ)*x 1 + (1592458059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2384882137/5000000000 : ℝ)^133 ≤ (18862730400719/50000000000000 : ℝ)^101 := by
    have hnat : (2384882137 : ℕ)^133*50000000000000^101 ≤ 18862730400719^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384882137 5000000000 18862730400719 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6208042543/10000000000 : ℝ)^133 ≤ (26688623369249/50000000000000 : ℝ)^101 := by
    have hnat : (6208042543 : ℕ)^133*50000000000000^101 ≤ 26688623369249^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6208042543 10000000000 26688623369249 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592458059/10000000000 : ℝ)^133 ≤ (1779458487969/20000000000000 : ℝ)^101 := by
    have hnat : (1592458059 : ℕ)^133*20000000000000^101 ≤ 1779458487969^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592458059 10000000000 1779458487969 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2384882137/5000000000 : ℝ), (6208042543/10000000000 : ℝ), (1592458059/10000000000 : ℝ)] ![(18862730400719/50000000000000 : ℝ), (26688623369249/50000000000000 : ℝ), (1779458487969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2384882137/5000000000 : ℝ)|^133 ≤ (18862730400719/50000000000000 : ℝ)^101
        have hw : |(2384882137/5000000000 : ℝ)|=(2384882137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6208042543/10000000000 : ℝ)|^133 ≤ (26688623369249/50000000000000 : ℝ)^101
        have hw : |(6208042543/10000000000 : ℝ)|=(6208042543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592458059/10000000000 : ℝ)|^133 ≤ (1779458487969/20000000000000 : ℝ)^101
        have hw : |(1592458059/10000000000 : ℝ)|=(1592458059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1383216629/10000000000 : ℝ)*x 0 + (1232407191/5000000000 : ℝ)*x 1 + (-8183067571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1383216629/10000000000 : ℝ)^133 ≤ (1478178882259/20000000000000 : ℝ)^101 := by
    have hnat : (1383216629 : ℕ)^133*20000000000000^101 ≤ 1478178882259^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383216629 10000000000 1478178882259 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232407191/5000000000 : ℝ)^133 ≤ (632618927017/4000000000000 : ℝ)^101 := by
    have hnat : (1232407191 : ℕ)^133*4000000000000^101 ≤ 632618927017^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232407191 5000000000 632618927017 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8183067571/10000000000 : ℝ)^133 ≤ (76793632401543/100000000000000 : ℝ)^101 := by
    have hnat : (8183067571 : ℕ)^133*100000000000000^101 ≤ 76793632401543^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8183067571 10000000000 76793632401543 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1383216629/10000000000 : ℝ), (1232407191/5000000000 : ℝ), (-8183067571/10000000000 : ℝ)] ![(1478178882259/20000000000000 : ℝ), (632618927017/4000000000000 : ℝ), (76793632401543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1383216629/10000000000 : ℝ)|^133 ≤ (1478178882259/20000000000000 : ℝ)^101
        have hw : |(-1383216629/10000000000 : ℝ)|=(1383216629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232407191/5000000000 : ℝ)|^133 ≤ (632618927017/4000000000000 : ℝ)^101
        have hw : |(1232407191/5000000000 : ℝ)|=(1232407191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8183067571/10000000000 : ℝ)|^133 ≤ (76793632401543/100000000000000 : ℝ)^101
        have hw : |(-8183067571/10000000000 : ℝ)|=(8183067571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2769386791/10000000000 : ℝ)*x 0 + (-484922599/5000000000 : ℝ)*x 1 + (-8194198383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2769386791/10000000000 : ℝ)^133 ≤ (18437968941421/100000000000000 : ℝ)^101 := by
    have hnat : (2769386791 : ℕ)^133*100000000000000^101 ≤ 18437968941421^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769386791 10000000000 18437968941421 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484922599/5000000000 : ℝ)^133 ≤ (4630817245137/100000000000000 : ℝ)^101 := by
    have hnat : (484922599 : ℕ)^133*100000000000000^101 ≤ 4630817245137^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484922599 5000000000 4630817245137 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8194198383/10000000000 : ℝ)^133 ≤ (38465606901843/50000000000000 : ℝ)^101 := by
    have hnat : (8194198383 : ℕ)^133*50000000000000^101 ≤ 38465606901843^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8194198383 10000000000 38465606901843 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2769386791/10000000000 : ℝ), (-484922599/5000000000 : ℝ), (-8194198383/10000000000 : ℝ)] ![(18437968941421/100000000000000 : ℝ), (4630817245137/100000000000000 : ℝ), (38465606901843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2769386791/10000000000 : ℝ)|^133 ≤ (18437968941421/100000000000000 : ℝ)^101
        have hw : |(2769386791/10000000000 : ℝ)|=(2769386791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484922599/5000000000 : ℝ)|^133 ≤ (4630817245137/100000000000000 : ℝ)^101
        have hw : |(-484922599/5000000000 : ℝ)|=(484922599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8194198383/10000000000 : ℝ)|^133 ≤ (38465606901843/50000000000000 : ℝ)^101
        have hw : |(-8194198383/10000000000 : ℝ)|=(8194198383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2688497777/10000000000 : ℝ)*x 0 + (39233523/50000000 : ℝ)*x 1 + (421893577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688497777/10000000000 : ℝ)^133 ≤ (17732104169001/100000000000000 : ℝ)^101 := by
    have hnat : (2688497777 : ℕ)^133*100000000000000^101 ≤ 17732104169001^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688497777 10000000000 17732104169001 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39233523/50000000 : ℝ)^133 ≤ (72664268234849/100000000000000 : ℝ)^101 := by
    have hnat : (39233523 : ℕ)^133*100000000000000^101 ≤ 72664268234849^101*50000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39233523 50000000 72664268234849 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421893577/2500000000 : ℝ)^133 ≤ (960362758743/10000000000000 : ℝ)^101 := by
    have hnat : (421893577 : ℕ)^133*10000000000000^101 ≤ 960362758743^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421893577 2500000000 960362758743 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688497777/10000000000 : ℝ), (39233523/50000000 : ℝ), (421893577/2500000000 : ℝ)] ![(17732104169001/100000000000000 : ℝ), (72664268234849/100000000000000 : ℝ), (960362758743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688497777/10000000000 : ℝ)|^133 ≤ (17732104169001/100000000000000 : ℝ)^101
        have hw : |(2688497777/10000000000 : ℝ)|=(2688497777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39233523/50000000 : ℝ)|^133 ≤ (72664268234849/100000000000000 : ℝ)^101
        have hw : |(39233523/50000000 : ℝ)|=(39233523/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(421893577/2500000000 : ℝ)|^133 ≤ (960362758743/10000000000000 : ℝ)^101
        have hw : |(421893577/2500000000 : ℝ)|=(421893577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2277653061/5000000000 : ℝ)*x 0 + (7167034303/10000000000 : ℝ)*x 1 + (71/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2277653061/5000000000 : ℝ)^133 ≤ (35507910251459/100000000000000 : ℝ)^101 := by
    have hnat : (2277653061 : ℕ)^133*100000000000000^101 ≤ 35507910251459^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277653061 5000000000 35507910251459 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7167034303/10000000000 : ℝ)^133 ≤ (64492089505147/100000000000000 : ℝ)^101 := by
    have hnat : (7167034303 : ℕ)^133*100000000000000^101 ≤ 64492089505147^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7167034303 10000000000 64492089505147 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71/250000000 : ℝ)^133 ≤ (239399/100000000000000 : ℝ)^101 := by
    have hnat : (71 : ℕ)^133*100000000000000^101 ≤ 239399^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71 250000000 239399 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2277653061/5000000000 : ℝ), (7167034303/10000000000 : ℝ), (71/250000000 : ℝ)] ![(35507910251459/100000000000000 : ℝ), (64492089505147/100000000000000 : ℝ), (239399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2277653061/5000000000 : ℝ)|^133 ≤ (35507910251459/100000000000000 : ℝ)^101
        have hw : |(2277653061/5000000000 : ℝ)|=(2277653061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7167034303/10000000000 : ℝ)|^133 ≤ (64492089505147/100000000000000 : ℝ)^101
        have hw : |(7167034303/10000000000 : ℝ)|=(7167034303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71/250000000 : ℝ)|^133 ≤ (239399/100000000000000 : ℝ)^101
        have hw : |(71/250000000 : ℝ)|=(71/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-780528291/5000000000 : ℝ)*x 0 + (2050418229/10000000000 : ℝ)*x 1 + (-2088679379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (780528291/5000000000 : ℝ)^133 ≤ (2166746606479/25000000000000 : ℝ)^101 := by
    have hnat : (780528291 : ℕ)^133*25000000000000^101 ≤ 2166746606479^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780528291 5000000000 2166746606479 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050418229/10000000000 : ℝ)^133 ≤ (6205579518689/50000000000000 : ℝ)^101 := by
    have hnat : (2050418229 : ℕ)^133*50000000000000^101 ≤ 6205579518689^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050418229 10000000000 6205579518689 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088679379/2500000000 : ℝ)^133 ≤ (3946092725963/5000000000000 : ℝ)^101 := by
    have hnat : (2088679379 : ℕ)^133*5000000000000^101 ≤ 3946092725963^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088679379 2500000000 3946092725963 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-780528291/5000000000 : ℝ), (2050418229/10000000000 : ℝ), (-2088679379/2500000000 : ℝ)] ![(2166746606479/25000000000000 : ℝ), (6205579518689/50000000000000 : ℝ), (3946092725963/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-780528291/5000000000 : ℝ)|^133 ≤ (2166746606479/25000000000000 : ℝ)^101
        have hw : |(-780528291/5000000000 : ℝ)|=(780528291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2050418229/10000000000 : ℝ)|^133 ≤ (6205579518689/50000000000000 : ℝ)^101
        have hw : |(2050418229/10000000000 : ℝ)|=(2050418229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088679379/2500000000 : ℝ)|^133 ≤ (3946092725963/5000000000000 : ℝ)^101
        have hw : |(-2088679379/2500000000 : ℝ)|=(2088679379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (207054187/1250000000 : ℝ)*x 0 + (-971728289/5000000000 : ℝ)*x 1 + (-1673217619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207054187/1250000000 : ℝ)^133 ≤ (1171368666209/12500000000000 : ℝ)^101 := by
    have hnat : (207054187 : ℕ)^133*12500000000000^101 ≤ 1171368666209^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207054187 1250000000 1171368666209 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971728289/5000000000 : ℝ)^133 ≤ (5782861829531/50000000000000 : ℝ)^101 := by
    have hnat : (971728289 : ℕ)^133*50000000000000^101 ≤ 5782861829531^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971728289 5000000000 5782861829531 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1673217619/2000000000 : ℝ)^133 ≤ (39531663497467/50000000000000 : ℝ)^101 := by
    have hnat : (1673217619 : ℕ)^133*50000000000000^101 ≤ 39531663497467^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673217619 2000000000 39531663497467 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207054187/1250000000 : ℝ), (-971728289/5000000000 : ℝ), (-1673217619/2000000000 : ℝ)] ![(1171368666209/12500000000000 : ℝ), (5782861829531/50000000000000 : ℝ), (39531663497467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207054187/1250000000 : ℝ)|^133 ≤ (1171368666209/12500000000000 : ℝ)^101
        have hw : |(207054187/1250000000 : ℝ)|=(207054187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971728289/5000000000 : ℝ)|^133 ≤ (5782861829531/50000000000000 : ℝ)^101
        have hw : |(-971728289/5000000000 : ℝ)|=(971728289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1673217619/2000000000 : ℝ)|^133 ≤ (39531663497467/50000000000000 : ℝ)^101
        have hw : |(-1673217619/2000000000 : ℝ)|=(1673217619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6586500461/10000000000 : ℝ)*x 0 + (4056923819/10000000000 : ℝ)*x 1 + (987509543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6586500461/10000000000 : ℝ)^133 ≤ (28851526936377/50000000000000 : ℝ)^101 := by
    have hnat : (6586500461 : ℕ)^133*50000000000000^101 ≤ 28851526936377^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6586500461 10000000000 28851526936377 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4056923819/10000000000 : ℝ)^133 ≤ (3810405671633/12500000000000 : ℝ)^101 := by
    have hnat : (4056923819 : ℕ)^133*12500000000000^101 ≤ 3810405671633^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056923819 10000000000 3810405671633 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987509543/5000000000 : ℝ)^133 ≤ (1181370073751/10000000000000 : ℝ)^101 := by
    have hnat : (987509543 : ℕ)^133*10000000000000^101 ≤ 1181370073751^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987509543 5000000000 1181370073751 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6586500461/10000000000 : ℝ), (4056923819/10000000000 : ℝ), (987509543/5000000000 : ℝ)] ![(28851526936377/50000000000000 : ℝ), (3810405671633/12500000000000 : ℝ), (1181370073751/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6586500461/10000000000 : ℝ)|^133 ≤ (28851526936377/50000000000000 : ℝ)^101
        have hw : |(6586500461/10000000000 : ℝ)|=(6586500461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4056923819/10000000000 : ℝ)|^133 ≤ (3810405671633/12500000000000 : ℝ)^101
        have hw : |(4056923819/10000000000 : ℝ)|=(4056923819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(987509543/5000000000 : ℝ)|^133 ≤ (1181370073751/10000000000000 : ℝ)^101
        have hw : |(987509543/5000000000 : ℝ)|=(987509543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1742055533/2000000000 : ℝ)*x 0 + (2560125643/10000000000 : ℝ)*x 1 + (3537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742055533/2000000000 : ℝ)^133 ≤ (83374306996911/100000000000000 : ℝ)^101 := by
    have hnat : (1742055533 : ℕ)^133*100000000000000^101 ≤ 83374306996911^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742055533 2000000000 83374306996911 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560125643/10000000000 : ℝ)^133 ≤ (8312845506081/50000000000000 : ℝ)^101 := by
    have hnat : (2560125643 : ℕ)^133*50000000000000^101 ≤ 8312845506081^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560125643 10000000000 8312845506081 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3537/2500000000 : ℝ)^133 ≤ (1983581/100000000000000 : ℝ)^101 := by
    have hnat : (3537 : ℕ)^133*100000000000000^101 ≤ 1983581^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3537 2500000000 1983581 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1742055533/2000000000 : ℝ), (2560125643/10000000000 : ℝ), (3537/2500000000 : ℝ)] ![(83374306996911/100000000000000 : ℝ), (8312845506081/50000000000000 : ℝ), (1983581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1742055533/2000000000 : ℝ)|^133 ≤ (83374306996911/100000000000000 : ℝ)^101
        have hw : |(1742055533/2000000000 : ℝ)|=(1742055533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2560125643/10000000000 : ℝ)|^133 ≤ (8312845506081/50000000000000 : ℝ)^101
        have hw : |(2560125643/10000000000 : ℝ)|=(2560125643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3537/2500000000 : ℝ)|^133 ≤ (1983581/100000000000000 : ℝ)^101
        have hw : |(3537/2500000000 : ℝ)|=(3537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1404195031/10000000000 : ℝ)*x 0 + (4732650773/10000000000 : ℝ)*x 1 + (-795190333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1404195031/10000000000 : ℝ)^133 ≤ (1884713922637/25000000000000 : ℝ)^101 := by
    have hnat : (1404195031 : ℕ)^133*25000000000000^101 ≤ 1884713922637^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404195031 10000000000 1884713922637 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4732650773/10000000000 : ℝ)^133 ≤ (37339393322369/100000000000000 : ℝ)^101 := by
    have hnat : (4732650773 : ℕ)^133*100000000000000^101 ≤ 37339393322369^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4732650773 10000000000 37339393322369 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795190333/1250000000 : ℝ)^133 ≤ (27560875485699/50000000000000 : ℝ)^101 := by
    have hnat : (795190333 : ℕ)^133*50000000000000^101 ≤ 27560875485699^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795190333 1250000000 27560875485699 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1404195031/10000000000 : ℝ), (4732650773/10000000000 : ℝ), (-795190333/1250000000 : ℝ)] ![(1884713922637/25000000000000 : ℝ), (37339393322369/100000000000000 : ℝ), (27560875485699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1404195031/10000000000 : ℝ)|^133 ≤ (1884713922637/25000000000000 : ℝ)^101
        have hw : |(-1404195031/10000000000 : ℝ)|=(1404195031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4732650773/10000000000 : ℝ)|^133 ≤ (37339393322369/100000000000000 : ℝ)^101
        have hw : |(4732650773/10000000000 : ℝ)|=(4732650773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-795190333/1250000000 : ℝ)|^133 ≤ (27560875485699/50000000000000 : ℝ)^101
        have hw : |(-795190333/1250000000 : ℝ)|=(795190333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7009058001/10000000000 : ℝ)*x 0 + (-15371699/125000000 : ℝ)*x 1 + (-51416907/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7009058001/10000000000 : ℝ)^133 ≤ (3914170680989/6250000000000 : ℝ)^101 := by
    have hnat : (7009058001 : ℕ)^133*6250000000000^101 ≤ 3914170680989^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7009058001 10000000000 3914170680989 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15371699/125000000 : ℝ)^133 ≤ (1266092434351/20000000000000 : ℝ)^101 := by
    have hnat : (15371699 : ℕ)^133*20000000000000^101 ≤ 1266092434351^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15371699 125000000 1266092434351 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51416907/125000000 : ℝ)^133 ≤ (31042806919073/100000000000000 : ℝ)^101 := by
    have hnat : (51416907 : ℕ)^133*100000000000000^101 ≤ 31042806919073^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51416907 125000000 31042806919073 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7009058001/10000000000 : ℝ), (-15371699/125000000 : ℝ), (-51416907/125000000 : ℝ)] ![(3914170680989/6250000000000 : ℝ), (1266092434351/20000000000000 : ℝ), (31042806919073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7009058001/10000000000 : ℝ)|^133 ≤ (3914170680989/6250000000000 : ℝ)^101
        have hw : |(7009058001/10000000000 : ℝ)|=(7009058001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15371699/125000000 : ℝ)|^133 ≤ (1266092434351/20000000000000 : ℝ)^101
        have hw : |(-15371699/125000000 : ℝ)|=(15371699/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51416907/125000000 : ℝ)|^133 ≤ (31042806919073/100000000000000 : ℝ)^101
        have hw : |(-51416907/125000000 : ℝ)|=(51416907/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (38288573/156250000 : ℝ)*x 0 + (1917548591/2500000000 : ℝ)*x 1 + (3553147/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38288573/156250000 : ℝ)^133 ≤ (15694371781203/100000000000000 : ℝ)^101 := by
    have hnat : (38288573 : ℕ)^133*100000000000000^101 ≤ 15694371781203^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38288573 156250000 15694371781203 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917548591/2500000000 : ℝ)^133 ≤ (70519524819917/100000000000000 : ℝ)^101 := by
    have hnat : (1917548591 : ℕ)^133*100000000000000^101 ≤ 70519524819917^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917548591 2500000000 70519524819917 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3553147/16000000 : ℝ)^133 ≤ (6893051692387/50000000000000 : ℝ)^101 := by
    have hnat : (3553147 : ℕ)^133*50000000000000^101 ≤ 6893051692387^101*16000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3553147 16000000 6893051692387 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(38288573/156250000 : ℝ), (1917548591/2500000000 : ℝ), (3553147/16000000 : ℝ)] ![(15694371781203/100000000000000 : ℝ), (70519524819917/100000000000000 : ℝ), (6893051692387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(38288573/156250000 : ℝ)|^133 ≤ (15694371781203/100000000000000 : ℝ)^101
        have hw : |(38288573/156250000 : ℝ)|=(38288573/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1917548591/2500000000 : ℝ)|^133 ≤ (70519524819917/100000000000000 : ℝ)^101
        have hw : |(1917548591/2500000000 : ℝ)|=(1917548591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3553147/16000000 : ℝ)|^133 ≤ (6893051692387/50000000000000 : ℝ)^101
        have hw : |(3553147/16000000 : ℝ)|=(3553147/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s3_s3_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4549970667/5000000000 : ℝ)*x 0 + (489411827/2500000000 : ℝ)*x 1 + (-3300057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4549970667/5000000000 : ℝ)^133 ≤ (88320337672313/100000000000000 : ℝ)^101 := by
    have hnat : (4549970667 : ℕ)^133*100000000000000^101 ≤ 88320337672313^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549970667 5000000000 88320337672313 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489411827/2500000000 : ℝ)^133 ≤ (11677059298863/100000000000000 : ℝ)^101 := by
    have hnat : (489411827 : ℕ)^133*100000000000000^101 ≤ 11677059298863^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489411827 2500000000 11677059298863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3300057/10000000000 : ℝ)^133 ≤ (130151367/5000000000000 : ℝ)^101 := by
    have hnat : (3300057 : ℕ)^133*5000000000000^101 ≤ 130151367^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3300057 10000000000 130151367 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4549970667/5000000000 : ℝ), (489411827/2500000000 : ℝ), (-3300057/10000000000 : ℝ)] ![(88320337672313/100000000000000 : ℝ), (11677059298863/100000000000000 : ℝ), (130151367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4549970667/5000000000 : ℝ)|^133 ≤ (88320337672313/100000000000000 : ℝ)^101
        have hw : |(4549970667/5000000000 : ℝ)|=(4549970667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(489411827/2500000000 : ℝ)|^133 ≤ (11677059298863/100000000000000 : ℝ)^101
        have hw : |(489411827/2500000000 : ℝ)|=(489411827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3300057/10000000000 : ℝ)|^133 ≤ (130151367/5000000000000 : ℝ)^101
        have hw : |(-3300057/10000000000 : ℝ)|=(3300057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304060_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((22513/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22513/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90703/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(90703/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81619/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81619/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16639/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16639/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10527/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10527/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73333/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73333/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (22513/25000 : ℝ) ^ (33/8 : ℝ) ≤ (64906041190638864147/100000000000000000000 : ℝ) := by
    have hpowers : (22513/25000 : ℝ)^33 ≤ (64906041190638864147/100000000000000000000 : ℝ)^8 := by
      have hnat : (22513 : ℕ)^33*100000000000000000000^8 ≤ 64906041190638864147^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22513 25000 64906041190638864147 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22513/25000 : ℝ)) (X := (64906041190638864147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (164906041190638864147/100000000000000000000 : ℝ) ≤ (11289206312353621/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (164906041190638864147/100000000000000000000 : ℝ)^8 ≤ (11289206312353621/10000000000000000 : ℝ)^33 := by
      have hnat : (164906041190638864147 : ℕ)^8*10000000000000000^33 ≤ 11289206312353621^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        164906041190638864147 100000000000000000000 11289206312353621 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11289206312353621/10000000000000000 : ℝ)) (X := (164906041190638864147/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (114906041190638864147/50000000000000000000 : ℝ) ≤ (6117522082015249/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (114906041190638864147/50000000000000000000 : ℝ)^8 ≤ (6117522082015249/5000000000000000 : ℝ)^33 := by
      have hnat : (114906041190638864147 : ℕ)^8*5000000000000000^33 ≤ 6117522082015249^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114906041190638864147 50000000000000000000 6117522082015249 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6117522082015249/5000000000000000 : ℝ)) (X := (114906041190638864147/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1289206312353621/9005200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(945837851676877/9005200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (22513/25000 : ℝ)) (alpha := (1289206312353621/9005200000000000 : ℝ)) (beta := (945837851676877/9005200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22513/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1289206312353621/9005200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(945837851676877/9005200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (90703/100000 : ℝ) ^ (33/8 : ℝ) ≤ (6686353180379938639/10000000000000000000 : ℝ) := by
    have hpowers : (90703/100000 : ℝ)^33 ≤ (6686353180379938639/10000000000000000000 : ℝ)^8 := by
      have hnat : (90703 : ℕ)^33*10000000000000000000^8 ≤ 6686353180379938639^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90703 100000 6686353180379938639 10000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (90703/100000 : ℝ)) (X := (6686353180379938639/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (16686353180379938639/10000000000000000000 : ℝ) ≤ (113215477238779/100000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (16686353180379938639/10000000000000000000 : ℝ)^8 ≤ (113215477238779/100000000000000 : ℝ)^33 := by
      have hnat : (16686353180379938639 : ℕ)^8*100000000000000^33 ≤ 113215477238779^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16686353180379938639 10000000000000000000 113215477238779 100000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (113215477238779/100000000000000 : ℝ)) (X := (16686353180379938639/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (11686353180379938639/5000000000000000000 : ℝ) ≤ (1535656257350233/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (11686353180379938639/5000000000000000000 : ℝ)^8 ≤ (1535656257350233/1250000000000000 : ℝ)^33 := by
      have hnat : (11686353180379938639 : ℕ)^8*1250000000000000^33 ≤ 1535656257350233^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11686353180379938639 5000000000000000000 1535656257350233 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1535656257350233/1250000000000000 : ℝ)) (X := (11686353180379938639/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(13215477238779/90703000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(240925583730991/2267575000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (90703/100000 : ℝ)) (alpha := (13215477238779/90703000000000 : ℝ)) (beta := (240925583730991/2267575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (90703/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(13215477238779/90703000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(240925583730991/2267575000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (81619/100000 : ℝ) ^ (33/8 : ℝ) ≤ (2163261349506182941/5000000000000000000 : ℝ) := by
    have hpowers : (81619/100000 : ℝ)^33 ≤ (2163261349506182941/5000000000000000000 : ℝ)^8 := by
      have hnat : (81619 : ℕ)^33*5000000000000000000^8 ≤ 2163261349506182941^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81619 100000 2163261349506182941 5000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81619/100000 : ℝ)) (X := (2163261349506182941/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (7163261349506182941/5000000000000000000 : ℝ) ≤ (10910692429586261/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (7163261349506182941/5000000000000000000 : ℝ)^8 ≤ (10910692429586261/10000000000000000 : ℝ)^33 := by
      have hnat : (7163261349506182941 : ℕ)^8*10000000000000000^33 ≤ 10910692429586261^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7163261349506182941 5000000000000000000 10910692429586261 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10910692429586261/10000000000000000 : ℝ)) (X := (7163261349506182941/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (4663261349506182941/2500000000000000000 : ℝ) ≤ (11631515462484261/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (4663261349506182941/2500000000000000000 : ℝ)^8 ≤ (11631515462484261/10000000000000000 : ℝ)^33 := by
      have hnat : (4663261349506182941 : ℕ)^8*10000000000000000^33 ≤ 11631515462484261^33*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4663261349506182941 2500000000000000000 11631515462484261 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11631515462484261/10000000000000000 : ℝ)) (X := (4663261349506182941/2500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(910692429586261/8161900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(360411516449/4080950000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (81619/100000 : ℝ)) (alpha := (910692429586261/8161900000000000 : ℝ)) (beta := (360411516449/4080950000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (81619/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(910692429586261/8161900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(360411516449/4080950000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_1 : ((565425579/1250000000 : ℝ)*X 1 0+(-824773503/5000000000 : ℝ)*X 1 1+(-639460161/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2384882137/5000000000 : ℝ)*X 2 0+(6208042543/10000000000 : ℝ)*X 2 1+(1592458059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1383216629/10000000000 : ℝ)*X 0 0+(1232407191/5000000000 : ℝ)*X 0 1+(-8183067571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2769386791/10000000000 : ℝ)*X 1 0+(-484922599/5000000000 : ℝ)*X 1 1+(-8194198383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2688497777/10000000000 : ℝ)*X 2 0+(39233523/50000000 : ℝ)*X 2 1+(421893577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2277653061/5000000000 : ℝ)*X 0 0+(7167034303/10000000000 : ℝ)*X 0 1+(71/250000000 : ℝ)*X 0 2+(2277653061/5000000000 : ℝ)*X 1 0+(7167034303/10000000000 : ℝ)*X 1 1+(71/250000000 : ℝ)*X 1 2+(2277653061/5000000000 : ℝ)*X 2 0+(7167034303/10000000000 : ℝ)*X 2 1+(71/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-780528291/5000000000 : ℝ)*X 0 0+(2050418229/10000000000 : ℝ)*X 0 1+(-2088679379/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((207054187/1250000000 : ℝ)*X 1 0+(-971728289/5000000000 : ℝ)*X 1 1+(-1673217619/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((6586500461/10000000000 : ℝ)*X 2 0+(4056923819/10000000000 : ℝ)*X 2 1+(987509543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1742055533/2000000000 : ℝ)*X 0 0+(2560125643/10000000000 : ℝ)*X 0 1+(3537/2500000000 : ℝ)*X 0 2+(1742055533/2000000000 : ℝ)*X 1 0+(2560125643/10000000000 : ℝ)*X 1 1+(3537/2500000000 : ℝ)*X 1 2+(1742055533/2000000000 : ℝ)*X 2 0+(2560125643/10000000000 : ℝ)*X 2 1+(3537/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1404195031/10000000000 : ℝ)*X 0 0+(4732650773/10000000000 : ℝ)*X 0 1+(-795190333/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((7009058001/10000000000 : ℝ)*X 1 0+(-15371699/125000000 : ℝ)*X 1 1+(-51416907/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((38288573/156250000 : ℝ)*X 2 0+(1917548591/2500000000 : ℝ)*X 2 1+(3553147/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((4549970667/5000000000 : ℝ)*X 0 0+(489411827/2500000000 : ℝ)*X 0 1+(-3300057/10000000000 : ℝ)*X 0 2+(4549970667/5000000000 : ℝ)*X 1 0+(489411827/2500000000 : ℝ)*X 1 1+(-3300057/10000000000 : ℝ)*X 1 2+(4549970667/5000000000 : ℝ)*X 2 0+(489411827/2500000000 : ℝ)*X 2 1+(-3300057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((16639/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16639/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1357075723224801201964423701/367497709400000000000000000000000 : ℝ) := by norm_num
    linear_combination (165847389137/500000000000 : ℝ)*(base5) + (205985391309/250000000000 : ℝ)*(base7) + (639659/1000000000000 : ℝ)*(base43) + (99229/500000000000 : ℝ)*(base53) + (2075963469667/1000000000000 : ℝ)*(major_s3_0) + (2075962830009/1000000000000 : ℝ)*(major_s3_1) + (207596327121/100000000000 : ℝ)*(major_s3_2) + (2210307/500000000000 : ℝ)*(sp_s3_1) + (226736078247/100000000000 : ℝ)*(sp_s3_7) + (2267344164399/1000000000000 : ℝ)*(sp_s3_8) + (2599053988331/1000000000000 : ℝ)*(sp_s3_9) + (930482889521/500000000000 : ℝ)*(sp_s3_13) + (3209279/250000000000 : ℝ)*(sp_s3_15) + (177087/100000000000 : ℝ)*(sp_s3_23) + (17108987401/12500000000 : ℝ)*(f.failure) + (2267361620587/1000000000000 : ℝ)*(f.sum) + (384198766071753279/2961235262800000000000000000000 : ℝ)*base63 + (259010028386173/408095000000000000000000000 : ℝ)*base65 + (647621280612703/1133787500000000000000000000 : ℝ)*base66 + (24676628359321/408095000000000000000000000 : ℝ)*base68 + (75360928720679556173/734995418800000000000000000000000 : ℝ)*base71 + (3154454376659601/9005200000000000000000000000 : ℝ)*base72 + (19182131925443/907030000000000000000000000 : ℝ)*base74 + (9550303369671087/9005200000000000000000000000 : ℝ)*base77 + (115996560802831808649/816798655600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (361/625000000000000 : ℝ)*base87 + (33/78125000000000 : ℝ)*base88 + (33/78125000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10527/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10527/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20264130495625051226662460873163/4166643091963525000000000000000000000 : ℝ) := by norm_num
    linear_combination (212081923931/250000000000 : ℝ)*(base7) + (969977/250000000000 : ℝ)*(base12) + (139997/250000000000 : ℝ)*(base39) + (75829/500000000000 : ℝ)*(base49) + (8248287221/250000000000 : ℝ)*(base60) + (245047560413/125000000000 : ℝ)*(major_s3_0) + (245047560413/125000000000 : ℝ)*(major_s3_1) + (245047560413/125000000000 : ℝ)*(major_s3_2) + (5130693/1000000000000 : ℝ)*(sp_s3_1) + (729111/200000000000 : ℝ)*(sp_s3_8) + (524282458921/250000000000 : ℝ)*(sp_s3_14) + (131070308709/62500000000 : ℝ)*(sp_s3_15) + (262141714449/125000000000 : ℝ)*(sp_s3_16) + (1070420402567/500000000000 : ℝ)*(sp_s3_20) + (129251310941/100000000000 : ℝ)*(f.failure) + (262141714449/125000000000 : ℝ)*(f.sum) + (150721679007419431077/185077203925000000000000000000000 : ℝ)*base62 + (220590559988581/408095000000000000000000000 : ℝ)*base64 + (167606026014651/566893750000000000000000000 : ℝ)*base67 + (3930574902684753/4080950000000000000000000000 : ℝ)*base68 + (43910086875319458483/91874427350000000000000000000000 : ℝ)*base70 + (85623889994501/281412500000000000000000000 : ℝ)*base72 + (225015666398653/453515000000000000000000000 : ℝ)*base74 + (262688632725177/1125650000000000000000000000 : ℝ)*base76 + (279094014308324913/102099831950000000000000000000000 : ℝ)*base78 + (419/1250000000000000 : ℝ)*base87 + (419/1250000000000000 : ℝ)*base89 + (419/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73333/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73333/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2489519952650881404038532282387/333331447357082000000000000000000000 : ℝ) := by norm_num
    linear_combination (568403961979/1000000000000 : ℝ)*(base7) + (2552347/500000000000 : ℝ)*(base16) + (2992551/500000000000 : ℝ)*(base34) + (178579/200000000000 : ℝ)*(base40) + (58943095891/100000000000 : ℝ)*(base43) + (1710361125619/1000000000000 : ℝ)*(major_s3_0) + (280234037953/250000000000 : ℝ)*(major_s3_1) + (855183555361/500000000000 : ℝ)*(major_s3_2) + (157133/10000000000 : ℝ)*(sp_s3_2) + (90504453/1000000000000 : ℝ)*(sp_s3_20) + (1347759195421/1000000000000 : ℝ)*(sp_s3_21) + (1937191034739/1000000000000 : ℝ)*(sp_s3_22) + (1347749467223/1000000000000 : ℝ)*(sp_s3_23) + (1695982396419/1000000000000 : ℝ)*(sp_s3_27) + (225534984799/200000000000 : ℝ)*(f.failure) + (1937196139433/1000000000000 : ℝ)*(f.sum) + (111541329431192688937/370154407850000000000000000000000 : ℝ)*base62 + (16679081316129/204047500000000000000000000 : ℝ)*base64 + (1405980402347629/4535150000000000000000000000 : ℝ)*base67 + (3431594293528129/4080950000000000000000000000 : ℝ)*base68 + (489941615348637569899/734995418800000000000000000000000 : ℝ)*base70 + (2015648581584943/9005200000000000000000000000 : ℝ)*base73 + (815167600949161/907030000000000000000000000 : ℝ)*base74 + (1928705716513161/9005200000000000000000000000 : ℝ)*base76 + (52456937296608030293/163359731120000000000000000000000 : ℝ)*base79 + (1741/2500000000000000 : ℝ)*base87 + (759/2500000000000000 : ℝ)*base88 + (759/2500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((22513/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22513/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90703/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(90703/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81619/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81619/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16639/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16639/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10527/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10527/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73333/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73333/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304060_s3 p hpa hpb X hX hprev2

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:48:27.424028+00:00
-- url     : https://prove2.me/submissions/06ec26f6-2437-46c7-8489-a6e4abfa4283

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
theorem collision_support_c314063_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-630393291/10000000000 : ℝ)*x 0 + (1114746801/2000000000 : ℝ)*x 1 + (89796381/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (630393291/10000000000 : ℝ)^75 ≤ (2979082429959/100000000000000 : ℝ)^59 := by
    have hnat : (630393291 : ℕ)^75*100000000000000^59 ≤ 2979082429959^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630393291 10000000000 2979082429959 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114746801/2000000000 : ℝ)^75 ≤ (1486464572181/3125000000000 : ℝ)^59 := by
    have hnat : (1114746801 : ℕ)^75*3125000000000^59 ≤ 1486464572181^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114746801 2000000000 1486464572181 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89796381/156250000 : ℝ)^75 ≤ (989081024849/2000000000000 : ℝ)^59 := by
    have hnat : (89796381 : ℕ)^75*2000000000000^59 ≤ 989081024849^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89796381 156250000 989081024849 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-630393291/10000000000 : ℝ), (1114746801/2000000000 : ℝ), (89796381/156250000 : ℝ)] ![(2979082429959/100000000000000 : ℝ), (1486464572181/3125000000000 : ℝ), (989081024849/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-630393291/10000000000 : ℝ)|^75 ≤ (2979082429959/100000000000000 : ℝ)^59
        have hw : |(-630393291/10000000000 : ℝ)|=(630393291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114746801/2000000000 : ℝ)|^75 ≤ (1486464572181/3125000000000 : ℝ)^59
        have hw : |(1114746801/2000000000 : ℝ)|=(1114746801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89796381/156250000 : ℝ)|^75 ≤ (989081024849/2000000000000 : ℝ)^59
        have hw : |(89796381/156250000 : ℝ)|=(89796381/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5573380663/10000000000 : ℝ)*x 0 + (-620524433/10000000000 : ℝ)*x 1 + (2876363083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5573380663/10000000000 : ℝ)^75 ≤ (47563033130939/100000000000000 : ℝ)^59 := by
    have hnat : (5573380663 : ℕ)^75*100000000000000^59 ≤ 47563033130939^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573380663 10000000000 47563033130939 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620524433/10000000000 : ℝ)^75 ≤ (2919923448897/100000000000000 : ℝ)^59 := by
    have hnat : (620524433 : ℕ)^75*100000000000000^59 ≤ 2919923448897^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620524433 10000000000 2919923448897 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2876363083/5000000000 : ℝ)^75 ≤ (9903408680933/20000000000000 : ℝ)^59 := by
    have hnat : (2876363083 : ℕ)^75*20000000000000^59 ≤ 9903408680933^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876363083 5000000000 9903408680933 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5573380663/10000000000 : ℝ), (-620524433/10000000000 : ℝ), (2876363083/5000000000 : ℝ)] ![(47563033130939/100000000000000 : ℝ), (2919923448897/100000000000000 : ℝ), (9903408680933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5573380663/10000000000 : ℝ)|^75 ≤ (47563033130939/100000000000000 : ℝ)^59
        have hw : |(5573380663/10000000000 : ℝ)|=(5573380663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620524433/10000000000 : ℝ)|^75 ≤ (2919923448897/100000000000000 : ℝ)^59
        have hw : |(-620524433/10000000000 : ℝ)|=(620524433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2876363083/5000000000 : ℝ)|^75 ≤ (9903408680933/20000000000000 : ℝ)^59
        have hw : |(2876363083/5000000000 : ℝ)|=(2876363083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1405857527/2500000000 : ℝ)*x 0 + (1146278323/2000000000 : ℝ)*x 1 + (-568036477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1405857527/2500000000 : ℝ)^75 ≤ (48106642205303/100000000000000 : ℝ)^59 := by
    have hnat : (1405857527 : ℕ)^75*100000000000000^59 ≤ 48106642205303^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405857527 2500000000 48106642205303 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146278323/2000000000 : ℝ)^75 ≤ (49283721710549/100000000000000 : ℝ)^59 := by
    have hnat : (1146278323 : ℕ)^75*100000000000000^59 ≤ 49283721710549^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146278323 2000000000 49283721710549 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568036477/10000000000 : ℝ)^75 ≤ (1304818037539/50000000000000 : ℝ)^59 := by
    have hnat : (568036477 : ℕ)^75*50000000000000^59 ≤ 1304818037539^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568036477 10000000000 1304818037539 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1405857527/2500000000 : ℝ), (1146278323/2000000000 : ℝ), (-568036477/10000000000 : ℝ)] ![(48106642205303/100000000000000 : ℝ), (49283721710549/100000000000000 : ℝ), (1304818037539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1405857527/2500000000 : ℝ)|^75 ≤ (48106642205303/100000000000000 : ℝ)^59
        have hw : |(1405857527/2500000000 : ℝ)|=(1405857527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146278323/2000000000 : ℝ)|^75 ≤ (49283721710549/100000000000000 : ℝ)^59
        have hw : |(1146278323/2000000000 : ℝ)|=(1146278323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568036477/10000000000 : ℝ)|^75 ≤ (1304818037539/50000000000000 : ℝ)^59
        have hw : |(-568036477/10000000000 : ℝ)|=(568036477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1196885477/10000000000 : ℝ)*x 0 + (2950258587/10000000000 : ℝ)*x 1 + (7729564273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1196885477/10000000000 : ℝ)^75 ≤ (6730277366849/100000000000000 : ℝ)^59 := by
    have hnat : (1196885477 : ℕ)^75*100000000000000^59 ≤ 6730277366849^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196885477 10000000000 6730277366849 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2950258587/10000000000 : ℝ)^75 ≤ (5297041002127/25000000000000 : ℝ)^59 := by
    have hnat : (2950258587 : ℕ)^75*25000000000000^59 ≤ 5297041002127^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950258587 10000000000 5297041002127 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7729564273/10000000000 : ℝ)^75 ≤ (72081558614829/100000000000000 : ℝ)^59 := by
    have hnat : (7729564273 : ℕ)^75*100000000000000^59 ≤ 72081558614829^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7729564273 10000000000 72081558614829 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1196885477/10000000000 : ℝ), (2950258587/10000000000 : ℝ), (7729564273/10000000000 : ℝ)] ![(6730277366849/100000000000000 : ℝ), (5297041002127/25000000000000 : ℝ), (72081558614829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1196885477/10000000000 : ℝ)|^75 ≤ (6730277366849/100000000000000 : ℝ)^59
        have hw : |(-1196885477/10000000000 : ℝ)|=(1196885477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2950258587/10000000000 : ℝ)|^75 ≤ (5297041002127/25000000000000 : ℝ)^59
        have hw : |(2950258587/10000000000 : ℝ)|=(2950258587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7729564273/10000000000 : ℝ)|^75 ≤ (72081558614829/100000000000000 : ℝ)^59
        have hw : |(7729564273/10000000000 : ℝ)|=(7729564273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3597300831/10000000000 : ℝ)*x 0 + (-172046703/10000000000 : ℝ)*x 1 + (7736679309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3597300831/10000000000 : ℝ)^75 ≤ (27262374255221/100000000000000 : ℝ)^59 := by
    have hnat : (3597300831 : ℕ)^75*100000000000000^59 ≤ 27262374255221^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3597300831 10000000000 27262374255221 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172046703/10000000000 : ℝ)^75 ≤ (571712343951/100000000000000 : ℝ)^59 := by
    have hnat : (172046703 : ℕ)^75*100000000000000^59 ≤ 571712343951^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172046703 10000000000 571712343951 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7736679309/10000000000 : ℝ)^75 ≤ (9020739174417/12500000000000 : ℝ)^59 := by
    have hnat : (7736679309 : ℕ)^75*12500000000000^59 ≤ 9020739174417^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7736679309 10000000000 9020739174417 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3597300831/10000000000 : ℝ), (-172046703/10000000000 : ℝ), (7736679309/10000000000 : ℝ)] ![(27262374255221/100000000000000 : ℝ), (571712343951/100000000000000 : ℝ), (9020739174417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3597300831/10000000000 : ℝ)|^75 ≤ (27262374255221/100000000000000 : ℝ)^59
        have hw : |(3597300831/10000000000 : ℝ)|=(3597300831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172046703/10000000000 : ℝ)|^75 ≤ (571712343951/100000000000000 : ℝ)^59
        have hw : |(-172046703/10000000000 : ℝ)|=(172046703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7736679309/10000000000 : ℝ)|^75 ≤ (9020739174417/12500000000000 : ℝ)^59
        have hw : |(7736679309/10000000000 : ℝ)|=(7736679309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1710144169/5000000000 : ℝ)*x 0 + (7911857509/10000000000 : ℝ)*x 1 + (-69919613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1710144169/5000000000 : ℝ)^75 ≤ (25568593990153/100000000000000 : ℝ)^59 := by
    have hnat : (1710144169 : ℕ)^75*100000000000000^59 ≤ 25568593990153^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710144169 5000000000 25568593990153 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7911857509/10000000000 : ℝ)^75 ≤ (7424940092621/10000000000000 : ℝ)^59 := by
    have hnat : (7911857509 : ℕ)^75*10000000000000^59 ≤ 7424940092621^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7911857509 10000000000 7424940092621 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69919613/10000000000 : ℝ)^75 ≤ (36401014729/20000000000000 : ℝ)^59 := by
    have hnat : (69919613 : ℕ)^75*20000000000000^59 ≤ 36401014729^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69919613 10000000000 36401014729 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1710144169/5000000000 : ℝ), (7911857509/10000000000 : ℝ), (-69919613/10000000000 : ℝ)] ![(25568593990153/100000000000000 : ℝ), (7424940092621/10000000000000 : ℝ), (36401014729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1710144169/5000000000 : ℝ)|^75 ≤ (25568593990153/100000000000000 : ℝ)^59
        have hw : |(1710144169/5000000000 : ℝ)|=(1710144169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7911857509/10000000000 : ℝ)|^75 ≤ (7424940092621/10000000000000 : ℝ)^59
        have hw : |(7911857509/10000000000 : ℝ)|=(7911857509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69919613/10000000000 : ℝ)|^75 ≤ (36401014729/20000000000000 : ℝ)^59
        have hw : |(-69919613/10000000000 : ℝ)|=(69919613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3495821329/10000000000 : ℝ)*x 0 + (3534400743/5000000000 : ℝ)*x 1 + (310552939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3495821329/10000000000 : ℝ)^75 ≤ (2628850975777/10000000000000 : ℝ)^59 := by
    have hnat : (3495821329 : ℕ)^75*10000000000000^59 ≤ 2628850975777^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495821329 10000000000 2628850975777 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3534400743/5000000000 : ℝ)^75 ≤ (64341385011533/100000000000000 : ℝ)^59 := by
    have hnat : (3534400743 : ℕ)^75*100000000000000^59 ≤ 64341385011533^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3534400743 5000000000 64341385011533 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310552939/2000000000 : ℝ)^75 ≤ (4685052610463/50000000000000 : ℝ)^59 := by
    have hnat : (310552939 : ℕ)^75*50000000000000^59 ≤ 4685052610463^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310552939 2000000000 4685052610463 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3495821329/10000000000 : ℝ), (3534400743/5000000000 : ℝ), (310552939/2000000000 : ℝ)] ![(2628850975777/10000000000000 : ℝ), (64341385011533/100000000000000 : ℝ), (4685052610463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3495821329/10000000000 : ℝ)|^75 ≤ (2628850975777/10000000000000 : ℝ)^59
        have hw : |(3495821329/10000000000 : ℝ)|=(3495821329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3534400743/5000000000 : ℝ)|^75 ≤ (64341385011533/100000000000000 : ℝ)^59
        have hw : |(3534400743/5000000000 : ℝ)|=(3534400743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310552939/2000000000 : ℝ)|^75 ≤ (4685052610463/50000000000000 : ℝ)^59
        have hw : |(310552939/2000000000 : ℝ)|=(310552939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-15639543/1000000000 : ℝ)*x 0 + (440162361/1250000000 : ℝ)*x 1 + (1950919493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15639543/1000000000 : ℝ)^75 ≤ (126608282349/25000000000000 : ℝ)^59 := by
    have hnat : (15639543 : ℕ)^75*25000000000000^59 ≤ 126608282349^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15639543 1000000000 126608282349 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440162361/1250000000 : ℝ)^75 ≤ (1326614879071/5000000000000 : ℝ)^59 := by
    have hnat : (440162361 : ℕ)^75*5000000000000^59 ≤ 1326614879071^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440162361 1250000000 1326614879071 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950919493/2500000000 : ℝ)^75 ≤ (72961269274859/100000000000000 : ℝ)^59 := by
    have hnat : (1950919493 : ℕ)^75*100000000000000^59 ≤ 72961269274859^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950919493 2500000000 72961269274859 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15639543/1000000000 : ℝ), (440162361/1250000000 : ℝ), (1950919493/2500000000 : ℝ)] ![(126608282349/25000000000000 : ℝ), (1326614879071/5000000000000 : ℝ), (72961269274859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15639543/1000000000 : ℝ)|^75 ≤ (126608282349/25000000000000 : ℝ)^59
        have hw : |(-15639543/1000000000 : ℝ)|=(15639543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440162361/1250000000 : ℝ)|^75 ≤ (1326614879071/5000000000000 : ℝ)^59
        have hw : |(440162361/1250000000 : ℝ)|=(440162361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1950919493/2500000000 : ℝ)|^75 ≤ (72961269274859/100000000000000 : ℝ)^59
        have hw : |(1950919493/2500000000 : ℝ)|=(1950919493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (177603519/625000000 : ℝ)*x 0 + (-239967753/2000000000 : ℝ)*x 1 + (1952720947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177603519/625000000 : ℝ)^75 ≤ (157825652279/781250000000 : ℝ)^59 := by
    have hnat : (177603519 : ℕ)^75*781250000000^59 ≤ 157825652279^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177603519 625000000 157825652279 781250000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239967753/2000000000 : ℝ)^75 ≤ (1687848693701/25000000000000 : ℝ)^59 := by
    have hnat : (239967753 : ℕ)^75*25000000000000^59 ≤ 1687848693701^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239967753 2000000000 1687848693701 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952720947/2500000000 : ℝ)^75 ≤ (36523460865529/50000000000000 : ℝ)^59 := by
    have hnat : (1952720947 : ℕ)^75*50000000000000^59 ≤ 36523460865529^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952720947 2500000000 36523460865529 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(177603519/625000000 : ℝ), (-239967753/2000000000 : ℝ), (1952720947/2500000000 : ℝ)] ![(157825652279/781250000000 : ℝ), (1687848693701/25000000000000 : ℝ), (36523460865529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(177603519/625000000 : ℝ)|^75 ≤ (157825652279/781250000000 : ℝ)^59
        have hw : |(177603519/625000000 : ℝ)|=(177603519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239967753/2000000000 : ℝ)|^75 ≤ (1687848693701/25000000000000 : ℝ)^59
        have hw : |(-239967753/2000000000 : ℝ)|=(239967753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1952720947/2500000000 : ℝ)|^75 ≤ (36523460865529/50000000000000 : ℝ)^59
        have hw : |(1952720947/2500000000 : ℝ)|=(1952720947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1532768081/2000000000 : ℝ)*x 0 + (3718455271/10000000000 : ℝ)*x 1 + (-18614881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1532768081/2000000000 : ℝ)^75 ≤ (35651671913121/50000000000000 : ℝ)^59 := by
    have hnat : (1532768081 : ℕ)^75*50000000000000^59 ≤ 35651671913121^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532768081 2000000000 35651671913121 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3718455271/10000000000 : ℝ)^75 ≤ (28434835105197/100000000000000 : ℝ)^59 := by
    have hnat : (3718455271 : ℕ)^75*100000000000000^59 ≤ 28434835105197^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718455271 10000000000 28434835105197 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18614881/2000000000 : ℝ)^75 ≤ (261821061141/100000000000000 : ℝ)^59 := by
    have hnat : (18614881 : ℕ)^75*100000000000000^59 ≤ 261821061141^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18614881 2000000000 261821061141 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1532768081/2000000000 : ℝ), (3718455271/10000000000 : ℝ), (-18614881/2000000000 : ℝ)] ![(35651671913121/50000000000000 : ℝ), (28434835105197/100000000000000 : ℝ), (261821061141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1532768081/2000000000 : ℝ)|^75 ≤ (35651671913121/50000000000000 : ℝ)^59
        have hw : |(1532768081/2000000000 : ℝ)|=(1532768081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3718455271/10000000000 : ℝ)|^75 ≤ (28434835105197/100000000000000 : ℝ)^59
        have hw : |(3718455271/10000000000 : ℝ)|=(3718455271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18614881/2000000000 : ℝ)|^75 ≤ (261821061141/100000000000000 : ℝ)^59
        have hw : |(-18614881/2000000000 : ℝ)|=(18614881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (749276411/1000000000 : ℝ)*x 0 + (1488965409/5000000000 : ℝ)*x 1 + (61602069/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749276411/1000000000 : ℝ)^75 ≤ (34643095498569/50000000000000 : ℝ)^59 := by
    have hnat : (749276411 : ℕ)^75*50000000000000^59 ≤ 34643095498569^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749276411 1000000000 34643095498569 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1488965409/5000000000 : ℝ)^75 ≤ (10720557797029/50000000000000 : ℝ)^59 := by
    have hnat : (1488965409 : ℕ)^75*50000000000000^59 ≤ 10720557797029^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488965409 5000000000 10720557797029 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61602069/400000000 : ℝ)^75 ≤ (1854538676803/20000000000000 : ℝ)^59 := by
    have hnat : (61602069 : ℕ)^75*20000000000000^59 ≤ 1854538676803^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61602069 400000000 1854538676803 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(749276411/1000000000 : ℝ), (1488965409/5000000000 : ℝ), (61602069/400000000 : ℝ)] ![(34643095498569/50000000000000 : ℝ), (10720557797029/50000000000000 : ℝ), (1854538676803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(749276411/1000000000 : ℝ)|^75 ≤ (34643095498569/50000000000000 : ℝ)^59
        have hw : |(749276411/1000000000 : ℝ)|=(749276411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1488965409/5000000000 : ℝ)|^75 ≤ (10720557797029/50000000000000 : ℝ)^59
        have hw : |(1488965409/5000000000 : ℝ)|=(1488965409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(61602069/400000000 : ℝ)|^75 ≤ (1854538676803/20000000000000 : ℝ)^59
        have hw : |(61602069/400000000 : ℝ)|=(61602069/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-158722411/10000000000 : ℝ)*x 0 + (875656267/1250000000 : ℝ)*x 1 + (892932783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158722411/10000000000 : ℝ)^75 ≤ (10320618851/2000000000000 : ℝ)^59 := by
    have hnat : (158722411 : ℕ)^75*2000000000000^59 ≤ 10320618851^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158722411 10000000000 10320618851 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (875656267/1250000000 : ℝ)^75 ≤ (63606959514649/100000000000000 : ℝ)^59 := by
    have hnat : (875656267 : ℕ)^75*100000000000000^59 ≤ 63606959514649^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875656267 1250000000 63606959514649 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892932783/2000000000 : ℝ)^75 ≤ (35877009521711/100000000000000 : ℝ)^59 := by
    have hnat : (892932783 : ℕ)^75*100000000000000^59 ≤ 35877009521711^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892932783 2000000000 35877009521711 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158722411/10000000000 : ℝ), (875656267/1250000000 : ℝ), (892932783/2000000000 : ℝ)] ![(10320618851/2000000000000 : ℝ), (63606959514649/100000000000000 : ℝ), (35877009521711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158722411/10000000000 : ℝ)|^75 ≤ (10320618851/2000000000000 : ℝ)^59
        have hw : |(-158722411/10000000000 : ℝ)|=(158722411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(875656267/1250000000 : ℝ)|^75 ≤ (63606959514649/100000000000000 : ℝ)^59
        have hw : |(875656267/1250000000 : ℝ)|=(875656267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(892932783/2000000000 : ℝ)|^75 ≤ (35877009521711/100000000000000 : ℝ)^59
        have hw : |(892932783/2000000000 : ℝ)|=(892932783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7650260119/10000000000 : ℝ)*x 0 + (-64745857/10000000000 : ℝ)*x 1 + (748980553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7650260119/10000000000 : ℝ)^75 ≤ (35571384546903/50000000000000 : ℝ)^59 := by
    have hnat : (7650260119 : ℕ)^75*50000000000000^59 ≤ 35571384546903^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7650260119 10000000000 35571384546903 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64745857/10000000000 : ℝ)^75 ≤ (165060194373/100000000000000 : ℝ)^59 := by
    have hnat : (64745857 : ℕ)^75*100000000000000^59 ≤ 165060194373^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64745857 10000000000 165060194373 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748980553/2000000000 : ℝ)^75 ≤ (5738434137957/20000000000000 : ℝ)^59 := by
    have hnat : (748980553 : ℕ)^75*20000000000000^59 ≤ 5738434137957^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748980553 2000000000 5738434137957 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7650260119/10000000000 : ℝ), (-64745857/10000000000 : ℝ), (748980553/2000000000 : ℝ)] ![(35571384546903/50000000000000 : ℝ), (165060194373/100000000000000 : ℝ), (5738434137957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7650260119/10000000000 : ℝ)|^75 ≤ (35571384546903/50000000000000 : ℝ)^59
        have hw : |(7650260119/10000000000 : ℝ)|=(7650260119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64745857/10000000000 : ℝ)|^75 ≤ (165060194373/100000000000000 : ℝ)^59
        have hw : |(-64745857/10000000000 : ℝ)|=(64745857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748980553/2000000000 : ℝ)|^75 ≤ (5738434137957/20000000000000 : ℝ)^59
        have hw : |(748980553/2000000000 : ℝ)|=(748980553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (271406017/1000000000 : ℝ)*x 0 + (1586142071/2000000000 : ℝ)*x 1 + (-232062089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271406017/1000000000 : ℝ)^75 ≤ (4763923300963/25000000000000 : ℝ)^59 := by
    have hnat : (271406017 : ℕ)^75*25000000000000^59 ≤ 4763923300963^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271406017 1000000000 4763923300963 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1586142071/2000000000 : ℝ)^75 ≤ (74474379357987/100000000000000 : ℝ)^59 := by
    have hnat : (1586142071 : ℕ)^75*100000000000000^59 ≤ 74474379357987^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586142071 2000000000 74474379357987 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232062089/2000000000 : ℝ)^75 ≤ (6469927423453/100000000000000 : ℝ)^59 := by
    have hnat : (232062089 : ℕ)^75*100000000000000^59 ≤ 6469927423453^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232062089 2000000000 6469927423453 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271406017/1000000000 : ℝ), (1586142071/2000000000 : ℝ), (-232062089/2000000000 : ℝ)] ![(4763923300963/25000000000000 : ℝ), (74474379357987/100000000000000 : ℝ), (6469927423453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271406017/1000000000 : ℝ)|^75 ≤ (4763923300963/25000000000000 : ℝ)^59
        have hw : |(271406017/1000000000 : ℝ)|=(271406017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1586142071/2000000000 : ℝ)|^75 ≤ (74474379357987/100000000000000 : ℝ)^59
        have hw : |(1586142071/2000000000 : ℝ)|=(1586142071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232062089/2000000000 : ℝ)|^75 ≤ (6469927423453/100000000000000 : ℝ)^59
        have hw : |(-232062089/2000000000 : ℝ)|=(232062089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1527420771/2000000000 : ℝ)*x 0 + (1228913197/5000000000 : ℝ)*x 1 + (1912760903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1527420771/2000000000 : ℝ)^75 ≤ (70987281740531/100000000000000 : ℝ)^59 := by
    have hnat : (1527420771 : ℕ)^75*100000000000000^59 ≤ 70987281740531^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1527420771 2000000000 70987281740531 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1228913197/5000000000 : ℝ)^75 ≤ (16798749493501/100000000000000 : ℝ)^59 := by
    have hnat : (1228913197 : ℕ)^75*100000000000000^59 ≤ 16798749493501^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228913197 5000000000 16798749493501 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912760903/10000000000 : ℝ)^75 ≤ (3053492187281/25000000000000 : ℝ)^59 := by
    have hnat : (1912760903 : ℕ)^75*25000000000000^59 ≤ 3053492187281^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912760903 10000000000 3053492187281 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1527420771/2000000000 : ℝ), (1228913197/5000000000 : ℝ), (1912760903/10000000000 : ℝ)] ![(70987281740531/100000000000000 : ℝ), (16798749493501/100000000000000 : ℝ), (3053492187281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1527420771/2000000000 : ℝ)|^75 ≤ (70987281740531/100000000000000 : ℝ)^59
        have hw : |(1527420771/2000000000 : ℝ)|=(1527420771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1228913197/5000000000 : ℝ)|^75 ≤ (16798749493501/100000000000000 : ℝ)^59
        have hw : |(1228913197/5000000000 : ℝ)|=(1228913197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1912760903/10000000000 : ℝ)|^75 ≤ (3053492187281/25000000000000 : ℝ)^59
        have hw : |(1912760903/10000000000 : ℝ)|=(1912760903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314063_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((40639/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40639/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16173/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16173/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39319/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39319/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63549/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61031/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61031/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (40639/50000 : ℝ) ^ (37/8 : ℝ) ≤ (19168810688997135321/50000000000000000000 : ℝ) := by
    have hpowers : (40639/50000 : ℝ)^37 ≤ (19168810688997135321/50000000000000000000 : ℝ)^8 := by
      have hnat : (40639 : ℕ)^37*50000000000000000000^8 ≤ 19168810688997135321^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40639 50000 19168810688997135321 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40639/50000 : ℝ)) (X := (19168810688997135321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (69168810688997135321/50000000000000000000 : ℝ) ≤ (335215121168607/312500000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (69168810688997135321/50000000000000000000 : ℝ)^8 ≤ (335215121168607/312500000000000 : ℝ)^37 := by
      have hnat : (69168810688997135321 : ℕ)^8*312500000000000^37 ≤ 335215121168607^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69168810688997135321 50000000000000000000 335215121168607 312500000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (335215121168607/312500000000000 : ℝ)) (X := (69168810688997135321/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (44168810688997135321/25000000000000000000 : ℝ) ≤ (1130949971258893/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (44168810688997135321/25000000000000000000 : ℝ)^8 ≤ (1130949971258893/1000000000000000 : ℝ)^37 := by
      have hnat : (44168810688997135321 : ℕ)^8*1000000000000000^37 ≤ 1130949971258893^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44168810688997135321 25000000000000000000 1130949971258893 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1130949971258893/1000000000000000 : ℝ)) (X := (44168810688997135321/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(22715121168607/253993750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(291307917596753/4063900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (40639/50000 : ℝ)) (alpha := (22715121168607/253993750000000 : ℝ)) (beta := (291307917596753/4063900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40639/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(22715121168607/253993750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(291307917596753/4063900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16173/20000 : ℝ) ^ (37/8 : ℝ) ≤ (18722452489116800451/50000000000000000000 : ℝ) := by
    have hpowers : (16173/20000 : ℝ)^37 ≤ (18722452489116800451/50000000000000000000 : ℝ)^8 := by
      have hnat : (16173 : ℕ)^37*50000000000000000000^8 ≤ 18722452489116800451^8*20000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16173 20000 18722452489116800451 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16173/20000 : ℝ)) (X := (18722452489116800451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (68722452489116800451/50000000000000000000 : ℝ) ≤ (10711878870667253/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (68722452489116800451/50000000000000000000 : ℝ)^8 ≤ (10711878870667253/10000000000000000 : ℝ)^37 := by
      have hnat : (68722452489116800451 : ℕ)^8*10000000000000000^37 ≤ 10711878870667253^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68722452489116800451 50000000000000000000 10711878870667253 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10711878870667253/10000000000000000 : ℝ)) (X := (68722452489116800451/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (43722452489116800451/25000000000000000000 : ℝ) ≤ (2256937946688809/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (43722452489116800451/25000000000000000000 : ℝ)^8 ≤ (2256937946688809/2000000000000000 : ℝ)^37 := by
      have hnat : (43722452489116800451 : ℕ)^8*2000000000000000^37 ≤ 2256937946688809^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43722452489116800451 25000000000000000000 2256937946688809 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2256937946688809/2000000000000000 : ℝ)) (X := (43722452489116800451/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(711878870667253/8086500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(71601357847099/1010812500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (16173/20000 : ℝ)) (alpha := (711878870667253/8086500000000000 : ℝ)) (beta := (71601357847099/1010812500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (16173/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(711878870667253/8086500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(71601357847099/1010812500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (39319/50000 : ℝ) ^ (37/8 : ℝ) ≤ (32907896706135137789/100000000000000000000 : ℝ) := by
    have hpowers : (39319/50000 : ℝ)^37 ≤ (32907896706135137789/100000000000000000000 : ℝ)^8 := by
      have hnat : (39319 : ℕ)^37*100000000000000000000^8 ≤ 32907896706135137789^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39319 50000 32907896706135137789 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39319/50000 : ℝ)) (X := (32907896706135137789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (132907896706135137789/100000000000000000000 : ℝ) ≤ (10634416933892101/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (132907896706135137789/100000000000000000000 : ℝ)^8 ≤ (10634416933892101/10000000000000000 : ℝ)^37 := by
      have hnat : (132907896706135137789 : ℕ)^8*10000000000000000^37 ≤ 10634416933892101^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132907896706135137789 100000000000000000000 10634416933892101 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10634416933892101/10000000000000000 : ℝ)) (X := (132907896706135137789/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (82907896706135137789/50000000000000000000 : ℝ) ≤ (11155439356737473/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (82907896706135137789/50000000000000000000 : ℝ)^8 ≤ (11155439356737473/10000000000000000 : ℝ)^37 := by
      have hnat : (82907896706135137789 : ℕ)^8*10000000000000000^37 ≤ 11155439356737473^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82907896706135137789 50000000000000000000 11155439356737473 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11155439356737473/10000000000000000 : ℝ)) (X := (82907896706135137789/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(634416933892101/7863800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(18607943673049/280850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (39319/50000 : ℝ)) (alpha := (634416933892101/7863800000000000 : ℝ)) (beta := (18607943673049/280850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39319/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(634416933892101/7863800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(18607943673049/280850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-630393291/10000000000 : ℝ)*X 0 0+(1114746801/2000000000 : ℝ)*X 0 1+(89796381/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5573380663/10000000000 : ℝ)*X 1 0+(-620524433/10000000000 : ℝ)*X 1 1+(2876363083/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1405857527/2500000000 : ℝ)*X 2 0+(1146278323/2000000000 : ℝ)*X 2 1+(-568036477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1196885477/10000000000 : ℝ)*X 0 0+(2950258587/10000000000 : ℝ)*X 0 1+(7729564273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3597300831/10000000000 : ℝ)*X 1 0+(-172046703/10000000000 : ℝ)*X 1 1+(7736679309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1710144169/5000000000 : ℝ)*X 2 0+(7911857509/10000000000 : ℝ)*X 2 1+(-69919613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3495821329/10000000000 : ℝ)*X 0 0+(3534400743/5000000000 : ℝ)*X 0 1+(310552939/2000000000 : ℝ)*X 0 2+(3495821329/10000000000 : ℝ)*X 1 0+(3534400743/5000000000 : ℝ)*X 1 1+(310552939/2000000000 : ℝ)*X 1 2+(3495821329/10000000000 : ℝ)*X 2 0+(3534400743/5000000000 : ℝ)*X 2 1+(310552939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-15639543/1000000000 : ℝ)*X 0 0+(440162361/1250000000 : ℝ)*X 0 1+(1950919493/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((177603519/625000000 : ℝ)*X 1 0+(-239967753/2000000000 : ℝ)*X 1 1+(1952720947/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1532768081/2000000000 : ℝ)*X 2 0+(3718455271/10000000000 : ℝ)*X 2 1+(-18614881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((749276411/1000000000 : ℝ)*X 0 0+(1488965409/5000000000 : ℝ)*X 0 1+(61602069/400000000 : ℝ)*X 0 2+(749276411/1000000000 : ℝ)*X 1 0+(1488965409/5000000000 : ℝ)*X 1 1+(61602069/400000000 : ℝ)*X 1 2+(749276411/1000000000 : ℝ)*X 2 0+(1488965409/5000000000 : ℝ)*X 2 1+(61602069/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-158722411/10000000000 : ℝ)*X 0 0+(875656267/1250000000 : ℝ)*X 0 1+(892932783/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7650260119/10000000000 : ℝ)*X 1 0+(-64745857/10000000000 : ℝ)*X 1 1+(748980553/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((271406017/1000000000 : ℝ)*X 2 0+(1586142071/2000000000 : ℝ)*X 2 1+(-232062089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1527420771/2000000000 : ℝ)*X 0 0+(1228913197/5000000000 : ℝ)*X 0 1+(1912760903/10000000000 : ℝ)*X 0 2+(1527420771/2000000000 : ℝ)*X 1 0+(1228913197/5000000000 : ℝ)*X 1 1+(1912760903/10000000000 : ℝ)*X 1 2+(1527420771/2000000000 : ℝ)*X 2 0+(1228913197/5000000000 : ℝ)*X 2 1+(1912760903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((63337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (182156665920603168100024247/35328121500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14482473459/20000000000 : ℝ)*(base7) + (280529/100000000000 : ℝ)*(base23) + (33693/50000000000 : ℝ)*(base50) + (6593277811/125000000000 : ℝ)*(base60) + (1855491231549/1000000000000 : ℝ)*(major_s1_0) + (1855491231549/1000000000000 : ℝ)*(major_s1_1) + (1855491231549/1000000000000 : ℝ)*(major_s1_2) + (2532189/1000000000000 : ℝ)*(sp_s1_0) + (247887/100000000000 : ℝ)*(sp_s1_1) + (2208438761361/1000000000000 : ℝ)*(sp_s1_7) + (1104229859489/500000000000 : ℝ)*(sp_s1_8) + (2208459392557/1000000000000 : ℝ)*(sp_s1_9) + (1802465054343/1000000000000 : ℝ)*(sp_s1_13) + (10452149/500000000000 : ℝ)*(sp_s1_14) + (1078341381393/1000000000000 : ℝ)*(f.failure) + (2208462197847/1000000000000 : ℝ)*(f.sum) + (14107220561753022343/211968729000000000000000000000000 : ℝ)*base62 + (194286619593889/280850000000000000000000000 : ℝ)*base64 + (142058242571641/673875000000000000000000000 : ℝ)*base66 + (806707228138051/7863800000000000000000000000 : ℝ)*base68 + (4363090875284776823/11413463150000000000000000000000 : ℝ)*base70 + (2114728035294333/4063900000000000000000000000 : ℝ)*base72 + (675380156970851/2695500000000000000000000000 : ℝ)*base74 + (101965348153799/2031950000000000000000000000 : ℝ)*base77 + (35277043340363020439/109542424500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (12117/100000000000000000 : ℝ)*base87 + (12117/100000000000000000 : ℝ)*base89 + (12117/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63549/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30015104853350310018007973180413/2153549294457750000000000000000000000 : ℝ) := by norm_num
    linear_combination (742213650289/1000000000000 : ℝ)*(base7) + (511711/1000000000000 : ℝ)*(base49) + (893624716069/500000000000 : ℝ)*(major_s1_0) + (893624716069/500000000000 : ℝ)*(major_s1_1) + (893624716069/500000000000 : ℝ)*(major_s1_2) + (1773179/250000000000 : ℝ)*(sp_s1_0) + (15360661/1000000000000 : ℝ)*(sp_s1_1) + (38118911/500000000000 : ℝ)*(sp_s1_8) + (84041191201/40000000000 : ℝ)*(sp_s1_14) + (131309180083/62500000000 : ℝ)*(sp_s1_15) + (2101038479811/1000000000000 : ℝ)*(sp_s1_16) + (1780823818833/1000000000000 : ℝ)*(sp_s1_20) + (1607069/1000000000000 : ℝ)*(sp_s1_21) + (35829007/500000000000 : ℝ)*(sp_s1_27) + (1038681826557/1000000000000 : ℝ)*(f.failure) + (2101038479811/1000000000000 : ℝ)*(f.sum) + (222955341504530472499/317953093500000000000000000000000 : ℝ)*base62 + (2616705361309/35106250000000000000000000 : ℝ)*base65 + (1447997280164599/2021625000000000000000000000 : ℝ)*base67 + (3098798852521061/3931900000000000000000000000 : ℝ)*base68 + (2160422562111932071/11413463150000000000000000000000 : ℝ)*base70 + (165148408154567/507987500000000000000000000 : ℝ)*base72 + (1817789207312209/2021625000000000000000000000 : ℝ)*base74 + (658175488723617/2031950000000000000000000000 : ℝ)*base76 + (33640195370225965277/164313636750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (36433/100000000000000000 : ℝ)*base87 + (36433/100000000000000000 : ℝ)*base89 + (36433/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61031/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61031/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6716337313547563826764925763497/717849764819250000000000000000000000 : ℝ) := by norm_num
    linear_combination (733907673757/1000000000000 : ℝ)*(base7) + (5816940487/40000000000 : ℝ)*(base40) + (342447/500000000000 : ℝ)*(base49) + (214105777383/125000000000 : ℝ)*(major_s1_0) + (214105777383/125000000000 : ℝ)*(major_s1_1) + (214105777383/125000000000 : ℝ)*(major_s1_2) + (1113037/100000000000 : ℝ)*(sp_s1_1) + (3319107/250000000000 : ℝ)*(sp_s1_2) + (24151399/500000000000 : ℝ)*(sp_s1_9) + (4305073/500000000000 : ℝ)*(sp_s1_20) + (2000339391309/1000000000000 : ℝ)*(sp_s1_21) + (2000328260939/1000000000000 : ℝ)*(sp_s1_22) + (2000277812083/1000000000000 : ℝ)*(sp_s1_23) + (1729340554561/1000000000000 : ℝ)*(sp_s1_27) + (995441490951/1000000000000 : ℝ)*(f.failure) + (2000339391309/1000000000000 : ℝ)*(f.sum) + (8343375779603145569/26496091125000000000000000000000 : ℝ)*base63 + (31795784303413/140425000000000000000000000 : ℝ)*base65 + (22545144041047/84234375000000000000000000 : ℝ)*base66 + (184911943601649/491487500000000000000000000 : ℝ)*base69 + (6290446846148813997/11413463150000000000000000000000 : ℝ)*base71 + (42113693038883/253993750000000000000000000 : ℝ)*base72 + (529904632587457/1347750000000000000000000000 : ℝ)*base75 + (1433510621054629/2031950000000000000000000000 : ℝ)*base77 + (11414987321354802337/13692803062500000000000000000000 : ℝ)*base78 + (47619/100000000000000000 : ℝ)*base87 + (47619/100000000000000000 : ℝ)*base89 + (47619/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((40639/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40639/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16173/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16173/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39319/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39319/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63549/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61031/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61031/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314063_s1 p hpa hpb X hX hprev0

#print axioms solution

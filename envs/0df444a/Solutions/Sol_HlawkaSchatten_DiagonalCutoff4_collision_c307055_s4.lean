-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307055_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:13:34.178705+00:00
-- url     : https://prove2.me/submissions/2f100dd5-1073-4c23-8019-ecb6b13f6369

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
theorem collision_support_c307055_s4_s4_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014096143/10000000000 : ℝ)*x 0 + (1155853367/2000000000 : ℝ)*x 1 + (1213906697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014096143/10000000000 : ℝ)^17 ≤ (6150650252327/50000000000000 : ℝ)^13 := by
    have hnat : (2014096143 : ℕ)^17*50000000000000^13 ≤ 6150650252327^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014096143 10000000000 6150650252327 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155853367/2000000000 : ℝ)^17 ≤ (24410283708969/50000000000000 : ℝ)^13 := by
    have hnat : (1155853367 : ℕ)^17*50000000000000^13 ≤ 24410283708969^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155853367 2000000000 24410283708969 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213906697/2500000000 : ℝ)^17 ≤ (38878132059717/100000000000000 : ℝ)^13 := by
    have hnat : (1213906697 : ℕ)^17*100000000000000^13 ≤ 38878132059717^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213906697 2500000000 38878132059717 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014096143/10000000000 : ℝ), (1155853367/2000000000 : ℝ), (1213906697/2500000000 : ℝ)] ![(6150650252327/50000000000000 : ℝ), (24410283708969/50000000000000 : ℝ), (38878132059717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014096143/10000000000 : ℝ)|^17 ≤ (6150650252327/50000000000000 : ℝ)^13
        have hw : |(-2014096143/10000000000 : ℝ)|=(2014096143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155853367/2000000000 : ℝ)|^17 ≤ (24410283708969/50000000000000 : ℝ)^13
        have hw : |(1155853367/2000000000 : ℝ)|=(1155853367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1213906697/2500000000 : ℝ)|^17 ≤ (38878132059717/100000000000000 : ℝ)^13
        have hw : |(1213906697/2500000000 : ℝ)|=(1213906697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1202651167/2500000000 : ℝ)*x 0 + (5810183579/10000000000 : ℝ)*x 1 + (-203021747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1202651167/2500000000 : ℝ)^17 ≤ (38407403755611/100000000000000 : ℝ)^13 := by
    have hnat : (1202651167 : ℕ)^17*100000000000000^13 ≤ 38407403755611^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202651167 2500000000 38407403755611 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5810183579/10000000000 : ℝ)^17 ≤ (49162378578421/100000000000000 : ℝ)^13 := by
    have hnat : (5810183579 : ℕ)^17*100000000000000^13 ≤ 49162378578421^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5810183579 10000000000 49162378578421 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203021747/1000000000 : ℝ)^17 ≤ (6215108824103/50000000000000 : ℝ)^13 := by
    have hnat : (203021747 : ℕ)^17*50000000000000^13 ≤ 6215108824103^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203021747 1000000000 6215108824103 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1202651167/2500000000 : ℝ), (5810183579/10000000000 : ℝ), (-203021747/1000000000 : ℝ)] ![(38407403755611/100000000000000 : ℝ), (49162378578421/100000000000000 : ℝ), (6215108824103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1202651167/2500000000 : ℝ)|^17 ≤ (38407403755611/100000000000000 : ℝ)^13
        have hw : |(1202651167/2500000000 : ℝ)|=(1202651167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5810183579/10000000000 : ℝ)|^17 ≤ (49162378578421/100000000000000 : ℝ)^13
        have hw : |(5810183579/10000000000 : ℝ)|=(5810183579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203021747/1000000000 : ℝ)|^17 ≤ (6215108824103/50000000000000 : ℝ)^13
        have hw : |(-203021747/1000000000 : ℝ)|=(203021747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (244363039/400000000 : ℝ)*x 0 + (4000619651/10000000000 : ℝ)*x 1 + (104683689/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244363039/400000000 : ℝ)^17 ≤ (3280966977863/6250000000000 : ℝ)^13 := by
    have hnat : (244363039 : ℕ)^17*6250000000000^13 ≤ 3280966977863^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244363039 400000000 3280966977863 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4000619651/10000000000 : ℝ)^17 ≤ (30179002672777/100000000000000 : ℝ)^13 := by
    have hnat : (4000619651 : ℕ)^17*100000000000000^13 ≤ 30179002672777^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000619651 10000000000 30179002672777 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104683689/400000000 : ℝ)^17 ≤ (3465105133211/20000000000000 : ℝ)^13 := by
    have hnat : (104683689 : ℕ)^17*20000000000000^13 ≤ 3465105133211^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104683689 400000000 3465105133211 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(244363039/400000000 : ℝ), (4000619651/10000000000 : ℝ), (104683689/400000000 : ℝ)] ![(3280966977863/6250000000000 : ℝ), (30179002672777/100000000000000 : ℝ), (3465105133211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(244363039/400000000 : ℝ)|^17 ≤ (3280966977863/6250000000000 : ℝ)^13
        have hw : |(244363039/400000000 : ℝ)|=(244363039/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4000619651/10000000000 : ℝ)|^17 ≤ (30179002672777/100000000000000 : ℝ)^13
        have hw : |(4000619651/10000000000 : ℝ)|=(4000619651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104683689/400000000 : ℝ)|^17 ≤ (3465105133211/20000000000000 : ℝ)^13
        have hw : |(104683689/400000000 : ℝ)|=(104683689/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1577562693/10000000000 : ℝ)*x 0 + (4919658581/10000000000 : ℝ)*x 1 + (3010708531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1577562693/10000000000 : ℝ)^17 ≤ (4468721467319/50000000000000 : ℝ)^13 := by
    have hnat : (1577562693 : ℕ)^17*50000000000000^13 ≤ 4468721467319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577562693 10000000000 4468721467319 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4919658581/10000000000 : ℝ)^17 ≤ (19774965150411/50000000000000 : ℝ)^13 := by
    have hnat : (4919658581 : ℕ)^17*50000000000000^13 ≤ 19774965150411^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4919658581 10000000000 19774965150411 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010708531/5000000000 : ℝ)^17 ≤ (12878156688099/25000000000000 : ℝ)^13 := by
    have hnat : (3010708531 : ℕ)^17*25000000000000^13 ≤ 12878156688099^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010708531 5000000000 12878156688099 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1577562693/10000000000 : ℝ), (4919658581/10000000000 : ℝ), (3010708531/5000000000 : ℝ)] ![(4468721467319/50000000000000 : ℝ), (19774965150411/50000000000000 : ℝ), (12878156688099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1577562693/10000000000 : ℝ)|^17 ≤ (4468721467319/50000000000000 : ℝ)^13
        have hw : |(-1577562693/10000000000 : ℝ)|=(1577562693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4919658581/10000000000 : ℝ)|^17 ≤ (19774965150411/50000000000000 : ℝ)^13
        have hw : |(4919658581/10000000000 : ℝ)|=(4919658581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010708531/5000000000 : ℝ)|^17 ≤ (12878156688099/25000000000000 : ℝ)^13
        have hw : |(3010708531/5000000000 : ℝ)|=(3010708531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2252206239/5000000000 : ℝ)*x 0 + (-179961667/10000000000 : ℝ)*x 1 + (7128548427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252206239/5000000000 : ℝ)^17 ≤ (17621191914519/50000000000000 : ℝ)^13 := by
    have hnat : (2252206239 : ℕ)^17*50000000000000^13 ≤ 17621191914519^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252206239 5000000000 17621191914519 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179961667/10000000000 : ℝ)^17 ≤ (32673249921/6250000000000 : ℝ)^13 := by
    have hnat : (179961667 : ℕ)^17*6250000000000^13 ≤ 32673249921^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179961667 10000000000 32673249921 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7128548427/10000000000 : ℝ)^17 ≤ (64234844161441/100000000000000 : ℝ)^13 := by
    have hnat : (7128548427 : ℕ)^17*100000000000000^13 ≤ 64234844161441^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7128548427 10000000000 64234844161441 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252206239/5000000000 : ℝ), (-179961667/10000000000 : ℝ), (7128548427/10000000000 : ℝ)] ![(17621191914519/50000000000000 : ℝ), (32673249921/6250000000000 : ℝ), (64234844161441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252206239/5000000000 : ℝ)|^17 ≤ (17621191914519/50000000000000 : ℝ)^13
        have hw : |(2252206239/5000000000 : ℝ)|=(2252206239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179961667/10000000000 : ℝ)|^17 ≤ (32673249921/6250000000000 : ℝ)^13
        have hw : |(-179961667/10000000000 : ℝ)|=(179961667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7128548427/10000000000 : ℝ)|^17 ≤ (64234844161441/100000000000000 : ℝ)^13
        have hw : |(7128548427/10000000000 : ℝ)|=(7128548427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4472011947/10000000000 : ℝ)*x 0 + (1359489121/2000000000 : ℝ)*x 1 + (-193864097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4472011947/10000000000 : ℝ)^17 ≤ (17455625152031/50000000000000 : ℝ)^13 := by
    have hnat : (4472011947 : ℕ)^17*50000000000000^13 ≤ 17455625152031^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472011947 10000000000 17455625152031 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359489121/2000000000 : ℝ)^17 ≤ (60361471019491/100000000000000 : ℝ)^13 := by
    have hnat : (1359489121 : ℕ)^17*100000000000000^13 ≤ 60361471019491^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359489121 2000000000 60361471019491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193864097/2000000000 : ℝ)^17 ≤ (236363933009/5000000000000 : ℝ)^13 := by
    have hnat : (193864097 : ℕ)^17*5000000000000^13 ≤ 236363933009^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193864097 2000000000 236363933009 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4472011947/10000000000 : ℝ), (1359489121/2000000000 : ℝ), (-193864097/2000000000 : ℝ)] ![(17455625152031/50000000000000 : ℝ), (60361471019491/100000000000000 : ℝ), (236363933009/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4472011947/10000000000 : ℝ)|^17 ≤ (17455625152031/50000000000000 : ℝ)^13
        have hw : |(4472011947/10000000000 : ℝ)|=(4472011947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359489121/2000000000 : ℝ)|^17 ≤ (60361471019491/100000000000000 : ℝ)^13
        have hw : |(1359489121/2000000000 : ℝ)|=(1359489121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193864097/2000000000 : ℝ)|^17 ≤ (236363933009/5000000000000 : ℝ)^13
        have hw : |(-193864097/2000000000 : ℝ)|=(193864097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (640467447/1250000000 : ℝ)*x 0 + (599916407/1000000000 : ℝ)*x 1 + (1312590457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640467447/1250000000 : ℝ)^17 ≤ (41708946106881/100000000000000 : ℝ)^13 := by
    have hnat : (640467447 : ℕ)^17*100000000000000^13 ≤ 41708946106881^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640467447 1250000000 41708946106881 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599916407/1000000000 : ℝ)^17 ≤ (5126382022807/10000000000000 : ℝ)^13 := by
    have hnat : (599916407 : ℕ)^17*10000000000000^13 ≤ 5126382022807^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599916407 1000000000 5126382022807 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1312590457/10000000000 : ℝ)^17 ≤ (1756808413529/25000000000000 : ℝ)^13 := by
    have hnat : (1312590457 : ℕ)^17*25000000000000^13 ≤ 1756808413529^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312590457 10000000000 1756808413529 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640467447/1250000000 : ℝ), (599916407/1000000000 : ℝ), (1312590457/10000000000 : ℝ)] ![(41708946106881/100000000000000 : ℝ), (5126382022807/10000000000000 : ℝ), (1756808413529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640467447/1250000000 : ℝ)|^17 ≤ (41708946106881/100000000000000 : ℝ)^13
        have hw : |(640467447/1250000000 : ℝ)|=(640467447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(599916407/1000000000 : ℝ)|^17 ≤ (5126382022807/10000000000000 : ℝ)^13
        have hw : |(599916407/1000000000 : ℝ)|=(599916407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1312590457/10000000000 : ℝ)|^17 ≤ (1756808413529/25000000000000 : ℝ)^13
        have hw : |(1312590457/10000000000 : ℝ)|=(1312590457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-800315337/10000000000 : ℝ)*x 0 + (5258091773/10000000000 : ℝ)*x 1 + (1542375507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800315337/10000000000 : ℝ)^17 ≤ (735924098377/20000000000000 : ℝ)^13 := by
    have hnat : (800315337 : ℕ)^17*20000000000000^13 ≤ 735924098377^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800315337 10000000000 735924098377 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258091773/10000000000 : ℝ)^17 ≤ (43144867019607/100000000000000 : ℝ)^13 := by
    have hnat : (5258091773 : ℕ)^17*100000000000000^13 ≤ 43144867019607^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258091773 10000000000 43144867019607 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1542375507/2500000000 : ℝ)^17 ≤ (6646939058809/12500000000000 : ℝ)^13 := by
    have hnat : (1542375507 : ℕ)^17*12500000000000^13 ≤ 6646939058809^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542375507 2500000000 6646939058809 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-800315337/10000000000 : ℝ), (5258091773/10000000000 : ℝ), (1542375507/2500000000 : ℝ)] ![(735924098377/20000000000000 : ℝ), (43144867019607/100000000000000 : ℝ), (6646939058809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-800315337/10000000000 : ℝ)|^17 ≤ (735924098377/20000000000000 : ℝ)^13
        have hw : |(-800315337/10000000000 : ℝ)|=(800315337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258091773/10000000000 : ℝ)|^17 ≤ (43144867019607/100000000000000 : ℝ)^13
        have hw : |(5258091773/10000000000 : ℝ)|=(5258091773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1542375507/2500000000 : ℝ)|^17 ≤ (6646939058809/12500000000000 : ℝ)^13
        have hw : |(1542375507/2500000000 : ℝ)|=(1542375507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4199038257/10000000000 : ℝ)*x 0 + (-736106861/10000000000 : ℝ)*x 1 + (7155317709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199038257/10000000000 : ℝ)^17 ≤ (6430221439623/20000000000000 : ℝ)^13 := by
    have hnat : (4199038257 : ℕ)^17*20000000000000^13 ≤ 6430221439623^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199038257 10000000000 6430221439623 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736106861/10000000000 : ℝ)^17 ≤ (3298430106647/100000000000000 : ℝ)^13 := by
    have hnat : (736106861 : ℕ)^17*100000000000000^13 ≤ 3298430106647^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736106861 10000000000 3298430106647 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7155317709/10000000000 : ℝ)^17 ≤ (64550462679559/100000000000000 : ℝ)^13 := by
    have hnat : (7155317709 : ℕ)^17*100000000000000^13 ≤ 64550462679559^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7155317709 10000000000 64550462679559 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199038257/10000000000 : ℝ), (-736106861/10000000000 : ℝ), (7155317709/10000000000 : ℝ)] ![(6430221439623/20000000000000 : ℝ), (3298430106647/100000000000000 : ℝ), (64550462679559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199038257/10000000000 : ℝ)|^17 ≤ (6430221439623/20000000000000 : ℝ)^13
        have hw : |(4199038257/10000000000 : ℝ)|=(4199038257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-736106861/10000000000 : ℝ)|^17 ≤ (3298430106647/100000000000000 : ℝ)^13
        have hw : |(-736106861/10000000000 : ℝ)|=(736106861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7155317709/10000000000 : ℝ)|^17 ≤ (64550462679559/100000000000000 : ℝ)^13
        have hw : |(7155317709/10000000000 : ℝ)|=(7155317709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3064173797/5000000000 : ℝ)*x 0 + (2644739519/5000000000 : ℝ)*x 1 + (-821235051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3064173797/5000000000 : ℝ)^17 ≤ (52712132601237/100000000000000 : ℝ)^13 := by
    have hnat : (3064173797 : ℕ)^17*100000000000000^13 ≤ 52712132601237^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3064173797 5000000000 52712132601237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2644739519/5000000000 : ℝ)^17 ≤ (4348196653119/10000000000000 : ℝ)^13 := by
    have hnat : (2644739519 : ℕ)^17*10000000000000^13 ≤ 4348196653119^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644739519 5000000000 4348196653119 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (821235051/10000000000 : ℝ)^17 ≤ (951475212729/25000000000000 : ℝ)^13 := by
    have hnat : (821235051 : ℕ)^17*25000000000000^13 ≤ 951475212729^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821235051 10000000000 951475212729 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3064173797/5000000000 : ℝ), (2644739519/5000000000 : ℝ), (-821235051/10000000000 : ℝ)] ![(52712132601237/100000000000000 : ℝ), (4348196653119/10000000000000 : ℝ), (951475212729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3064173797/5000000000 : ℝ)|^17 ≤ (52712132601237/100000000000000 : ℝ)^13
        have hw : |(3064173797/5000000000 : ℝ)|=(3064173797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2644739519/5000000000 : ℝ)|^17 ≤ (4348196653119/10000000000000 : ℝ)^13
        have hw : |(2644739519/5000000000 : ℝ)|=(2644739519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-821235051/10000000000 : ℝ)|^17 ≤ (951475212729/25000000000000 : ℝ)^13
        have hw : |(-821235051/10000000000 : ℝ)|=(821235051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (190543109/250000000 : ℝ)*x 0 + (327807031/1000000000 : ℝ)*x 1 + (628067117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190543109/250000000 : ℝ)^17 ≤ (70107087799709/100000000000000 : ℝ)^13 := by
    have hnat : (190543109 : ℕ)^17*100000000000000^13 ≤ 70107087799709^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190543109 250000000 70107087799709 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327807031/1000000000 : ℝ)^17 ≤ (11629143634339/50000000000000 : ℝ)^13 := by
    have hnat : (327807031 : ℕ)^17*50000000000000^13 ≤ 11629143634339^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327807031 1000000000 11629143634339 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628067117/5000000000 : ℝ)^17 ≤ (414664057323/6250000000000 : ℝ)^13 := by
    have hnat : (628067117 : ℕ)^17*6250000000000^13 ≤ 414664057323^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628067117 5000000000 414664057323 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(190543109/250000000 : ℝ), (327807031/1000000000 : ℝ), (628067117/5000000000 : ℝ)] ![(70107087799709/100000000000000 : ℝ), (11629143634339/50000000000000 : ℝ), (414664057323/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(190543109/250000000 : ℝ)|^17 ≤ (70107087799709/100000000000000 : ℝ)^13
        have hw : |(190543109/250000000 : ℝ)|=(190543109/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327807031/1000000000 : ℝ)|^17 ≤ (11629143634339/50000000000000 : ℝ)^13
        have hw : |(327807031/1000000000 : ℝ)|=(327807031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628067117/5000000000 : ℝ)|^17 ≤ (414664057323/6250000000000 : ℝ)^13
        have hw : |(628067117/5000000000 : ℝ)|=(628067117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-195341671/2500000000 : ℝ)*x 0 + (6548247269/10000000000 : ℝ)*x 1 + (4862463561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195341671/2500000000 : ℝ)^17 ≤ (1783055495179/50000000000000 : ℝ)^13 := by
    have hnat : (195341671 : ℕ)^17*50000000000000^13 ≤ 1783055495179^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195341671 2500000000 1783055495179 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6548247269/10000000000 : ℝ)^17 ≤ (2299366291873/4000000000000 : ℝ)^13 := by
    have hnat : (6548247269 : ℕ)^17*4000000000000^13 ≤ 2299366291873^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6548247269 10000000000 2299366291873 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4862463561/10000000000 : ℝ)^17 ≤ (9737432925649/25000000000000 : ℝ)^13 := by
    have hnat : (4862463561 : ℕ)^17*25000000000000^13 ≤ 9737432925649^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862463561 10000000000 9737432925649 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-195341671/2500000000 : ℝ), (6548247269/10000000000 : ℝ), (4862463561/10000000000 : ℝ)] ![(1783055495179/50000000000000 : ℝ), (2299366291873/4000000000000 : ℝ), (9737432925649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-195341671/2500000000 : ℝ)|^17 ≤ (1783055495179/50000000000000 : ℝ)^13
        have hw : |(-195341671/2500000000 : ℝ)|=(195341671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6548247269/10000000000 : ℝ)|^17 ≤ (2299366291873/4000000000000 : ℝ)^13
        have hw : |(6548247269/10000000000 : ℝ)|=(6548247269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4862463561/10000000000 : ℝ)|^17 ≤ (9737432925649/25000000000000 : ℝ)^13
        have hw : |(4862463561/10000000000 : ℝ)|=(4862463561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6179696073/10000000000 : ℝ)*x 0 + (-182447223/10000000000 : ℝ)*x 1 + (5538430559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6179696073/10000000000 : ℝ)^17 ≤ (53290439989523/100000000000000 : ℝ)^13 := by
    have hnat : (6179696073 : ℕ)^17*100000000000000^13 ≤ 53290439989523^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6179696073 10000000000 53290439989523 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182447223/10000000000 : ℝ)^17 ≤ (106446788441/20000000000000 : ℝ)^13 := by
    have hnat : (182447223 : ℕ)^17*20000000000000^13 ≤ 106446788441^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182447223 10000000000 106446788441 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5538430559/10000000000 : ℝ)^17 ≤ (5772165756319/12500000000000 : ℝ)^13 := by
    have hnat : (5538430559 : ℕ)^17*12500000000000^13 ≤ 5772165756319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538430559 10000000000 5772165756319 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6179696073/10000000000 : ℝ), (-182447223/10000000000 : ℝ), (5538430559/10000000000 : ℝ)] ![(53290439989523/100000000000000 : ℝ), (106446788441/20000000000000 : ℝ), (5772165756319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6179696073/10000000000 : ℝ)|^17 ≤ (53290439989523/100000000000000 : ℝ)^13
        have hw : |(6179696073/10000000000 : ℝ)|=(6179696073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182447223/10000000000 : ℝ)|^17 ≤ (106446788441/20000000000000 : ℝ)^13
        have hw : |(-182447223/10000000000 : ℝ)|=(182447223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5538430559/10000000000 : ℝ)|^17 ≤ (5772165756319/12500000000000 : ℝ)^13
        have hw : |(5538430559/10000000000 : ℝ)|=(5538430559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4195649633/10000000000 : ℝ)*x 0 + (84937001/125000000 : ℝ)*x 1 + (-1386655513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195649633/10000000000 : ℝ)^17 ≤ (2007323881209/6250000000000 : ℝ)^13 := by
    have hnat : (4195649633 : ℕ)^17*6250000000000^13 ≤ 2007323881209^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195649633 10000000000 2007323881209 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84937001/125000000 : ℝ)^17 ≤ (60332609888557/100000000000000 : ℝ)^13 := by
    have hnat : (84937001 : ℕ)^17*100000000000000^13 ≤ 60332609888557^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84937001 125000000 60332609888557 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386655513/10000000000 : ℝ)^17 ≤ (7550207993533/100000000000000 : ℝ)^13 := by
    have hnat : (1386655513 : ℕ)^17*100000000000000^13 ≤ 7550207993533^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386655513 10000000000 7550207993533 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195649633/10000000000 : ℝ), (84937001/125000000 : ℝ), (-1386655513/10000000000 : ℝ)] ![(2007323881209/6250000000000 : ℝ), (60332609888557/100000000000000 : ℝ), (7550207993533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195649633/10000000000 : ℝ)|^17 ≤ (2007323881209/6250000000000 : ℝ)^13
        have hw : |(4195649633/10000000000 : ℝ)|=(4195649633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84937001/125000000 : ℝ)|^17 ≤ (60332609888557/100000000000000 : ℝ)^13
        have hw : |(84937001/125000000 : ℝ)|=(84937001/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1386655513/10000000000 : ℝ)|^17 ≤ (7550207993533/100000000000000 : ℝ)^13
        have hw : |(-1386655513/10000000000 : ℝ)|=(1386655513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307055_s4_s4_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3780269363/5000000000 : ℝ)*x 0 + (2564536149/10000000000 : ℝ)*x 1 + (2193817313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3780269363/5000000000 : ℝ)^17 ≤ (69372022334539/100000000000000 : ℝ)^13 := by
    have hnat : (3780269363 : ℕ)^17*100000000000000^13 ≤ 69372022334539^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780269363 5000000000 69372022334539 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564536149/10000000000 : ℝ)^17 ≤ (16871954157661/100000000000000 : ℝ)^13 := by
    have hnat : (2564536149 : ℕ)^17*100000000000000^13 ≤ 16871954157661^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564536149 10000000000 16871954157661 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193817313/10000000000 : ℝ)^17 ≤ (1375602348393/10000000000000 : ℝ)^13 := by
    have hnat : (2193817313 : ℕ)^17*10000000000000^13 ≤ 1375602348393^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193817313 10000000000 1375602348393 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3780269363/5000000000 : ℝ), (2564536149/10000000000 : ℝ), (2193817313/10000000000 : ℝ)] ![(69372022334539/100000000000000 : ℝ), (16871954157661/100000000000000 : ℝ), (1375602348393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3780269363/5000000000 : ℝ)|^17 ≤ (69372022334539/100000000000000 : ℝ)^13
        have hw : |(3780269363/5000000000 : ℝ)|=(3780269363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564536149/10000000000 : ℝ)|^17 ≤ (16871954157661/100000000000000 : ℝ)^13
        have hw : |(2564536149/10000000000 : ℝ)|=(2564536149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2193817313/10000000000 : ℝ)|^17 ≤ (1375602348393/10000000000000 : ℝ)^13
        have hw : |(2193817313/10000000000 : ℝ)|=(2193817313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307055_s4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((2627/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2627/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32443/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32443/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33283/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33283/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11903/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11903/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48521/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48521/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49033/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49033/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s4_pow0 : (2627/4000 : ℝ) ^ (135/32 : ℝ) ≤ (16969013440350039419/100000000000000000000 : ℝ) := by
    have hpowers : (2627/4000 : ℝ)^135 ≤ (16969013440350039419/100000000000000000000 : ℝ)^32 := by
      have hnat : (2627 : ℕ)^135*100000000000000000000^32 ≤ 16969013440350039419^32*4000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2627 4000 16969013440350039419 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2627/4000 : ℝ)) (X := (16969013440350039419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (116969013440350039419/100000000000000000000 : ℝ) ≤ (2075703429102357/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (116969013440350039419/100000000000000000000 : ℝ)^32 ≤ (2075703429102357/2000000000000000 : ℝ)^135 := by
      have hnat : (116969013440350039419 : ℕ)^32*2000000000000000^135 ≤ 2075703429102357^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116969013440350039419 100000000000000000000 2075703429102357 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2075703429102357/2000000000000000 : ℝ)) (X := (116969013440350039419/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (66969013440350039419/50000000000000000000 : ℝ) ≤ (669824364980703/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (66969013440350039419/50000000000000000000 : ℝ)^32 ≤ (669824364980703/625000000000000 : ℝ)^135 := by
      have hnat : (66969013440350039419 : ℕ)^32*625000000000000^135 ≤ 669824364980703^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66969013440350039419 50000000000000000000 669824364980703 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (669824364980703/625000000000000 : ℝ)) (X := (66969013440350039419/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(75703429102357/1313500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(338672694179463/6567500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (2627/4000 : ℝ)) (alpha := (75703429102357/1313500000000000 : ℝ)) (beta := (338672694179463/6567500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2627/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(75703429102357/1313500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(338672694179463/6567500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (32443/50000 : ℝ) ^ (135/32 : ℝ) ≤ (8062728668607905363/50000000000000000000 : ℝ) := by
    have hpowers : (32443/50000 : ℝ)^135 ≤ (8062728668607905363/50000000000000000000 : ℝ)^32 := by
      have hnat : (32443 : ℕ)^135*50000000000000000000^32 ≤ 8062728668607905363^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32443 50000 8062728668607905363 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32443/50000 : ℝ)) (X := (8062728668607905363/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (58062728668607905363/50000000000000000000 : ℝ) ≤ (10360726450601597/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (58062728668607905363/50000000000000000000 : ℝ)^32 ≤ (10360726450601597/10000000000000000 : ℝ)^135 := by
      have hnat : (58062728668607905363 : ℕ)^32*10000000000000000^135 ≤ 10360726450601597^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58062728668607905363 50000000000000000000 10360726450601597 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10360726450601597/10000000000000000 : ℝ)) (X := (58062728668607905363/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (33062728668607905363/25000000000000000000 : ℝ) ≤ (10685035870114157/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (33062728668607905363/25000000000000000000 : ℝ)^32 ≤ (10685035870114157/10000000000000000 : ℝ)^135 := by
      have hnat : (33062728668607905363 : ℕ)^32*10000000000000000^135 ≤ 10685035870114157^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33062728668607905363 25000000000000000000 10685035870114157 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10685035870114157/10000000000000000 : ℝ)) (X := (33062728668607905363/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(360726450601597/6488600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(4053867743907/81107500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (32443/50000 : ℝ)) (alpha := (360726450601597/6488600000000000 : ℝ)) (beta := (4053867743907/81107500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (32443/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(360726450601597/6488600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(4053867743907/81107500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (33283/50000 : ℝ) ^ (135/32 : ℝ) ≤ (8980826838783284151/50000000000000000000 : ℝ) := by
    have hpowers : (33283/50000 : ℝ)^135 ≤ (8980826838783284151/50000000000000000000 : ℝ)^32 := by
      have hnat : (33283 : ℕ)^135*50000000000000000000^32 ≤ 8980826838783284151^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33283 50000 8980826838783284151 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33283/50000 : ℝ)) (X := (8980826838783284151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (58980826838783284151/50000000000000000000 : ℝ) ≤ (2599831777023227/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (58980826838783284151/50000000000000000000 : ℝ)^32 ≤ (2599831777023227/2500000000000000 : ℝ)^135 := by
      have hnat : (58980826838783284151 : ℕ)^32*2500000000000000^135 ≤ 2599831777023227^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58980826838783284151 50000000000000000000 2599831777023227 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2599831777023227/2500000000000000 : ℝ)) (X := (58980826838783284151/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (33980826838783284151/25000000000000000000 : ℝ) ≤ (134432913828383/125000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (33980826838783284151/25000000000000000000 : ℝ)^32 ≤ (134432913828383/125000000000000 : ℝ)^135 := by
      have hnat : (33980826838783284151 : ℕ)^32*125000000000000^135 ≤ 134432913828383^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33980826838783284151 25000000000000000000 134432913828383 125000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (134432913828383/125000000000000 : ℝ)) (X := (33980826838783284151/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(99831777023227/1664150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(88826499544433/1664150000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (33283/50000 : ℝ)) (alpha := (99831777023227/1664150000000000 : ℝ)) (beta := (88826499544433/1664150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (33283/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(99831777023227/1664150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(88826499544433/1664150000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-2014096143/10000000000 : ℝ)*X 0 0+(1155853367/2000000000 : ℝ)*X 0 1+(1213906697/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((1202651167/2500000000 : ℝ)*X 2 0+(5810183579/10000000000 : ℝ)*X 2 1+(-203021747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((244363039/400000000 : ℝ)*X 0 0+(4000619651/10000000000 : ℝ)*X 0 1+(104683689/400000000 : ℝ)*X 0 2+(244363039/400000000 : ℝ)*X 1 0+(4000619651/10000000000 : ℝ)*X 1 1+(104683689/400000000 : ℝ)*X 1 2+(244363039/400000000 : ℝ)*X 2 0+(4000619651/10000000000 : ℝ)*X 2 1+(104683689/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-1577562693/10000000000 : ℝ)*X 0 0+(4919658581/10000000000 : ℝ)*X 0 1+(3010708531/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((2252206239/5000000000 : ℝ)*X 1 0+(-179961667/10000000000 : ℝ)*X 1 1+(7128548427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4472011947/10000000000 : ℝ)*X 2 0+(1359489121/2000000000 : ℝ)*X 2 1+(-193864097/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((640467447/1250000000 : ℝ)*X 0 0+(599916407/1000000000 : ℝ)*X 0 1+(1312590457/10000000000 : ℝ)*X 0 2+(640467447/1250000000 : ℝ)*X 1 0+(599916407/1000000000 : ℝ)*X 1 1+(1312590457/10000000000 : ℝ)*X 1 2+(640467447/1250000000 : ℝ)*X 2 0+(599916407/1000000000 : ℝ)*X 2 1+(1312590457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-800315337/10000000000 : ℝ)*X 0 0+(5258091773/10000000000 : ℝ)*X 0 1+(1542375507/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4199038257/10000000000 : ℝ)*X 1 0+(-736106861/10000000000 : ℝ)*X 1 1+(7155317709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((3064173797/5000000000 : ℝ)*X 2 0+(2644739519/5000000000 : ℝ)*X 2 1+(-821235051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((190543109/250000000 : ℝ)*X 0 0+(327807031/1000000000 : ℝ)*X 0 1+(628067117/5000000000 : ℝ)*X 0 2+(190543109/250000000 : ℝ)*X 1 0+(327807031/1000000000 : ℝ)*X 1 1+(628067117/5000000000 : ℝ)*X 1 2+(190543109/250000000 : ℝ)*X 2 0+(327807031/1000000000 : ℝ)*X 2 1+(628067117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-195341671/2500000000 : ℝ)*X 0 0+(6548247269/10000000000 : ℝ)*X 0 1+(4862463561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6179696073/10000000000 : ℝ)*X 1 0+(-182447223/10000000000 : ℝ)*X 1 1+(5538430559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4195649633/10000000000 : ℝ)*X 2 0+(84937001/125000000 : ℝ)*X 2 1+(-1386655513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((3780269363/5000000000 : ℝ)*X 0 0+(2564536149/10000000000 : ℝ)*X 0 1+(2193817313/10000000000 : ℝ)*X 0 2+(3780269363/5000000000 : ℝ)*X 1 0+(2564536149/10000000000 : ℝ)*X 1 1+(2193817313/10000000000 : ℝ)*X 1 2+(3780269363/5000000000 : ℝ)*X 2 0+(2564536149/10000000000 : ℝ)*X 2 1+(2193817313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307055_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((11903/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11903/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23308453901971007112059141819283/1418317784681500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1792357/200000000000 : ℝ)*(base19) + (97119747723/500000000000 : ℝ)*(base49) + (3992027981271/1000000000000 : ℝ)*(major_s4_0) + (3992027981271/1000000000000 : ℝ)*(major_s4_1) + (3992027981271/1000000000000 : ℝ)*(major_s4_2) + (4510343/100000000000 : ℝ)*(sp_s4_0) + (1722031/200000000000 : ℝ)*(sp_s4_6) + (676990388559/125000000000 : ℝ)*(sp_s4_7) + (1353972187571/250000000000 : ℝ)*(sp_s4_8) + (338483985641/62500000000 : ℝ)*(sp_s4_9) + (642017683881/250000000000 : ℝ)*(sp_s4_13) + (73426833/1000000000000 : ℝ)*(sp_s4_15) + (2926999/1000000000000 : ℝ)*(sp_s4_21) + (113684323/500000000000 : ℝ)*(sp_s4_23) + (2568079345679/1000000000000 : ℝ)*(f.failure) + (5415971138901/1000000000000 : ℝ)*(f.sum) + (6041258576664840403/43192014760000000000000000000000 : ℝ)*base62 + (560005590858173/1664150000000000000000000000 : ℝ)*base65 + (98786152035157/162215000000000000000000000 : ℝ)*base67 + (12282817210013/1664150000000000000000000000 : ℝ)*base68 + (2491107354353347189/43717220500000000000000000000000 : ℝ)*base70 + (2822772223766527/6567500000000000000000000000 : ℝ)*base72 + (1154561827259353/6488600000000000000000000000 : ℝ)*base74 + (407016290340003/1313500000000000000000000000 : ℝ)*base76 + (59378592051156571289/213069402500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1149/12500000000000000 : ℝ)*base87 + (1149/12500000000000000 : ℝ)*base89 + (1149/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48521/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48521/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (308499999004736519244203223/21858610250000000000000000000000 : ℝ) := by norm_num
    linear_combination (119319/250000000000 : ℝ)*(base21) + (2054789/500000000000 : ℝ)*(base39) + (120967878441/1000000000000 : ℝ)*(base49) + (508069/1000000000000 : ℝ)*(base60) + (3757364432759/1000000000000 : ℝ)*(major_s4_0) + (3757364432759/1000000000000 : ℝ)*(major_s4_1) + (3757364432759/1000000000000 : ℝ)*(major_s4_2) + (16363287/500000000000 : ℝ)*(sp_s4_7) + (45316837/500000000000 : ℝ)*(sp_s4_8) + (1019514320967/200000000000 : ℝ)*(sp_s4_14) + (1019502739547/200000000000 : ℝ)*(sp_s4_15) + (5097603854133/1000000000000 : ℝ)*(sp_s4_16) + (2417035372189/1000000000000 : ℝ)*(sp_s4_20) + (42228719/500000000000 : ℝ)*(sp_s4_27) + (2417119829627/1000000000000 : ℝ)*(f.failure) + (5097604331409/1000000000000 : ℝ)*(f.sum) + (22181631510608819/69107223616000000000000000000 : ℝ)*base62 + (148859264557779/208018750000000000000000000 : ℝ)*base65 + (6521843919941/81107500000000000000000000 : ℝ)*base67 + (54531828529033/416037500000000000000000000 : ℝ)*base68 + (20917324577765323269/43717220500000000000000000000000 : ℝ)*base71 + (922753820705667/6567500000000000000000000000 : ℝ)*base73 + (960401989410323/6488600000000000000000000000 : ℝ)*base75 + (597977453609863/1313500000000000000000000000 : ℝ)*base77 + (53128465754064832519/213069402500000000000000000000000 : ℝ)*base78 + (5263/12500000000000000 : ℝ)*base86 + (5263/12500000000000000 : ℝ)*base88 + (5263/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49033/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49033/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17432784182466121386146873199309/3545794461703750000000000000000000000 : ℝ) := by norm_num
    linear_combination (55166007649/500000000000 : ℝ)*(base40) + (73164789037/1000000000000 : ℝ)*(base49) + (1373977/1000000000000 : ℝ)*(base59) + (14752855779/3906250000 : ℝ)*(major_s4_0) + (14752855779/3906250000 : ℝ)*(major_s4_1) + (14752855779/3906250000 : ℝ)*(major_s4_2) + (2973893/250000000000 : ℝ)*(sp_s4_0) + (2103953/1000000000000 : ℝ)*(sp_s4_2) + (830361/100000000000 : ℝ)*(sp_s4_9) + (893309/20000000000 : ℝ)*(sp_s4_20) + (102477403869/20000000000 : ℝ)*(sp_s4_21) + (2561941044511/500000000000 : ℝ)*(sp_s4_22) + (5123871681459/1000000000000 : ℝ)*(sp_s4_23) + (151845860347/62500000000 : ℝ)*(sp_s4_27) + (1214789215501/500000000000 : ℝ)*(f.failure) + (2561941044511/500000000000 : ℝ)*(f.sum) + (26366650198429361/539900184500000000000000000000 : ℝ)*base63 + (281800605989939/832075000000000000000000000 : ℝ)*base64 + (27873068301669/162215000000000000000000000 : ℝ)*base66 + (136317834240161/832075000000000000000000000 : ℝ)*base68 + (943172458376870029/10929305125000000000000000000000 : ℝ)*base70 + (450521925738797/1641875000000000000000000000 : ℝ)*base72 + (149371526649163/1622150000000000000000000000 : ℝ)*base74 + (15650986545309/656750000000000000000000000 : ℝ)*base77 + (16591558084952584517/106534701250000000000000000000000 : ℝ)*base78 + (69/6250000000000000 : ℝ)*base86 + (69/6250000000000000 : ℝ)*base88 + (69/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((2627/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2627/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32443/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32443/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33283/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33283/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11903/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11903/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48521/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48521/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49033/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49033/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307055_s4 p hpa hpb X hX hprev3

#print axioms solution

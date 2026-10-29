-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:16:17.651996+00:00
-- url     : https://prove2.me/submissions/459d67bb-4b4e-4269-9ae8-1e0434bd8899

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
theorem collision_support_c317083_s1_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1128202513/5000000000 : ℝ)*x 0 + (2405346283/5000000000 : ℝ)*x 1 + (528265501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128202513/5000000000 : ℝ)^39 ≤ (7682931282479/50000000000000 : ℝ)^31 := by
    have hnat : (1128202513 : ℕ)^39*50000000000000^31 ≤ 7682931282479^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128202513 5000000000 7682931282479 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2405346283/5000000000 : ℝ)^39 ≤ (7965749743619/20000000000000 : ℝ)^31 := by
    have hnat : (2405346283 : ℕ)^39*20000000000000^31 ≤ 7965749743619^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405346283 5000000000 7965749743619 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528265501/1000000000 : ℝ)^39 ≤ (44805388706493/100000000000000 : ℝ)^31 := by
    have hnat : (528265501 : ℕ)^39*100000000000000^31 ≤ 44805388706493^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528265501 1000000000 44805388706493 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1128202513/5000000000 : ℝ), (2405346283/5000000000 : ℝ), (528265501/1000000000 : ℝ)] ![(7682931282479/50000000000000 : ℝ), (7965749743619/20000000000000 : ℝ), (44805388706493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1128202513/5000000000 : ℝ)|^39 ≤ (7682931282479/50000000000000 : ℝ)^31
        have hw : |(-1128202513/5000000000 : ℝ)|=(1128202513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2405346283/5000000000 : ℝ)|^39 ≤ (7965749743619/20000000000000 : ℝ)^31
        have hw : |(2405346283/5000000000 : ℝ)|=(2405346283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528265501/1000000000 : ℝ)|^39 ≤ (44805388706493/100000000000000 : ℝ)^31
        have hw : |(528265501/1000000000 : ℝ)|=(528265501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6793810717/10000000000 : ℝ)*x 0 + (-197313327/2500000000 : ℝ)*x 1 + (85662777/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6793810717/10000000000 : ℝ)^39 ≤ (2459505912753/4000000000000 : ℝ)^31 := by
    have hnat : (6793810717 : ℕ)^39*4000000000000^31 ≤ 2459505912753^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6793810717 10000000000 2459505912753 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197313327/2500000000 : ℝ)^39 ≤ (1024630091519/25000000000000 : ℝ)^31 := by
    have hnat : (197313327 : ℕ)^39*25000000000000^31 ≤ 1024630091519^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197313327 2500000000 1024630091519 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85662777/200000000 : ℝ)^39 ≤ (17206915903797/50000000000000 : ℝ)^31 := by
    have hnat : (85662777 : ℕ)^39*50000000000000^31 ≤ 17206915903797^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85662777 200000000 17206915903797 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6793810717/10000000000 : ℝ), (-197313327/2500000000 : ℝ), (85662777/200000000 : ℝ)] ![(2459505912753/4000000000000 : ℝ), (1024630091519/25000000000000 : ℝ), (17206915903797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6793810717/10000000000 : ℝ)|^39 ≤ (2459505912753/4000000000000 : ℝ)^31
        have hw : |(6793810717/10000000000 : ℝ)|=(6793810717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197313327/2500000000 : ℝ)|^39 ≤ (1024630091519/25000000000000 : ℝ)^31
        have hw : |(-197313327/2500000000 : ℝ)|=(197313327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85662777/200000000 : ℝ)|^39 ≤ (17206915903797/50000000000000 : ℝ)^31
        have hw : |(85662777/200000000 : ℝ)|=(85662777/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (710920117/2000000000 : ℝ)*x 0 + (6398965169/10000000000 : ℝ)*x 1 + (-2301745737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (710920117/2000000000 : ℝ)^39 ≤ (1701162781771/6250000000000 : ℝ)^31 := by
    have hnat : (710920117 : ℕ)^39*6250000000000^31 ≤ 1701162781771^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710920117 2000000000 1701162781771 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6398965169/10000000000 : ℝ)^39 ≤ (57026084292049/100000000000000 : ℝ)^31 := by
    have hnat : (6398965169 : ℕ)^39*100000000000000^31 ≤ 57026084292049^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6398965169 10000000000 57026084292049 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2301745737/10000000000 : ℝ)^39 ≤ (15755311190173/100000000000000 : ℝ)^31 := by
    have hnat : (2301745737 : ℕ)^39*100000000000000^31 ≤ 15755311190173^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301745737 10000000000 15755311190173 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(710920117/2000000000 : ℝ), (6398965169/10000000000 : ℝ), (-2301745737/10000000000 : ℝ)] ![(1701162781771/6250000000000 : ℝ), (57026084292049/100000000000000 : ℝ), (15755311190173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(710920117/2000000000 : ℝ)|^39 ≤ (1701162781771/6250000000000 : ℝ)^31
        have hw : |(710920117/2000000000 : ℝ)|=(710920117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6398965169/10000000000 : ℝ)|^39 ≤ (57026084292049/100000000000000 : ℝ)^31
        have hw : |(6398965169/10000000000 : ℝ)|=(6398965169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2301745737/10000000000 : ℝ)|^39 ≤ (15755311190173/100000000000000 : ℝ)^31
        have hw : |(-2301745737/10000000000 : ℝ)|=(2301745737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-568686467/2500000000 : ℝ)*x 0 + (2387510251/5000000000 : ℝ)*x 1 + (530269139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568686467/2500000000 : ℝ)^39 ≤ (15523158107211/100000000000000 : ℝ)^31 := by
    have hnat : (568686467 : ℕ)^39*100000000000000^31 ≤ 15523158107211^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568686467 2500000000 15523158107211 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2387510251/5000000000 : ℝ)^39 ≤ (19728776176091/50000000000000 : ℝ)^31 := by
    have hnat : (2387510251 : ℕ)^39*50000000000000^31 ≤ 19728776176091^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387510251 5000000000 19728776176091 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530269139/1000000000 : ℝ)^39 ≤ (45019289534741/100000000000000 : ℝ)^31 := by
    have hnat : (530269139 : ℕ)^39*100000000000000^31 ≤ 45019289534741^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530269139 1000000000 45019289534741 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-568686467/2500000000 : ℝ), (2387510251/5000000000 : ℝ), (530269139/1000000000 : ℝ)] ![(15523158107211/100000000000000 : ℝ), (19728776176091/50000000000000 : ℝ), (45019289534741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-568686467/2500000000 : ℝ)|^39 ≤ (15523158107211/100000000000000 : ℝ)^31
        have hw : |(-568686467/2500000000 : ℝ)|=(568686467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2387510251/5000000000 : ℝ)|^39 ≤ (19728776176091/50000000000000 : ℝ)^31
        have hw : |(2387510251/5000000000 : ℝ)|=(2387510251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530269139/1000000000 : ℝ)|^39 ≤ (45019289534741/100000000000000 : ℝ)^31
        have hw : |(530269139/1000000000 : ℝ)|=(530269139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1301365471/2000000000 : ℝ)*x 0 + (-16114181/5000000000 : ℝ)*x 1 + (4988420943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301365471/2000000000 : ℝ)^39 ≤ (58238008881609/100000000000000 : ℝ)^31 := by
    have hnat : (1301365471 : ℕ)^39*100000000000000^31 ≤ 58238008881609^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301365471 2000000000 58238008881609 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16114181/5000000000 : ℝ)^39 ≤ (9164588121/12500000000000 : ℝ)^31 := by
    have hnat : (16114181 : ℕ)^39*12500000000000^31 ≤ 9164588121^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16114181 5000000000 9164588121 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988420943/10000000000 : ℝ)^39 ≤ (5211084300119/12500000000000 : ℝ)^31 := by
    have hnat : (4988420943 : ℕ)^39*12500000000000^31 ≤ 5211084300119^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988420943 10000000000 5211084300119 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301365471/2000000000 : ℝ), (-16114181/5000000000 : ℝ), (4988420943/10000000000 : ℝ)] ![(58238008881609/100000000000000 : ℝ), (9164588121/12500000000000 : ℝ), (5211084300119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301365471/2000000000 : ℝ)|^39 ≤ (58238008881609/100000000000000 : ℝ)^31
        have hw : |(1301365471/2000000000 : ℝ)|=(1301365471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16114181/5000000000 : ℝ)|^39 ≤ (9164588121/12500000000000 : ℝ)^31
        have hw : |(-16114181/5000000000 : ℝ)|=(16114181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988420943/10000000000 : ℝ)|^39 ≤ (5211084300119/12500000000000 : ℝ)^31
        have hw : |(4988420943/10000000000 : ℝ)|=(4988420943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3102913491/10000000000 : ℝ)*x 0 + (1449803941/2000000000 : ℝ)*x 1 + (-823716447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3102913491/10000000000 : ℝ)^39 ≤ (2867632315731/12500000000000 : ℝ)^31 := by
    have hnat : (3102913491 : ℕ)^39*12500000000000^31 ≤ 2867632315731^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102913491 10000000000 2867632315731 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1449803941/2000000000 : ℝ)^39 ≤ (13342964054031/20000000000000 : ℝ)^31 := by
    have hnat : (1449803941 : ℕ)^39*20000000000000^31 ≤ 13342964054031^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449803941 2000000000 13342964054031 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823716447/5000000000 : ℝ)^39 ≤ (5172060592943/50000000000000 : ℝ)^31 := by
    have hnat : (823716447 : ℕ)^39*50000000000000^31 ≤ 5172060592943^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823716447 5000000000 5172060592943 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3102913491/10000000000 : ℝ), (1449803941/2000000000 : ℝ), (-823716447/5000000000 : ℝ)] ![(2867632315731/12500000000000 : ℝ), (13342964054031/20000000000000 : ℝ), (5172060592943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3102913491/10000000000 : ℝ)|^39 ≤ (2867632315731/12500000000000 : ℝ)^31
        have hw : |(3102913491/10000000000 : ℝ)|=(3102913491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1449803941/2000000000 : ℝ)|^39 ≤ (13342964054031/20000000000000 : ℝ)^31
        have hw : |(1449803941/2000000000 : ℝ)|=(1449803941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-823716447/5000000000 : ℝ)|^39 ≤ (5172060592943/50000000000000 : ℝ)^31
        have hw : |(-823716447/5000000000 : ℝ)|=(823716447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (351888793/1250000000 : ℝ)*x 0 + (465937697/1000000000 : ℝ)*x 1 + (4965132607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351888793/1250000000 : ℝ)^39 ≤ (811876024611/4000000000000 : ℝ)^31 := by
    have hnat : (351888793 : ℕ)^39*4000000000000^31 ≤ 811876024611^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351888793 1250000000 811876024611 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465937697/1000000000 : ℝ)^39 ≤ (19129562596741/50000000000000 : ℝ)^31 := by
    have hnat : (465937697 : ℕ)^39*50000000000000^31 ≤ 19129562596741^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465937697 1000000000 19129562596741 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4965132607/10000000000 : ℝ)^39 ≤ (41443974175381/100000000000000 : ℝ)^31 := by
    have hnat : (4965132607 : ℕ)^39*100000000000000^31 ≤ 41443974175381^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965132607 10000000000 41443974175381 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(351888793/1250000000 : ℝ), (465937697/1000000000 : ℝ), (4965132607/10000000000 : ℝ)] ![(811876024611/4000000000000 : ℝ), (19129562596741/50000000000000 : ℝ), (41443974175381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(351888793/1250000000 : ℝ)|^39 ≤ (811876024611/4000000000000 : ℝ)^31
        have hw : |(351888793/1250000000 : ℝ)|=(351888793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465937697/1000000000 : ℝ)|^39 ≤ (19129562596741/50000000000000 : ℝ)^31
        have hw : |(465937697/1000000000 : ℝ)|=(465937697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4965132607/10000000000 : ℝ)|^39 ≤ (41443974175381/100000000000000 : ℝ)^31
        have hw : |(4965132607/10000000000 : ℝ)|=(4965132607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-704172379/5000000000 : ℝ)*x 0 + (118111003/312500000 : ℝ)*x 1 + (6847949633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704172379/5000000000 : ℝ)^39 ≤ (8492214923569/100000000000000 : ℝ)^31 := by
    have hnat : (704172379 : ℕ)^39*100000000000000^31 ≤ 8492214923569^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704172379 5000000000 8492214923569 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118111003/312500000 : ℝ)^39 ≤ (7350767547049/25000000000000 : ℝ)^31 := by
    have hnat : (118111003 : ℕ)^39*25000000000000^31 ≤ 7350767547049^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118111003 312500000 7350767547049 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6847949633/10000000000 : ℝ)^39 ≤ (3105235743619/5000000000000 : ℝ)^31 := by
    have hnat : (6847949633 : ℕ)^39*5000000000000^31 ≤ 3105235743619^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6847949633 10000000000 3105235743619 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-704172379/5000000000 : ℝ), (118111003/312500000 : ℝ), (6847949633/10000000000 : ℝ)] ![(8492214923569/100000000000000 : ℝ), (7350767547049/25000000000000 : ℝ), (3105235743619/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-704172379/5000000000 : ℝ)|^39 ≤ (8492214923569/100000000000000 : ℝ)^31
        have hw : |(-704172379/5000000000 : ℝ)|=(704172379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118111003/312500000 : ℝ)|^39 ≤ (7350767547049/25000000000000 : ℝ)^31
        have hw : |(118111003/312500000 : ℝ)|=(118111003/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6847949633/10000000000 : ℝ)|^39 ≤ (3105235743619/5000000000000 : ℝ)^31
        have hw : |(6847949633/10000000000 : ℝ)|=(6847949633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7839585327/10000000000 : ℝ)*x 0 + (-294169599/5000000000 : ℝ)*x 1 + (3167650203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7839585327/10000000000 : ℝ)^39 ≤ (73623064250129/100000000000000 : ℝ)^31 := by
    have hnat : (7839585327 : ℕ)^39*100000000000000^31 ≤ 73623064250129^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7839585327 10000000000 73623064250129 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294169599/5000000000 : ℝ)^39 ≤ (2832124712673/100000000000000 : ℝ)^31 := by
    have hnat : (294169599 : ℕ)^39*100000000000000^31 ≤ 2832124712673^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294169599 5000000000 2832124712673 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167650203/10000000000 : ℝ)^39 ≤ (1471550688509/6250000000000 : ℝ)^31 := by
    have hnat : (3167650203 : ℕ)^39*6250000000000^31 ≤ 1471550688509^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167650203 10000000000 1471550688509 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7839585327/10000000000 : ℝ), (-294169599/5000000000 : ℝ), (3167650203/10000000000 : ℝ)] ![(73623064250129/100000000000000 : ℝ), (2832124712673/100000000000000 : ℝ), (1471550688509/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7839585327/10000000000 : ℝ)|^39 ≤ (73623064250129/100000000000000 : ℝ)^31
        have hw : |(7839585327/10000000000 : ℝ)|=(7839585327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294169599/5000000000 : ℝ)|^39 ≤ (2832124712673/100000000000000 : ℝ)^31
        have hw : |(-294169599/5000000000 : ℝ)|=(294169599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167650203/10000000000 : ℝ)|^39 ≤ (1471550688509/6250000000000 : ℝ)^31
        have hw : |(3167650203/10000000000 : ℝ)|=(3167650203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3649490227/10000000000 : ℝ)*x 0 + (68917167/100000000 : ℝ)*x 1 + (-754303423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3649490227/10000000000 : ℝ)^39 ≤ (28135839039607/100000000000000 : ℝ)^31 := by
    have hnat : (3649490227 : ℕ)^39*100000000000000^31 ≤ 28135839039607^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3649490227 10000000000 28135839039607 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68917167/100000000 : ℝ)^39 ≤ (31302243374643/50000000000000 : ℝ)^31 := by
    have hnat : (68917167 : ℕ)^39*50000000000000^31 ≤ 31302243374643^31*100000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68917167 100000000 31302243374643 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754303423/5000000000 : ℝ)^39 ≤ (231491854931/2500000000000 : ℝ)^31 := by
    have hnat : (754303423 : ℕ)^39*2500000000000^31 ≤ 231491854931^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754303423 5000000000 231491854931 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3649490227/10000000000 : ℝ), (68917167/100000000 : ℝ), (-754303423/5000000000 : ℝ)] ![(28135839039607/100000000000000 : ℝ), (31302243374643/50000000000000 : ℝ), (231491854931/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3649490227/10000000000 : ℝ)|^39 ≤ (28135839039607/100000000000000 : ℝ)^31
        have hw : |(3649490227/10000000000 : ℝ)|=(3649490227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68917167/100000000 : ℝ)|^39 ≤ (31302243374643/50000000000000 : ℝ)^31
        have hw : |(68917167/100000000 : ℝ)|=(68917167/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-754303423/5000000000 : ℝ)|^39 ≤ (231491854931/2500000000000 : ℝ)^31
        have hw : |(-754303423/5000000000 : ℝ)|=(754303423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (618676003/2500000000 : ℝ)*x 0 + (1904726521/5000000000 : ℝ)*x 1 + (3020634711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (618676003/2500000000 : ℝ)^39 ≤ (17258900960569/100000000000000 : ℝ)^31 := by
    have hnat : (618676003 : ℕ)^39*100000000000000^31 ≤ 17258900960569^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618676003 2500000000 17258900960569 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904726521/5000000000 : ℝ)^39 ≤ (7424003179379/25000000000000 : ℝ)^31 := by
    have hnat : (1904726521 : ℕ)^39*25000000000000^31 ≤ 7424003179379^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904726521 5000000000 7424003179379 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3020634711/5000000000 : ℝ)^39 ≤ (2121803452057/4000000000000 : ℝ)^31 := by
    have hnat : (3020634711 : ℕ)^39*4000000000000^31 ≤ 2121803452057^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020634711 5000000000 2121803452057 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(618676003/2500000000 : ℝ), (1904726521/5000000000 : ℝ), (3020634711/5000000000 : ℝ)] ![(17258900960569/100000000000000 : ℝ), (7424003179379/25000000000000 : ℝ), (2121803452057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(618676003/2500000000 : ℝ)|^39 ≤ (17258900960569/100000000000000 : ℝ)^31
        have hw : |(618676003/2500000000 : ℝ)|=(618676003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1904726521/5000000000 : ℝ)|^39 ≤ (7424003179379/25000000000000 : ℝ)^31
        have hw : |(1904726521/5000000000 : ℝ)|=(1904726521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3020634711/5000000000 : ℝ)|^39 ≤ (2121803452057/4000000000000 : ℝ)^31
        have hw : |(3020634711/5000000000 : ℝ)|=(3020634711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1683482517/10000000000 : ℝ)*x 0 + (2737022739/5000000000 : ℝ)*x 1 + (2533345523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1683482517/10000000000 : ℝ)^39 ≤ (10629687821149/100000000000000 : ℝ)^31 := by
    have hnat : (1683482517 : ℕ)^39*100000000000000^31 ≤ 10629687821149^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683482517 10000000000 10629687821149 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737022739/5000000000 : ℝ)^39 ≤ (11714266338307/25000000000000 : ℝ)^31 := by
    have hnat : (2737022739 : ℕ)^39*25000000000000^31 ≤ 11714266338307^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737022739 5000000000 11714266338307 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2533345523/5000000000 : ℝ)^39 ≤ (42513246804407/100000000000000 : ℝ)^31 := by
    have hnat : (2533345523 : ℕ)^39*100000000000000^31 ≤ 42513246804407^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533345523 5000000000 42513246804407 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1683482517/10000000000 : ℝ), (2737022739/5000000000 : ℝ), (2533345523/5000000000 : ℝ)] ![(10629687821149/100000000000000 : ℝ), (11714266338307/25000000000000 : ℝ), (42513246804407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1683482517/10000000000 : ℝ)|^39 ≤ (10629687821149/100000000000000 : ℝ)^31
        have hw : |(-1683482517/10000000000 : ℝ)|=(1683482517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737022739/5000000000 : ℝ)|^39 ≤ (11714266338307/25000000000000 : ℝ)^31
        have hw : |(2737022739/5000000000 : ℝ)|=(2737022739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2533345523/5000000000 : ℝ)|^39 ≤ (42513246804407/100000000000000 : ℝ)^31
        have hw : |(2533345523/5000000000 : ℝ)|=(2533345523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1490713563/2000000000 : ℝ)*x 0 + (-34333723/10000000000 : ℝ)*x 1 + (1962262647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1490713563/2000000000 : ℝ)^39 ≤ (69091709455129/100000000000000 : ℝ)^31 := by
    have hnat : (1490713563 : ℕ)^39*100000000000000^31 ≤ 69091709455129^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490713563 2000000000 69091709455129 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34333723/10000000000 : ℝ)^39 ≤ (7939221253/10000000000000 : ℝ)^31 := by
    have hnat : (34333723 : ℕ)^39*10000000000000^31 ≤ 7939221253^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34333723 10000000000 7939221253 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962262647/5000000000 : ℝ)^39 ≤ (30828898323513/100000000000000 : ℝ)^31 := by
    have hnat : (1962262647 : ℕ)^39*100000000000000^31 ≤ 30828898323513^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962262647 5000000000 30828898323513 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1490713563/2000000000 : ℝ), (-34333723/10000000000 : ℝ), (1962262647/5000000000 : ℝ)] ![(69091709455129/100000000000000 : ℝ), (7939221253/10000000000000 : ℝ), (30828898323513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1490713563/2000000000 : ℝ)|^39 ≤ (69091709455129/100000000000000 : ℝ)^31
        have hw : |(1490713563/2000000000 : ℝ)|=(1490713563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34333723/10000000000 : ℝ)|^39 ≤ (7939221253/10000000000000 : ℝ)^31
        have hw : |(-34333723/10000000000 : ℝ)|=(34333723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1962262647/5000000000 : ℝ)|^39 ≤ (30828898323513/100000000000000 : ℝ)^31
        have hw : |(1962262647/5000000000 : ℝ)|=(1962262647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3410811443/10000000000 : ℝ)*x 0 + (6542716087/10000000000 : ℝ)*x 1 + (-2274012251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3410811443/10000000000 : ℝ)^39 ≤ (6460183754639/25000000000000 : ℝ)^31 := by
    have hnat : (3410811443 : ℕ)^39*25000000000000^31 ≤ 6460183754639^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410811443 10000000000 6460183754639 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6542716087/10000000000 : ℝ)^39 ≤ (29321202422661/50000000000000 : ℝ)^31 := by
    have hnat : (6542716087 : ℕ)^39*50000000000000^31 ≤ 29321202422661^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6542716087 10000000000 29321202422661 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274012251/10000000000 : ℝ)^39 ≤ (15516860125117/100000000000000 : ℝ)^31 := by
    have hnat : (2274012251 : ℕ)^39*100000000000000^31 ≤ 15516860125117^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274012251 10000000000 15516860125117 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3410811443/10000000000 : ℝ), (6542716087/10000000000 : ℝ), (-2274012251/10000000000 : ℝ)] ![(6460183754639/25000000000000 : ℝ), (29321202422661/50000000000000 : ℝ), (15516860125117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3410811443/10000000000 : ℝ)|^39 ≤ (6460183754639/25000000000000 : ℝ)^31
        have hw : |(3410811443/10000000000 : ℝ)|=(3410811443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6542716087/10000000000 : ℝ)|^39 ≤ (29321202422661/50000000000000 : ℝ)^31
        have hw : |(6542716087/10000000000 : ℝ)|=(6542716087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2274012251/10000000000 : ℝ)|^39 ≤ (15516860125117/100000000000000 : ℝ)^31
        have hw : |(-2274012251/10000000000 : ℝ)|=(2274012251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317083_s1_s1_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (676518271/2000000000 : ℝ)*x 0 + (4672813291/10000000000 : ℝ)*x 1 + (4442267093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676518271/2000000000 : ℝ)^39 ≤ (319650623969/1250000000000 : ℝ)^31 := by
    have hnat : (676518271 : ℕ)^39*1250000000000^31 ≤ 319650623969^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676518271 2000000000 319650623969 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4672813291/10000000000 : ℝ)^39 ≤ (1535919084973/4000000000000 : ℝ)^31 := by
    have hnat : (4672813291 : ℕ)^39*4000000000000^31 ≤ 1535919084973^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4672813291 10000000000 1535919084973 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4442267093/10000000000 : ℝ)^39 ≤ (36029972948527/100000000000000 : ℝ)^31 := by
    have hnat : (4442267093 : ℕ)^39*100000000000000^31 ≤ 36029972948527^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442267093 10000000000 36029972948527 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676518271/2000000000 : ℝ), (4672813291/10000000000 : ℝ), (4442267093/10000000000 : ℝ)] ![(319650623969/1250000000000 : ℝ), (1535919084973/4000000000000 : ℝ), (36029972948527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676518271/2000000000 : ℝ)|^39 ≤ (319650623969/1250000000000 : ℝ)^31
        have hw : |(676518271/2000000000 : ℝ)|=(676518271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4672813291/10000000000 : ℝ)|^39 ≤ (1535919084973/4000000000000 : ℝ)^31
        have hw : |(4672813291/10000000000 : ℝ)|=(4672813291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4442267093/10000000000 : ℝ)|^39 ≤ (36029972948527/100000000000000 : ℝ)^31
        have hw : |(4442267093/10000000000 : ℝ)|=(4442267093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317083_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((67011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6657/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6657/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(73121/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14419/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14419/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((14339/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(14339/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15307/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (67011/100000 : ℝ) ^ (77/16 : ℝ) ≤ (7282795336236706397/50000000000000000000 : ℝ) := by
    have hpowers : (67011/100000 : ℝ)^77 ≤ (7282795336236706397/50000000000000000000 : ℝ)^16 := by
      have hnat : (67011 : ℕ)^77*50000000000000000000^16 ≤ 7282795336236706397^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67011 100000 7282795336236706397 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67011/100000 : ℝ)) (X := (7282795336236706397/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (57282795336236706397/50000000000000000000 : ℝ) ≤ (10286579865027339/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (57282795336236706397/50000000000000000000 : ℝ)^16 ≤ (10286579865027339/10000000000000000 : ℝ)^77 := by
      have hnat : (57282795336236706397 : ℕ)^16*10000000000000000^77 ≤ 10286579865027339^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57282795336236706397 50000000000000000000 10286579865027339 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10286579865027339/10000000000000000 : ℝ)) (X := (57282795336236706397/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (32282795336236706397/25000000000000000000 : ℝ) ≤ (10545602625489961/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (32282795336236706397/25000000000000000000 : ℝ)^16 ≤ (10545602625489961/10000000000000000 : ℝ)^77 := by
      have hnat : (32282795336236706397 : ℕ)^16*10000000000000000^77 ≤ 10545602625489961^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32282795336236706397 25000000000000000000 10545602625489961 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10545602625489961/10000000000000000 : ℝ)) (X := (32282795336236706397/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(286579865027339/6701100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(129511380231311/3350550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (67011/100000 : ℝ)) (alpha := (286579865027339/6701100000000000 : ℝ)) (beta := (129511380231311/3350550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (67011/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(286579865027339/6701100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(129511380231311/3350550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6657/10000 : ℝ) ^ (77/16 : ℝ) ≤ (7055016920142318659/50000000000000000000 : ℝ) := by
    have hpowers : (6657/10000 : ℝ)^77 ≤ (7055016920142318659/50000000000000000000 : ℝ)^16 := by
      have hnat : (6657 : ℕ)^77*50000000000000000000^16 ≤ 7055016920142318659^16*10000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6657 10000 7055016920142318659 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6657/10000 : ℝ)) (X := (7055016920142318659/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (57055016920142318659/50000000000000000000 : ℝ) ≤ (10278067039063489/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (57055016920142318659/50000000000000000000 : ℝ)^16 ≤ (10278067039063489/10000000000000000 : ℝ)^77 := by
      have hnat : (57055016920142318659 : ℕ)^16*10000000000000000^77 ≤ 10278067039063489^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57055016920142318659 50000000000000000000 10278067039063489 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10278067039063489/10000000000000000 : ℝ)) (X := (57055016920142318659/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (32055016920142318659/25000000000000000000 : ℝ) ≤ (1316262258857407/1250000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (32055016920142318659/25000000000000000000 : ℝ)^16 ≤ (1316262258857407/1250000000000000 : ℝ)^77 := by
      have hnat : (32055016920142318659 : ℕ)^16*1250000000000000^77 ≤ 1316262258857407^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32055016920142318659 25000000000000000000 1316262258857407 1250000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1316262258857407/1250000000000000 : ℝ)) (X := (32055016920142318659/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(92689013021163/2219000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(36004433113681/951000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (6657/10000 : ℝ)) (alpha := (92689013021163/2219000000000000 : ℝ)) (beta := (36004433113681/951000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (6657/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(92689013021163/2219000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(36004433113681/951000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (73121/100000 : ℝ) ^ (77/16 : ℝ) ≤ (22166785199517339113/100000000000000000000 : ℝ) := by
    have hpowers : (73121/100000 : ℝ)^77 ≤ (22166785199517339113/100000000000000000000 : ℝ)^16 := by
      have hnat : (73121 : ℕ)^77*100000000000000000000^16 ≤ 22166785199517339113^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73121 100000 22166785199517339113 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73121/100000 : ℝ)) (X := (22166785199517339113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (122166785199517339113/100000000000000000000 : ℝ) ≤ (10424810905701341/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (122166785199517339113/100000000000000000000 : ℝ)^16 ≤ (10424810905701341/10000000000000000 : ℝ)^77 := by
      have hnat : (122166785199517339113 : ℕ)^16*10000000000000000^77 ≤ 10424810905701341^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122166785199517339113 100000000000000000000 10424810905701341 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10424810905701341/10000000000000000 : ℝ)) (X := (122166785199517339113/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (72166785199517339113/50000000000000000000 : ℝ) ≤ (10792331941536263/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (72166785199517339113/50000000000000000000 : ℝ)^16 ≤ (10792331941536263/10000000000000000 : ℝ)^77 := by
      have hnat : (72166785199517339113 : ℕ)^16*10000000000000000^77 ≤ 10792331941536263^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72166785199517339113 50000000000000000000 10792331941536263 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10792331941536263/10000000000000000 : ℝ)) (X := (72166785199517339113/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(424810905701341/7312100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(183760517917461/3656050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (73121/100000 : ℝ)) (alpha := (424810905701341/7312100000000000 : ℝ)) (beta := (183760517917461/3656050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (73121/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(424810905701341/7312100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(183760517917461/3656050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1128202513/5000000000 : ℝ)*X 0 0+(2405346283/5000000000 : ℝ)*X 0 1+(528265501/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6793810717/10000000000 : ℝ)*X 1 0+(-197313327/2500000000 : ℝ)*X 1 1+(85662777/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((710920117/2000000000 : ℝ)*X 2 0+(6398965169/10000000000 : ℝ)*X 2 1+(-2301745737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-568686467/2500000000 : ℝ)*X 0 0+(2387510251/5000000000 : ℝ)*X 0 1+(530269139/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1301365471/2000000000 : ℝ)*X 1 0+(-16114181/5000000000 : ℝ)*X 1 1+(4988420943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3102913491/10000000000 : ℝ)*X 2 0+(1449803941/2000000000 : ℝ)*X 2 1+(-823716447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((351888793/1250000000 : ℝ)*X 0 0+(465937697/1000000000 : ℝ)*X 0 1+(4965132607/10000000000 : ℝ)*X 0 2+(351888793/1250000000 : ℝ)*X 1 0+(465937697/1000000000 : ℝ)*X 1 1+(4965132607/10000000000 : ℝ)*X 1 2+(351888793/1250000000 : ℝ)*X 2 0+(465937697/1000000000 : ℝ)*X 2 1+(4965132607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-704172379/5000000000 : ℝ)*X 0 0+(118111003/312500000 : ℝ)*X 0 1+(6847949633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7839585327/10000000000 : ℝ)*X 1 0+(-294169599/5000000000 : ℝ)*X 1 1+(3167650203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3649490227/10000000000 : ℝ)*X 2 0+(68917167/100000000 : ℝ)*X 2 1+(-754303423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((618676003/2500000000 : ℝ)*X 0 0+(1904726521/5000000000 : ℝ)*X 0 1+(3020634711/5000000000 : ℝ)*X 0 2+(618676003/2500000000 : ℝ)*X 1 0+(1904726521/5000000000 : ℝ)*X 1 1+(3020634711/5000000000 : ℝ)*X 1 2+(618676003/2500000000 : ℝ)*X 2 0+(1904726521/5000000000 : ℝ)*X 2 1+(3020634711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1683482517/10000000000 : ℝ)*X 0 0+(2737022739/5000000000 : ℝ)*X 0 1+(2533345523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1490713563/2000000000 : ℝ)*X 1 0+(-34333723/10000000000 : ℝ)*X 1 1+(1962262647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3410811443/10000000000 : ℝ)*X 2 0+(6542716087/10000000000 : ℝ)*X 2 1+(-2274012251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((676518271/2000000000 : ℝ)*X 0 0+(4672813291/10000000000 : ℝ)*X 0 1+(4442267093/10000000000 : ℝ)*X 0 2+(676518271/2000000000 : ℝ)*X 1 0+(4672813291/10000000000 : ℝ)*X 1 1+(4442267093/10000000000 : ℝ)*X 1 2+(676518271/2000000000 : ℝ)*X 2 0+(4672813291/10000000000 : ℝ)*X 2 1+(4442267093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((14419/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14419/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17615107871145268009991924943/3235983108181250000000000000000000 : ℝ) := by norm_num
    linear_combination (3678337/1000000000000 : ℝ)*(base19) + (23927030847/125000000000 : ℝ)*(base40) + (332761387789/250000000000 : ℝ)*(base49) + (9211061033/20000000000 : ℝ)*(base60) + (452910866797/100000000000 : ℝ)*(major_s1_0) + (452910866797/100000000000 : ℝ)*(major_s1_1) + (452910866797/100000000000 : ℝ)*(major_s1_2) + (147217897/125000000000 : ℝ)*(sp_s1_0) + (8364433/1000000000000 : ℝ)*(sp_s1_1) + (1634733937791/250000000000 : ℝ)*(sp_s1_7) + (654010145157/100000000000 : ℝ)*(sp_s1_8) + (327005674717/50000000000 : ℝ)*(sp_s1_9) + (1259035589039/500000000000 : ℝ)*(sp_s1_13) + (6169803/200000000000 : ℝ)*(sp_s1_20) + (2518102027093/1000000000000 : ℝ)*(f.failure) + (327005674717/50000000000 : ℝ)*(f.sum) + (6209094363253828033/6953807100000000000000000000000 : ℝ)*base63 + (2817397011603/4570062500000000000000000 : ℝ)*base64 + (34085122382329/221900000000000000000000000 : ℝ)*base66 + (217930425172097/365605000000000000000000000 : ℝ)*base69 + (20458389085393438649/48999113310000000000000000000000 : ℝ)*base70 + (154198938261931/335055000000000000000000000 : ℝ)*base72 + (23870047826723/95100000000000000000000000 : ℝ)*base75 + (77857563323707/670110000000000000000000000 : ℝ)*base76 + (852955689402863/2124248700000000000000000000000 : ℝ)*base79 + (583/50000000000000000 : ℝ)*base87 + (583/50000000000000000 : ℝ)*base89 + (583/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((14339/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(14339/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (266358072181161401184931725111/18491332046750000000000000000000000 : ℝ) := by norm_num
    linear_combination (3520633/200000000000 : ℝ)*(base21) + (433536237341/500000000000 : ℝ)*(base40) + (1051551075989/1000000000000 : ℝ)*(base49) + (373787308577/500000000000 : ℝ)*(base60) + (55218175803/15625000000 : ℝ)*(major_s1_0) + (55218175803/15625000000 : ℝ)*(major_s1_1) + (55218175803/15625000000 : ℝ)*(major_s1_2) + (12561603/500000000000 : ℝ)*(sp_s1_1) + (12951431/1000000000000 : ℝ)*(sp_s1_2) + (2551551211199/500000000000 : ℝ)*(sp_s1_14) + (2551509831941/500000000000 : ℝ)*(sp_s1_15) + (2551535933901/500000000000 : ℝ)*(sp_s1_16) + (1964819278887/1000000000000 : ℝ)*(sp_s1_20) + (5763531/100000000000 : ℝ)*(sp_s1_22) + (1964819278887/1000000000000 : ℝ)*(f.failure) + (2551551211199/500000000000 : ℝ)*(f.sum) + (119463948178776409/362177453125000000000000000000 : ℝ)*base63 + (741645067298101/1828025000000000000000000000 : ℝ)*base65 + (1443154824727/4953125000000000000000000 : ℝ)*base67 + (306558567180143/1828025000000000000000000000 : ℝ)*base69 + (370577468960511321/729153471875000000000000000000 : ℝ)*base71 + (567498103829/4985937500000000000000000 : ℝ)*base72 + (62256030673979/79250000000000000000000000 : ℝ)*base75 + (92347085423849/159550000000000000000000000 : ℝ)*base77 + (68860425561691893/252886750000000000000000000000 : ℝ)*base78 + (13203/50000000000000000 : ℝ)*base86 + (13203/50000000000000000 : ℝ)*base88 + (13203/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15307/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (275331200230392955285910925241/64719662163625000000000000000000000 : ℝ) := by norm_num
    linear_combination (409359/250000000000 : ℝ)*(base11) + (392223244199/500000000000 : ℝ)*(base40) + (1364894619539/1000000000000 : ℝ)*(base49) + (125763/100000000000 : ℝ)*(base50) + (605979474511/125000000000 : ℝ)*(major_s1_0) + (605979474511/125000000000 : ℝ)*(major_s1_1) + (605979474511/125000000000 : ℝ)*(major_s1_2) + (7327139/125000000000 : ℝ)*(sp_s1_2) + (16476821/1000000000000 : ℝ)*(sp_s1_15) + (25590703/1000000000000 : ℝ)*(sp_s1_16) + (700036002453/100000000000 : ℝ)*(sp_s1_21) + (875043148143/125000000000 : ℝ)*(sp_s1_22) + (7000277454151/1000000000000 : ℝ)*(sp_s1_23) + (269530851213/100000000000 : ℝ)*(sp_s1_27) + (269530851213/100000000000 : ℝ)*(f.failure) + (3500180830983/500000000000 : ℝ)*(f.sum) + (4229446990387600849/8692258875000000000000000000000 : ℝ)*base63 + (172541962532359/1828025000000000000000000000 : ℝ)*base65 + (33000989059917/69343750000000000000000000 : ℝ)*base67 + (3465370839375919/3656050000000000000000000000 : ℝ)*base69 + (11969208607760538179/61248891637500000000000000000000 : ℝ)*base70 + (3301733289266473/3350550000000000000000000000 : ℝ)*base73 + (79210727703209/118875000000000000000000000 : ℝ)*base75 + (321899999444809/3350550000000000000000000000 : ℝ)*base76 + (2648580769173256333/5310621750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (3697/5000000000000000 : ℝ)*base86 + (3697/5000000000000000 : ℝ)*base88 + (3697/5000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((67011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6657/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6657/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(73121/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14419/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14419/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((14339/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(14339/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15307/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317083_s1 p hpa hpb X hX hprev0

#print axioms solution

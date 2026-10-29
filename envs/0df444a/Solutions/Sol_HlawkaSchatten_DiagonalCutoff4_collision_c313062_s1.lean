-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:52.560052+00:00
-- url     : https://prove2.me/submissions/00f8938d-dbdb-43fb-9317-8119a95650ba

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
theorem collision_support_c313062_s1_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1204391301/10000000000 : ℝ)*x 0 + (5039625581/10000000000 : ℝ)*x 1 + (-743826299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1204391301/10000000000 : ℝ)^37 ≤ (3358584392349/50000000000000 : ℝ)^29 := by
    have hnat : (1204391301 : ℕ)^37*50000000000000^29 ≤ 3358584392349^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204391301 10000000000 3358584392349 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5039625581/10000000000 : ℝ)^37 ≤ (10428966007783/25000000000000 : ℝ)^29 := by
    have hnat : (5039625581 : ℕ)^37*25000000000000^29 ≤ 10428966007783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039625581 10000000000 10428966007783 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743826299/1250000000 : ℝ)^37 ≤ (12891741793457/25000000000000 : ℝ)^29 := by
    have hnat : (743826299 : ℕ)^37*25000000000000^29 ≤ 12891741793457^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743826299 1250000000 12891741793457 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1204391301/10000000000 : ℝ), (5039625581/10000000000 : ℝ), (-743826299/1250000000 : ℝ)] ![(3358584392349/50000000000000 : ℝ), (10428966007783/25000000000000 : ℝ), (12891741793457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1204391301/10000000000 : ℝ)|^37 ≤ (3358584392349/50000000000000 : ℝ)^29
        have hw : |(-1204391301/10000000000 : ℝ)|=(1204391301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5039625581/10000000000 : ℝ)|^37 ≤ (10428966007783/25000000000000 : ℝ)^29
        have hw : |(5039625581/10000000000 : ℝ)|=(5039625581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-743826299/1250000000 : ℝ)|^37 ≤ (12891741793457/25000000000000 : ℝ)^29
        have hw : |(-743826299/1250000000 : ℝ)|=(743826299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5075101533/10000000000 : ℝ)*x 0 + (-610614971/5000000000 : ℝ)*x 1 + (-2952893189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5075101533/10000000000 : ℝ)^37 ≤ (263068063447/625000000000 : ℝ)^29 := by
    have hnat : (5075101533 : ℕ)^37*625000000000^29 ≤ 263068063447^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075101533 10000000000 263068063447 625000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610614971/5000000000 : ℝ)^37 ≤ (3418609550179/50000000000000 : ℝ)^29 := by
    have hnat : (610614971 : ℕ)^37*50000000000000^29 ≤ 3418609550179^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610614971 5000000000 3418609550179 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2952893189/5000000000 : ℝ)^37 ≤ (797998292727/1562500000000 : ℝ)^29 := by
    have hnat : (2952893189 : ℕ)^37*1562500000000^29 ≤ 797998292727^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2952893189 5000000000 797998292727 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5075101533/10000000000 : ℝ), (-610614971/5000000000 : ℝ), (-2952893189/5000000000 : ℝ)] ![(263068063447/625000000000 : ℝ), (3418609550179/50000000000000 : ℝ), (797998292727/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5075101533/10000000000 : ℝ)|^37 ≤ (263068063447/625000000000 : ℝ)^29
        have hw : |(5075101533/10000000000 : ℝ)|=(5075101533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610614971/5000000000 : ℝ)|^37 ≤ (3418609550179/50000000000000 : ℝ)^29
        have hw : |(-610614971/5000000000 : ℝ)|=(610614971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2952893189/5000000000 : ℝ)|^37 ≤ (797998292727/1562500000000 : ℝ)^29
        have hw : |(-2952893189/5000000000 : ℝ)|=(2952893189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5308645809/10000000000 : ℝ)*x 0 + (5350543239/10000000000 : ℝ)*x 1 + (1695953193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5308645809/10000000000 : ℝ)^37 ≤ (22288826470533/50000000000000 : ℝ)^29 := by
    have hnat : (5308645809 : ℕ)^37*50000000000000^29 ≤ 22288826470533^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5308645809 10000000000 22288826470533 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5350543239/10000000000 : ℝ)^37 ≤ (45027014766239/100000000000000 : ℝ)^29 := by
    have hnat : (5350543239 : ℕ)^37*100000000000000^29 ≤ 45027014766239^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350543239 10000000000 45027014766239 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1695953193/10000000000 : ℝ)^37 ≤ (2079066454519/20000000000000 : ℝ)^29 := by
    have hnat : (1695953193 : ℕ)^37*20000000000000^29 ≤ 2079066454519^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695953193 10000000000 2079066454519 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5308645809/10000000000 : ℝ), (5350543239/10000000000 : ℝ), (1695953193/10000000000 : ℝ)] ![(22288826470533/50000000000000 : ℝ), (45027014766239/100000000000000 : ℝ), (2079066454519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5308645809/10000000000 : ℝ)|^37 ≤ (22288826470533/50000000000000 : ℝ)^29
        have hw : |(5308645809/10000000000 : ℝ)|=(5308645809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5350543239/10000000000 : ℝ)|^37 ≤ (45027014766239/100000000000000 : ℝ)^29
        have hw : |(5350543239/10000000000 : ℝ)|=(5350543239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1695953193/10000000000 : ℝ)|^37 ≤ (2079066454519/20000000000000 : ℝ)^29
        have hw : |(1695953193/10000000000 : ℝ)|=(1695953193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-356386459/2500000000 : ℝ)*x 0 + (3310598209/10000000000 : ℝ)*x 1 + (-7328785437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356386459/2500000000 : ℝ)^37 ≤ (8329073325133/100000000000000 : ℝ)^29 := by
    have hnat : (356386459 : ℕ)^37*100000000000000^29 ≤ 8329073325133^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356386459 2500000000 8329073325133 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3310598209/10000000000 : ℝ)^37 ≤ (1220216482871/5000000000000 : ℝ)^29 := by
    have hnat : (3310598209 : ℕ)^37*5000000000000^29 ≤ 1220216482871^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3310598209 10000000000 1220216482871 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7328785437/10000000000 : ℝ)^37 ≤ (33633298500473/50000000000000 : ℝ)^29 := by
    have hnat : (7328785437 : ℕ)^37*50000000000000^29 ≤ 33633298500473^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7328785437 10000000000 33633298500473 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356386459/2500000000 : ℝ), (3310598209/10000000000 : ℝ), (-7328785437/10000000000 : ℝ)] ![(8329073325133/100000000000000 : ℝ), (1220216482871/5000000000000 : ℝ), (33633298500473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356386459/2500000000 : ℝ)|^37 ≤ (8329073325133/100000000000000 : ℝ)^29
        have hw : |(-356386459/2500000000 : ℝ)|=(356386459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3310598209/10000000000 : ℝ)|^37 ≤ (1220216482871/5000000000000 : ℝ)^29
        have hw : |(3310598209/10000000000 : ℝ)|=(3310598209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7328785437/10000000000 : ℝ)|^37 ≤ (33633298500473/50000000000000 : ℝ)^29
        have hw : |(-7328785437/10000000000 : ℝ)|=(7328785437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1906205191/5000000000 : ℝ)*x 0 + (-149605471/2000000000 : ℝ)*x 1 + (-91456003/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906205191/5000000000 : ℝ)^37 ≤ (29219212758811/100000000000000 : ℝ)^29 := by
    have hnat : (1906205191 : ℕ)^37*100000000000000^29 ≤ 29219212758811^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906205191 5000000000 29219212758811 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149605471/2000000000 : ℝ)^37 ≤ (1829127716807/50000000000000 : ℝ)^29 := by
    have hnat : (149605471 : ℕ)^37*50000000000000^29 ≤ 1829127716807^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149605471 2000000000 1829127716807 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91456003/125000000 : ℝ)^37 ≤ (16387336863/24414062500 : ℝ)^29 := by
    have hnat : (91456003 : ℕ)^37*24414062500^29 ≤ 16387336863^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91456003 125000000 16387336863 24414062500 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1906205191/5000000000 : ℝ), (-149605471/2000000000 : ℝ), (-91456003/125000000 : ℝ)] ![(29219212758811/100000000000000 : ℝ), (1829127716807/50000000000000 : ℝ), (16387336863/24414062500 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1906205191/5000000000 : ℝ)|^37 ≤ (29219212758811/100000000000000 : ℝ)^29
        have hw : |(1906205191/5000000000 : ℝ)|=(1906205191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149605471/2000000000 : ℝ)|^37 ≤ (1829127716807/50000000000000 : ℝ)^29
        have hw : |(-149605471/2000000000 : ℝ)|=(149605471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91456003/125000000 : ℝ)|^37 ≤ (16387336863/24414062500 : ℝ)^29
        have hw : |(-91456003/125000000 : ℝ)|=(91456003/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (777297869/2000000000 : ℝ)*x 0 + (6966182471/10000000000 : ℝ)*x 1 + (622312053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777297869/2000000000 : ℝ)^37 ≤ (29945526900743/100000000000000 : ℝ)^29 := by
    have hnat : (777297869 : ℕ)^37*100000000000000^29 ≤ 29945526900743^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777297869 2000000000 29945526900743 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6966182471/10000000000 : ℝ)^37 ≤ (31524853995329/50000000000000 : ℝ)^29 := by
    have hnat : (6966182471 : ℕ)^37*50000000000000^29 ≤ 31524853995329^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966182471 10000000000 31524853995329 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622312053/5000000000 : ℝ)^37 ≤ (7004765097827/100000000000000 : ℝ)^29 := by
    have hnat : (622312053 : ℕ)^37*100000000000000^29 ≤ 7004765097827^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622312053 5000000000 7004765097827 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777297869/2000000000 : ℝ), (6966182471/10000000000 : ℝ), (622312053/5000000000 : ℝ)] ![(29945526900743/100000000000000 : ℝ), (31524853995329/50000000000000 : ℝ), (7004765097827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777297869/2000000000 : ℝ)|^37 ≤ (29945526900743/100000000000000 : ℝ)^29
        have hw : |(777297869/2000000000 : ℝ)|=(777297869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6966182471/10000000000 : ℝ)|^37 ≤ (31524853995329/50000000000000 : ℝ)^29
        have hw : |(6966182471/10000000000 : ℝ)|=(6966182471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622312053/5000000000 : ℝ)|^37 ≤ (7004765097827/100000000000000 : ℝ)^29
        have hw : |(622312053/5000000000 : ℝ)|=(622312053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4274973741/10000000000 : ℝ)*x 0 + (7231429349/10000000000 : ℝ)*x 1 + (-1401549/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274973741/10000000000 : ℝ)^37 ≤ (16907990458651/50000000000000 : ℝ)^29 := by
    have hnat : (4274973741 : ℕ)^37*50000000000000^29 ≤ 16907990458651^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274973741 10000000000 16907990458651 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7231429349/10000000000 : ℝ)^37 ≤ (66128615404469/100000000000000 : ℝ)^29 := by
    have hnat : (7231429349 : ℕ)^37*100000000000000^29 ≤ 66128615404469^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7231429349 10000000000 66128615404469 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401549/500000000 : ℝ)^37 ≤ (55403665319/100000000000000 : ℝ)^29 := by
    have hnat : (1401549 : ℕ)^37*100000000000000^29 ≤ 55403665319^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401549 500000000 55403665319 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274973741/10000000000 : ℝ), (7231429349/10000000000 : ℝ), (-1401549/500000000 : ℝ)] ![(16907990458651/50000000000000 : ℝ), (66128615404469/100000000000000 : ℝ), (55403665319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274973741/10000000000 : ℝ)|^37 ≤ (16907990458651/50000000000000 : ℝ)^29
        have hw : |(4274973741/10000000000 : ℝ)|=(4274973741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7231429349/10000000000 : ℝ)|^37 ≤ (66128615404469/100000000000000 : ℝ)^29
        have hw : |(7231429349/10000000000 : ℝ)|=(7231429349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1401549/500000000 : ℝ)|^37 ≤ (55403665319/100000000000000 : ℝ)^29
        have hw : |(-1401549/500000000 : ℝ)|=(1401549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-368415109/5000000000 : ℝ)*x 0 + (75061663/200000000 : ℝ)*x 1 + (-7371835281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368415109/5000000000 : ℝ)^37 ≤ (358853398641/10000000000000 : ℝ)^29 := by
    have hnat : (368415109 : ℕ)^37*10000000000000^29 ≤ 358853398641^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368415109 5000000000 358853398641 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75061663/200000000 : ℝ)^37 ≤ (14320165434631/50000000000000 : ℝ)^29 := by
    have hnat : (75061663 : ℕ)^37*50000000000000^29 ≤ 14320165434631^29*200000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75061663 200000000 14320165434631 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7371835281/10000000000 : ℝ)^37 ≤ (33885567564581/50000000000000 : ℝ)^29 := by
    have hnat : (7371835281 : ℕ)^37*50000000000000^29 ≤ 33885567564581^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7371835281 10000000000 33885567564581 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368415109/5000000000 : ℝ), (75061663/200000000 : ℝ), (-7371835281/10000000000 : ℝ)] ![(358853398641/10000000000000 : ℝ), (14320165434631/50000000000000 : ℝ), (33885567564581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368415109/5000000000 : ℝ)|^37 ≤ (358853398641/10000000000000 : ℝ)^29
        have hw : |(-368415109/5000000000 : ℝ)|=(368415109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75061663/200000000 : ℝ)|^37 ≤ (14320165434631/50000000000000 : ℝ)^29
        have hw : |(75061663/200000000 : ℝ)|=(75061663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7371835281/10000000000 : ℝ)|^37 ≤ (33885567564581/50000000000000 : ℝ)^29
        have hw : |(-7371835281/10000000000 : ℝ)|=(7371835281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3268631103/10000000000 : ℝ)*x 0 + (-715098981/5000000000 : ℝ)*x 1 + (-1471890297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3268631103/10000000000 : ℝ)^37 ≤ (480206328849/2000000000000 : ℝ)^29 := by
    have hnat : (3268631103 : ℕ)^37*2000000000000^29 ≤ 480206328849^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3268631103 10000000000 480206328849 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715098981/5000000000 : ℝ)^37 ≤ (167275365051/2000000000000 : ℝ)^29 := by
    have hnat : (715098981 : ℕ)^37*2000000000000^29 ≤ 167275365051^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715098981 5000000000 167275365051 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1471890297/2000000000 : ℝ)^37 ≤ (67625915283507/100000000000000 : ℝ)^29 := by
    have hnat : (1471890297 : ℕ)^37*100000000000000^29 ≤ 67625915283507^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471890297 2000000000 67625915283507 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3268631103/10000000000 : ℝ), (-715098981/5000000000 : ℝ), (-1471890297/2000000000 : ℝ)] ![(480206328849/2000000000000 : ℝ), (167275365051/2000000000000 : ℝ), (67625915283507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3268631103/10000000000 : ℝ)|^37 ≤ (480206328849/2000000000000 : ℝ)^29
        have hw : |(3268631103/10000000000 : ℝ)|=(3268631103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715098981/5000000000 : ℝ)|^37 ≤ (167275365051/2000000000000 : ℝ)^29
        have hw : |(-715098981/5000000000 : ℝ)|=(715098981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1471890297/2000000000 : ℝ)|^37 ≤ (67625915283507/100000000000000 : ℝ)^29
        have hw : |(-1471890297/2000000000 : ℝ)|=(1471890297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6764983171/10000000000 : ℝ)*x 0 + (256950099/625000000 : ℝ)*x 1 + (314202689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6764983171/10000000000 : ℝ)^37 ≤ (12147131767633/20000000000000 : ℝ)^29 := by
    have hnat : (6764983171 : ℕ)^37*20000000000000^29 ≤ 12147131767633^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6764983171 10000000000 12147131767633 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256950099/625000000 : ℝ)^37 ≤ (6434390202879/20000000000000 : ℝ)^29 := by
    have hnat : (256950099 : ℕ)^37*20000000000000^29 ≤ 6434390202879^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256950099 625000000 6434390202879 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314202689/2500000000 : ℝ)^37 ≤ (7092390130123/100000000000000 : ℝ)^29 := by
    have hnat : (314202689 : ℕ)^37*100000000000000^29 ≤ 7092390130123^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314202689 2500000000 7092390130123 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6764983171/10000000000 : ℝ), (256950099/625000000 : ℝ), (314202689/2500000000 : ℝ)] ![(12147131767633/20000000000000 : ℝ), (6434390202879/20000000000000 : ℝ), (7092390130123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6764983171/10000000000 : ℝ)|^37 ≤ (12147131767633/20000000000000 : ℝ)^29
        have hw : |(6764983171/10000000000 : ℝ)|=(6764983171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256950099/625000000 : ℝ)|^37 ≤ (6434390202879/20000000000000 : ℝ)^29
        have hw : |(256950099/625000000 : ℝ)|=(256950099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314202689/2500000000 : ℝ)|^37 ≤ (7092390130123/100000000000000 : ℝ)^29
        have hw : |(314202689/2500000000 : ℝ)|=(314202689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1517641781/2000000000 : ℝ)*x 0 + (963101453/2500000000 : ℝ)*x 1 + (-16811/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1517641781/2000000000 : ℝ)^37 ≤ (17579813388383/25000000000000 : ℝ)^29 := by
    have hnat : (1517641781 : ℕ)^37*25000000000000^29 ≤ 17579813388383^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517641781 2000000000 17579813388383 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963101453/2500000000 : ℝ)^37 ≤ (29610872883399/100000000000000 : ℝ)^29 := by
    have hnat : (963101453 : ℕ)^37*100000000000000^29 ≤ 29610872883399^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963101453 2500000000 29610872883399 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16811/5000000 : ℝ)^37 ≤ (69873548179/100000000000000 : ℝ)^29 := by
    have hnat : (16811 : ℕ)^37*100000000000000^29 ≤ 69873548179^29*5000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16811 5000000 69873548179 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1517641781/2000000000 : ℝ), (963101453/2500000000 : ℝ), (-16811/5000000 : ℝ)] ![(17579813388383/25000000000000 : ℝ), (29610872883399/100000000000000 : ℝ), (69873548179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1517641781/2000000000 : ℝ)|^37 ≤ (17579813388383/25000000000000 : ℝ)^29
        have hw : |(1517641781/2000000000 : ℝ)|=(1517641781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963101453/2500000000 : ℝ)|^37 ≤ (29610872883399/100000000000000 : ℝ)^29
        have hw : |(963101453/2500000000 : ℝ)|=(963101453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16811/5000000 : ℝ)|^37 ≤ (69873548179/100000000000000 : ℝ)^29
        have hw : |(-16811/5000000 : ℝ)|=(16811/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2005121/125000000 : ℝ)*x 0 + (6157073517/10000000000 : ℝ)*x 1 + (-270314657/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005121/125000000 : ℝ)^37 ≤ (513005197113/100000000000000 : ℝ)^29 := by
    have hnat : (2005121 : ℕ)^37*100000000000000^29 ≤ 513005197113^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005121 125000000 513005197113 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6157073517/10000000000 : ℝ)^37 ≤ (26930270332159/50000000000000 : ℝ)^29 := by
    have hnat : (6157073517 : ℕ)^37*50000000000000^29 ≤ 26930270332159^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6157073517 10000000000 26930270332159 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270314657/500000000 : ℝ)^37 ≤ (22813227058953/50000000000000 : ℝ)^29 := by
    have hnat : (270314657 : ℕ)^37*50000000000000^29 ≤ 22813227058953^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270314657 500000000 22813227058953 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2005121/125000000 : ℝ), (6157073517/10000000000 : ℝ), (-270314657/500000000 : ℝ)] ![(513005197113/100000000000000 : ℝ), (26930270332159/50000000000000 : ℝ), (22813227058953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2005121/125000000 : ℝ)|^37 ≤ (513005197113/100000000000000 : ℝ)^29
        have hw : |(-2005121/125000000 : ℝ)|=(2005121/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6157073517/10000000000 : ℝ)|^37 ≤ (26930270332159/50000000000000 : ℝ)^29
        have hw : |(6157073517/10000000000 : ℝ)|=(6157073517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270314657/500000000 : ℝ)|^37 ≤ (22813227058953/50000000000000 : ℝ)^29
        have hw : |(-270314657/500000000 : ℝ)|=(270314657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6610537969/10000000000 : ℝ)*x 0 + (-296889111/5000000000 : ℝ)*x 1 + (-1178382391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6610537969/10000000000 : ℝ)^37 ≤ (11794429873569/20000000000000 : ℝ)^29 := by
    have hnat : (6610537969 : ℕ)^37*20000000000000^29 ≤ 11794429873569^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6610537969 10000000000 11794429873569 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296889111/5000000000 : ℝ)^37 ≤ (2724668791449/100000000000000 : ℝ)^29 := by
    have hnat : (296889111 : ℕ)^37*100000000000000^29 ≤ 2724668791449^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296889111 5000000000 2724668791449 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1178382391/2500000000 : ℝ)^37 ≤ (38303181822277/100000000000000 : ℝ)^29 := by
    have hnat : (1178382391 : ℕ)^37*100000000000000^29 ≤ 38303181822277^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178382391 2500000000 38303181822277 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6610537969/10000000000 : ℝ), (-296889111/5000000000 : ℝ), (-1178382391/2500000000 : ℝ)] ![(11794429873569/20000000000000 : ℝ), (2724668791449/100000000000000 : ℝ), (38303181822277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6610537969/10000000000 : ℝ)|^37 ≤ (11794429873569/20000000000000 : ℝ)^29
        have hw : |(6610537969/10000000000 : ℝ)|=(6610537969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296889111/5000000000 : ℝ)|^37 ≤ (2724668791449/100000000000000 : ℝ)^29
        have hw : |(-296889111/5000000000 : ℝ)|=(296889111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1178382391/2500000000 : ℝ)|^37 ≤ (38303181822277/100000000000000 : ℝ)^29
        have hw : |(-1178382391/2500000000 : ℝ)|=(1178382391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (155814997/400000000 : ℝ)*x 0 + (6492324581/10000000000 : ℝ)*x 1 + (121223733/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155814997/400000000 : ℝ)^37 ≤ (6006580929533/20000000000000 : ℝ)^29 := by
    have hnat : (155814997 : ℕ)^37*20000000000000^29 ≤ 6006580929533^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155814997 400000000 6006580929533 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6492324581/10000000000 : ℝ)^37 ≤ (57629992324227/100000000000000 : ℝ)^29 := by
    have hnat : (6492324581 : ℕ)^37*100000000000000^29 ≤ 57629992324227^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6492324581 10000000000 57629992324227 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121223733/625000000 : ℝ)^37 ≤ (2467420603371/20000000000000 : ℝ)^29 := by
    have hnat : (121223733 : ℕ)^37*20000000000000^29 ≤ 2467420603371^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121223733 625000000 2467420603371 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(155814997/400000000 : ℝ), (6492324581/10000000000 : ℝ), (121223733/625000000 : ℝ)] ![(6006580929533/20000000000000 : ℝ), (57629992324227/100000000000000 : ℝ), (2467420603371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(155814997/400000000 : ℝ)|^37 ≤ (6006580929533/20000000000000 : ℝ)^29
        have hw : |(155814997/400000000 : ℝ)|=(155814997/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6492324581/10000000000 : ℝ)|^37 ≤ (57629992324227/100000000000000 : ℝ)^29
        have hw : |(6492324581/10000000000 : ℝ)|=(6492324581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(121223733/625000000 : ℝ)|^37 ≤ (2467420603371/20000000000000 : ℝ)^29
        have hw : |(121223733/625000000 : ℝ)|=(121223733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8029906231/10000000000 : ℝ)*x 0 + (810738221/2500000000 : ℝ)*x 1 + (-48110829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8029906231/10000000000 : ℝ)^37 ≤ (37791463652909/50000000000000 : ℝ)^29 := by
    have hnat : (8029906231 : ℕ)^37*50000000000000^29 ≤ 37791463652909^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8029906231 10000000000 37791463652909 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (810738221/2500000000 : ℝ)^37 ≤ (23769919546769/100000000000000 : ℝ)^29 := by
    have hnat : (810738221 : ℕ)^37*100000000000000^29 ≤ 23769919546769^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810738221 2500000000 23769919546769 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48110829/2500000000 : ℝ)^37 ≤ (647153137531/100000000000000 : ℝ)^29 := by
    have hnat : (48110829 : ℕ)^37*100000000000000^29 ≤ 647153137531^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48110829 2500000000 647153137531 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8029906231/10000000000 : ℝ), (810738221/2500000000 : ℝ), (-48110829/2500000000 : ℝ)] ![(37791463652909/50000000000000 : ℝ), (23769919546769/100000000000000 : ℝ), (647153137531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8029906231/10000000000 : ℝ)|^37 ≤ (37791463652909/50000000000000 : ℝ)^29
        have hw : |(8029906231/10000000000 : ℝ)|=(8029906231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(810738221/2500000000 : ℝ)|^37 ≤ (23769919546769/100000000000000 : ℝ)^29
        have hw : |(810738221/2500000000 : ℝ)|=(810738221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48110829/2500000000 : ℝ)|^37 ≤ (647153137531/100000000000000 : ℝ)^29
        have hw : |(-48110829/2500000000 : ℝ)|=(48110829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313062_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((83423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(83423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41331/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(41331/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2252/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2252/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2509/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2509/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62841/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62841/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47623/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (83423/100000 : ℝ) ^ (73/16 : ℝ) ≤ (43738761238789703903/100000000000000000000 : ℝ) := by
    have hpowers : (83423/100000 : ℝ)^73 ≤ (43738761238789703903/100000000000000000000 : ℝ)^16 := by
      have hnat : (83423 : ℕ)^73*100000000000000000000^16 ≤ 43738761238789703903^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83423 100000 43738761238789703903 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83423/100000 : ℝ)) (X := (43738761238789703903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (143738761238789703903/100000000000000000000 : ℝ) ≤ (135346415270841/125000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (143738761238789703903/100000000000000000000 : ℝ)^16 ≤ (135346415270841/125000000000000 : ℝ)^73 := by
      have hnat : (143738761238789703903 : ℕ)^16*125000000000000^73 ≤ 135346415270841^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143738761238789703903 100000000000000000000 135346415270841 125000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (135346415270841/125000000000000 : ℝ)) (X := (143738761238789703903/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (93738761238789703903/50000000000000000000 : ℝ) ≤ (2295379396690177/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (93738761238789703903/50000000000000000000 : ℝ)^16 ≤ (2295379396690177/2000000000000000 : ℝ)^73 := by
      have hnat : (93738761238789703903 : ℕ)^16*2000000000000000^73 ≤ 2295379396690177^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93738761238789703903 50000000000000000000 2295379396690177 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2295379396690177/2000000000000000 : ℝ)) (X := (93738761238789703903/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10346415270841/104278750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(129836752356721/1668460000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (83423/100000 : ℝ)) (alpha := (10346415270841/104278750000000 : ℝ)) (beta := (129836752356721/1668460000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (83423/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10346415270841/104278750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(129836752356721/1668460000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (41331/50000 : ℝ) ^ (73/16 : ℝ) ≤ (20973852679576589899/50000000000000000000 : ℝ) := by
    have hpowers : (41331/50000 : ℝ)^73 ≤ (20973852679576589899/50000000000000000000 : ℝ)^16 := by
      have hnat : (41331 : ℕ)^73*50000000000000000000^16 ≤ 20973852679576589899^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41331 50000 20973852679576589899 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41331/50000 : ℝ)) (X := (20973852679576589899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (70973852679576589899/50000000000000000000 : ℝ) ≤ (2159599416437747/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (70973852679576589899/50000000000000000000 : ℝ)^16 ≤ (2159599416437747/2000000000000000 : ℝ)^73 := by
      have hnat : (70973852679576589899 : ℕ)^16*2000000000000000^73 ≤ 2159599416437747^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70973852679576589899 50000000000000000000 2159599416437747 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2159599416437747/2000000000000000 : ℝ)) (X := (70973852679576589899/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (45973852679576589899/25000000000000000000 : ℝ) ≤ (11428471261246249/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (45973852679576589899/25000000000000000000 : ℝ)^16 ≤ (11428471261246249/10000000000000000 : ℝ)^73 := by
      have hnat : (45973852679576589899 : ℕ)^16*10000000000000000^73 ≤ 11428471261246249^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45973852679576589899 25000000000000000000 11428471261246249 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11428471261246249/10000000000000000 : ℝ)) (X := (45973852679576589899/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(53199805479249/551080000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(105079029842919/1377700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (41331/50000 : ℝ)) (alpha := (53199805479249/551080000000000 : ℝ)) (beta := (105079029842919/1377700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (41331/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(53199805479249/551080000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(105079029842919/1377700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2252/3125 : ℝ) ^ (73/16 : ℝ) ≤ (2803819494748647943/12500000000000000000 : ℝ) := by
    have hpowers : (2252/3125 : ℝ)^73 ≤ (2803819494748647943/12500000000000000000 : ℝ)^16 := by
      have hnat : (2252 : ℕ)^73*12500000000000000000^16 ≤ 2803819494748647943^16*3125^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2252 3125 2803819494748647943 12500000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2252/3125 : ℝ)) (X := (2803819494748647943/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (15303819494748647943/12500000000000000000 : ℝ) ≤ (5226771650760619/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (15303819494748647943/12500000000000000000 : ℝ)^16 ≤ (5226771650760619/5000000000000000 : ℝ)^73 := by
      have hnat : (15303819494748647943 : ℕ)^16*5000000000000000^73 ≤ 5226771650760619^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15303819494748647943 12500000000000000000 5226771650760619 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5226771650760619/5000000000000000 : ℝ)) (X := (15303819494748647943/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (9053819494748647943/6250000000000000000 : ℝ) ≤ (1355773444105389/1250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (9053819494748647943/6250000000000000000 : ℝ)^16 ≤ (1355773444105389/1250000000000000 : ℝ)^73 := by
      have hnat : (9053819494748647943 : ℕ)^16*1250000000000000^73 ≤ 1355773444105389^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9053819494748647943 6250000000000000000 1355773444105389 1250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1355773444105389/1250000000000000 : ℝ)) (X := (9053819494748647943/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(226771650760619/3603200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(196322125660937/3603200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (2252/3125 : ℝ)) (alpha := (226771650760619/3603200000000000 : ℝ)) (beta := (196322125660937/3603200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2252/3125 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(226771650760619/3603200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(196322125660937/3603200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1204391301/10000000000 : ℝ)*X 0 0+(5039625581/10000000000 : ℝ)*X 0 1+(-743826299/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5075101533/10000000000 : ℝ)*X 1 0+(-610614971/5000000000 : ℝ)*X 1 1+(-2952893189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5308645809/10000000000 : ℝ)*X 2 0+(5350543239/10000000000 : ℝ)*X 2 1+(1695953193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-356386459/2500000000 : ℝ)*X 0 0+(3310598209/10000000000 : ℝ)*X 0 1+(-7328785437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1906205191/5000000000 : ℝ)*X 1 0+(-149605471/2000000000 : ℝ)*X 1 1+(-91456003/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((777297869/2000000000 : ℝ)*X 2 0+(6966182471/10000000000 : ℝ)*X 2 1+(622312053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4274973741/10000000000 : ℝ)*X 0 0+(7231429349/10000000000 : ℝ)*X 0 1+(-1401549/500000000 : ℝ)*X 0 2+(4274973741/10000000000 : ℝ)*X 1 0+(7231429349/10000000000 : ℝ)*X 1 1+(-1401549/500000000 : ℝ)*X 1 2+(4274973741/10000000000 : ℝ)*X 2 0+(7231429349/10000000000 : ℝ)*X 2 1+(-1401549/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-368415109/5000000000 : ℝ)*X 0 0+(75061663/200000000 : ℝ)*X 0 1+(-7371835281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3268631103/10000000000 : ℝ)*X 1 0+(-715098981/5000000000 : ℝ)*X 1 1+(-1471890297/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6764983171/10000000000 : ℝ)*X 2 0+(256950099/625000000 : ℝ)*X 2 1+(314202689/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1517641781/2000000000 : ℝ)*X 0 0+(963101453/2500000000 : ℝ)*X 0 1+(-16811/5000000 : ℝ)*X 0 2+(1517641781/2000000000 : ℝ)*X 1 0+(963101453/2500000000 : ℝ)*X 1 1+(-16811/5000000 : ℝ)*X 1 2+(1517641781/2000000000 : ℝ)*X 2 0+(963101453/2500000000 : ℝ)*X 2 1+(-16811/5000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2005121/125000000 : ℝ)*X 0 0+(6157073517/10000000000 : ℝ)*X 0 1+(-270314657/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6610537969/10000000000 : ℝ)*X 1 0+(-296889111/5000000000 : ℝ)*X 1 1+(-1178382391/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((155814997/400000000 : ℝ)*X 2 0+(6492324581/10000000000 : ℝ)*X 2 1+(121223733/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8029906231/10000000000 : ℝ)*X 0 0+(810738221/2500000000 : ℝ)*X 0 1+(-48110829/2500000000 : ℝ)*X 0 2+(8029906231/10000000000 : ℝ)*X 1 0+(810738221/2500000000 : ℝ)*X 1 1+(-48110829/2500000000 : ℝ)*X 1 2+(8029906231/10000000000 : ℝ)*X 2 0+(810738221/2500000000 : ℝ)*X 2 1+(-48110829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((2509/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2509/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (109173719183222076509378031/6205160800000000000000000000000 : ℝ) := by norm_num
    linear_combination (132662473657/200000000000 : ℝ)*(base7) + (15459/62500000000 : ℝ)*(base39) + (7774102691/125000000000 : ℝ)*(base60) + (640135794481/250000000000 : ℝ)*(major_s1_0) + (640135794481/250000000000 : ℝ)*(major_s1_1) + (640135794481/250000000000 : ℝ)*(major_s1_2) + (13914091/1000000000000 : ℝ)*(sp_s1_0) + (2793677/1000000000000 : ℝ)*(sp_s1_1) + (3218900896777/1000000000000 : ℝ)*(sp_s1_7) + (1609508607699/500000000000 : ℝ)*(sp_s1_8) + (3219025079707/1000000000000 : ℝ)*(sp_s1_9) + (1087036590287/500000000000 : ℝ)*(sp_s1_13) + (55134419/500000000000 : ℝ)*(sp_s1_14) + (633829/125000000000 : ℝ)*(sp_s1_22) + (1510760812289/1000000000000 : ℝ)*(f.failure) + (3219025079707/1000000000000 : ℝ)*(f.sum) + (820460178911069803/12410321600000000000000000000000 : ℝ)*base63 + (224240441365497/900800000000000000000000000 : ℝ)*base65 + (658925416144107/688850000000000000000000000 : ℝ)*base66 + (426476876424219/900800000000000000000000000 : ℝ)*base69 + (25102581288300088729/75147438400000000000000000000000 : ℝ)*base70 + (9597015061967/104278750000000000000000000 : ℝ)*base72 + (1393563672581/8610625000000000000000000 : ℝ)*base75 + (130602597081043/834230000000000000000000000 : ℝ)*base77 + (3796531236760247477/28732966775000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (25743/100000000000000000 : ℝ)*base87 + (25743/100000000000000000 : ℝ)*base89 + (25743/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62841/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62841/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9022196065759857045149483941563/517653129418400000000000000000000000 : ℝ) := by norm_num
    linear_combination (2113880057/3125000000 : ℝ)*(base7) + (2480585747179/1000000000000 : ℝ)*(major_s1_0) + (2480585747179/1000000000000 : ℝ)*(major_s1_1) + (2480585747179/1000000000000 : ℝ)*(major_s1_2) + (376873/40000000000 : ℝ)*(sp_s1_0) + (7999119/1000000000000 : ℝ)*(sp_s1_1) + (10881427/1000000000000 : ℝ)*(sp_s1_2) + (1464839/250000000000 : ℝ)*(sp_s1_7) + (10155567/100000000000 : ℝ)*(sp_s1_8) + (3098526059931/1000000000000 : ℝ)*(sp_s1_14) + (3098431786323/1000000000000 : ℝ)*(sp_s1_15) + (619706091937/200000000000 : ℝ)*(sp_s1_16) + (1069992055521/500000000000 : ℝ)*(sp_s1_20) + (8435149/200000000000 : ℝ)*(sp_s1_27) + (731792334273/500000000000 : ℝ)*(f.failure) + (387317667639/125000000000 : ℝ)*(f.sum) + (18003161284662677783/49641286400000000000000000000000 : ℝ)*base62 + (290325939973437/3603200000000000000000000000 : ℝ)*base64 + (345798250731189/1377700000000000000000000000 : ℝ)*base66 + (772940560253319/3603200000000000000000000000 : ℝ)*base68 + (52972255833088480931/300589753600000000000000000000000 : ℝ)*base70 + (335297990402919/1668460000000000000000000000 : ℝ)*base72 + (79843101418193/551080000000000000000000000 : ℝ)*base74 + (24716533010359/834230000000000000000000000 : ℝ)*base76 + (595150248766457991/14366483387500000000000000000000 : ℝ)*base79 + (22049/50000000000000000 : ℝ)*base86 + (22049/50000000000000000 : ℝ)*base88 + (22049/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47623/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10332663256158082517837605269633/1035306258836800000000000000000000000 : ℝ) := by norm_num
    linear_combination (323978643733/1000000000000 : ℝ)*(base7) + (1514997/125000000000 : ℝ)*(base11) + (11478907541/50000000000 : ℝ)*(base39) + (2959/15625000000 : ℝ)*(base59) + (2525950604539/1000000000000 : ℝ)*(major_s1_0) + (2525950604539/1000000000000 : ℝ)*(major_s1_1) + (2525950604539/1000000000000 : ℝ)*(major_s1_2) + (11415981/500000000000 : ℝ)*(sp_s1_0) + (9819063/1000000000000 : ℝ)*(sp_s1_2) + (17103119/250000000000 : ℝ)*(sp_s1_9) + (674078807921/200000000000 : ℝ)*(sp_s1_21) + (3370428991543/1000000000000 : ℝ)*(sp_s1_22) + (842587690001/250000000000 : ℝ)*(sp_s1_23) + (1814329292773/1000000000000 : ℝ)*(sp_s1_27) + (18629383113/12500000000 : ℝ)*(f.failure) + (3370428991543/1000000000000 : ℝ)*(f.sum) + (19035330259670518297/49641286400000000000000000000000 : ℝ)*base63 + (1908923596619437/3603200000000000000000000000 : ℝ)*base64 + (22803726108781/1377700000000000000000000000 : ℝ)*base67 + (323213364336041/3603200000000000000000000000 : ℝ)*base69 + (51022560422520001331/300589753600000000000000000000000 : ℝ)*base70 + (413398184011461/1668460000000000000000000000 : ℝ)*base72 + (82685708268611/551080000000000000000000000 : ℝ)*base75 + (9140407505423/166846000000000000000000000 : ℝ)*base76 + (7249123033212110479/14366483387500000000000000000000 : ℝ)*base78 + (719/1250000000000000 : ℝ)*base86 + (719/1250000000000000 : ℝ)*base88 + (719/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((83423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(83423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41331/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(41331/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2252/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2252/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2509/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2509/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62841/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62841/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47623/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313062_s1 p hpa hpb X hX hprev0

#print axioms solution

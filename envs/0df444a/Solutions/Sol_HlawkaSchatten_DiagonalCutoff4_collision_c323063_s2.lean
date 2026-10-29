-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c323063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:53:31.661546+00:00
-- url     : https://prove2.me/submissions/a4b316eb-5826-42ca-98e2-a05ce62baf65

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
theorem collision_support_c323063_s2_s2_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1325044161/10000000000 : ℝ)*x 0 + (5317698207/10000000000 : ℝ)*x 1 + (1331685531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325044161/10000000000 : ℝ)^21 ≤ (164712406969/2000000000000 : ℝ)^17 := by
    have hnat : (1325044161 : ℕ)^21*2000000000000^17 ≤ 164712406969^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325044161 10000000000 164712406969 2000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5317698207/10000000000 : ℝ)^21 ≤ (45834034062173/100000000000000 : ℝ)^17 := by
    have hnat : (5317698207 : ℕ)^21*100000000000000^17 ≤ 45834034062173^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5317698207 10000000000 45834034062173 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1331685531/2500000000 : ℝ)^21 ≤ (22965172785597/50000000000000 : ℝ)^17 := by
    have hnat : (1331685531 : ℕ)^21*50000000000000^17 ≤ 22965172785597^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331685531 2500000000 22965172785597 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1325044161/10000000000 : ℝ), (5317698207/10000000000 : ℝ), (1331685531/2500000000 : ℝ)] ![(164712406969/2000000000000 : ℝ), (45834034062173/100000000000000 : ℝ), (22965172785597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1325044161/10000000000 : ℝ)|^21 ≤ (164712406969/2000000000000 : ℝ)^17
        have hw : |(-1325044161/10000000000 : ℝ)|=(1325044161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5317698207/10000000000 : ℝ)|^21 ≤ (45834034062173/100000000000000 : ℝ)^17
        have hw : |(5317698207/10000000000 : ℝ)|=(5317698207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1331685531/2500000000 : ℝ)|^21 ≤ (22965172785597/50000000000000 : ℝ)^17
        have hw : |(1331685531/2500000000 : ℝ)|=(1331685531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5318110011/10000000000 : ℝ)*x 0 + (-1328254291/10000000000 : ℝ)*x 1 + (2662007863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5318110011/10000000000 : ℝ)^21 ≤ (22919209327593/50000000000000 : ℝ)^17 := by
    have hnat : (5318110011 : ℕ)^21*50000000000000^17 ≤ 22919209327593^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5318110011 10000000000 22919209327593 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328254291/10000000000 : ℝ)^21 ≤ (8260274079111/100000000000000 : ℝ)^17 := by
    have hnat : (1328254291 : ℕ)^21*100000000000000^17 ≤ 8260274079111^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328254291 10000000000 8260274079111 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2662007863/5000000000 : ℝ)^21 ≤ (5737663406181/12500000000000 : ℝ)^17 := by
    have hnat : (2662007863 : ℕ)^21*12500000000000^17 ≤ 5737663406181^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2662007863 5000000000 5737663406181 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5318110011/10000000000 : ℝ), (-1328254291/10000000000 : ℝ), (2662007863/5000000000 : ℝ)] ![(22919209327593/50000000000000 : ℝ), (8260274079111/100000000000000 : ℝ), (5737663406181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5318110011/10000000000 : ℝ)|^21 ≤ (22919209327593/50000000000000 : ℝ)^17
        have hw : |(5318110011/10000000000 : ℝ)|=(5318110011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1328254291/10000000000 : ℝ)|^21 ≤ (8260274079111/100000000000000 : ℝ)^17
        have hw : |(-1328254291/10000000000 : ℝ)|=(1328254291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2662007863/5000000000 : ℝ)|^21 ≤ (5737663406181/12500000000000 : ℝ)^17
        have hw : |(2662007863/5000000000 : ℝ)|=(2662007863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5325318091/10000000000 : ℝ)*x 0 + (5322998539/10000000000 : ℝ)*x 1 + (-263933199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325318091/10000000000 : ℝ)^21 ≤ (45915178043129/100000000000000 : ℝ)^17 := by
    have hnat : (5325318091 : ℕ)^21*100000000000000^17 ≤ 45915178043129^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325318091 10000000000 45915178043129 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5322998539/10000000000 : ℝ)^21 ≤ (22945237144759/50000000000000 : ℝ)^17 := by
    have hnat : (5322998539 : ℕ)^21*50000000000000^17 ≤ 22945237144759^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322998539 10000000000 22945237144759 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263933199/2000000000 : ℝ)^21 ≤ (1024293455877/12500000000000 : ℝ)^17 := by
    have hnat : (263933199 : ℕ)^21*12500000000000^17 ≤ 1024293455877^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263933199 2000000000 1024293455877 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325318091/10000000000 : ℝ), (5322998539/10000000000 : ℝ), (-263933199/2000000000 : ℝ)] ![(45915178043129/100000000000000 : ℝ), (22945237144759/50000000000000 : ℝ), (1024293455877/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325318091/10000000000 : ℝ)|^21 ≤ (45915178043129/100000000000000 : ℝ)^17
        have hw : |(5325318091/10000000000 : ℝ)|=(5325318091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5322998539/10000000000 : ℝ)|^21 ≤ (22945237144759/50000000000000 : ℝ)^17
        have hw : |(5322998539/10000000000 : ℝ)|=(5322998539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263933199/2000000000 : ℝ)|^21 ≤ (1024293455877/12500000000000 : ℝ)^17
        have hw : |(-263933199/2000000000 : ℝ)|=(263933199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4111586143/10000000000 : ℝ)*x 0 + (4110185139/10000000000 : ℝ)*x 1 + (2052938301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111586143/10000000000 : ℝ)^21 ≤ (33357083692501/100000000000000 : ℝ)^17 := by
    have hnat : (4111586143 : ℕ)^21*100000000000000^17 ≤ 33357083692501^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111586143 10000000000 33357083692501 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110185139/10000000000 : ℝ)^21 ≤ (16671521783049/50000000000000 : ℝ)^17 := by
    have hnat : (4110185139 : ℕ)^21*50000000000000^17 ≤ 16671521783049^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110185139 10000000000 16671521783049 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052938301/5000000000 : ℝ)^21 ≤ (3329987272813/10000000000000 : ℝ)^17 := by
    have hnat : (2052938301 : ℕ)^21*10000000000000^17 ≤ 3329987272813^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052938301 5000000000 3329987272813 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111586143/10000000000 : ℝ), (4110185139/10000000000 : ℝ), (2052938301/5000000000 : ℝ)] ![(33357083692501/100000000000000 : ℝ), (16671521783049/50000000000000 : ℝ), (3329987272813/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111586143/10000000000 : ℝ)|^21 ≤ (33357083692501/100000000000000 : ℝ)^17
        have hw : |(4111586143/10000000000 : ℝ)|=(4111586143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110185139/10000000000 : ℝ)|^21 ≤ (16671521783049/50000000000000 : ℝ)^17
        have hw : |(4110185139/10000000000 : ℝ)|=(4110185139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2052938301/5000000000 : ℝ)|^21 ≤ (3329987272813/10000000000000 : ℝ)^17
        have hw : |(2052938301/5000000000 : ℝ)|=(2052938301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-158424789/1250000000 : ℝ)*x 0 + (4761423327/10000000000 : ℝ)*x 1 + (2954894583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158424789/1250000000 : ℝ)^21 ≤ (7795318415389/100000000000000 : ℝ)^17 := by
    have hnat : (158424789 : ℕ)^21*100000000000000^17 ≤ 7795318415389^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158424789 1250000000 7795318415389 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4761423327/10000000000 : ℝ)^21 ≤ (39986202303267/100000000000000 : ℝ)^17 := by
    have hnat : (4761423327 : ℕ)^21*100000000000000^17 ≤ 39986202303267^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4761423327 10000000000 39986202303267 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2954894583/5000000000 : ℝ)^21 ≤ (26109239631637/50000000000000 : ℝ)^17 := by
    have hnat : (2954894583 : ℕ)^21*50000000000000^17 ≤ 26109239631637^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2954894583 5000000000 26109239631637 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158424789/1250000000 : ℝ), (4761423327/10000000000 : ℝ), (2954894583/5000000000 : ℝ)] ![(7795318415389/100000000000000 : ℝ), (39986202303267/100000000000000 : ℝ), (26109239631637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158424789/1250000000 : ℝ)|^21 ≤ (7795318415389/100000000000000 : ℝ)^17
        have hw : |(-158424789/1250000000 : ℝ)|=(158424789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4761423327/10000000000 : ℝ)|^21 ≤ (39986202303267/100000000000000 : ℝ)^17
        have hw : |(4761423327/10000000000 : ℝ)|=(4761423327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2954894583/5000000000 : ℝ)|^21 ≤ (26109239631637/50000000000000 : ℝ)^17
        have hw : |(2954894583/5000000000 : ℝ)|=(2954894583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1020110893/2000000000 : ℝ)*x 0 + (-779766161/10000000000 : ℝ)*x 1 + (5907053287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020110893/2000000000 : ℝ)^21 ≤ (10883322278033/25000000000000 : ℝ)^17 := by
    have hnat : (1020110893 : ℕ)^21*25000000000000^17 ≤ 10883322278033^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020110893 2000000000 10883322278033 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779766161/10000000000 : ℝ)^21 ≤ (855618404313/20000000000000 : ℝ)^17 := by
    have hnat : (779766161 : ℕ)^21*20000000000000^17 ≤ 855618404313^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779766161 10000000000 855618404313 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5907053287/10000000000 : ℝ)^21 ≤ (5218861884857/10000000000000 : ℝ)^17 := by
    have hnat : (5907053287 : ℕ)^21*10000000000000^17 ≤ 5218861884857^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5907053287 10000000000 5218861884857 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020110893/2000000000 : ℝ), (-779766161/10000000000 : ℝ), (5907053287/10000000000 : ℝ)] ![(10883322278033/25000000000000 : ℝ), (855618404313/20000000000000 : ℝ), (5218861884857/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020110893/2000000000 : ℝ)|^21 ≤ (10883322278033/25000000000000 : ℝ)^17
        have hw : |(1020110893/2000000000 : ℝ)|=(1020110893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-779766161/10000000000 : ℝ)|^21 ≤ (855618404313/20000000000000 : ℝ)^17
        have hw : |(-779766161/10000000000 : ℝ)|=(779766161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5907053287/10000000000 : ℝ)|^21 ≤ (5218861884857/10000000000000 : ℝ)^17
        have hw : |(5907053287/10000000000 : ℝ)|=(5907053287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4926175417/10000000000 : ℝ)*x 0 + (6082657081/10000000000 : ℝ)*x 1 + (-191537409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4926175417/10000000000 : ℝ)^21 ≤ (5212778452661/12500000000000 : ℝ)^17 := by
    have hnat : (4926175417 : ℕ)^21*12500000000000^17 ≤ 5212778452661^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4926175417 10000000000 5212778452661 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6082657081/10000000000 : ℝ)^21 ≤ (13527943263243/25000000000000 : ℝ)^17 := by
    have hnat : (6082657081 : ℕ)^21*25000000000000^17 ≤ 13527943263243^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6082657081 10000000000 13527943263243 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191537409/2500000000 : ℝ)^21 ≤ (1046499827527/25000000000000 : ℝ)^17 := by
    have hnat : (191537409 : ℕ)^21*25000000000000^17 ≤ 1046499827527^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191537409 2500000000 1046499827527 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4926175417/10000000000 : ℝ), (6082657081/10000000000 : ℝ), (-191537409/2500000000 : ℝ)] ![(5212778452661/12500000000000 : ℝ), (13527943263243/25000000000000 : ℝ), (1046499827527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4926175417/10000000000 : ℝ)|^21 ≤ (5212778452661/12500000000000 : ℝ)^17
        have hw : |(4926175417/10000000000 : ℝ)|=(4926175417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6082657081/10000000000 : ℝ)|^21 ≤ (13527943263243/25000000000000 : ℝ)^17
        have hw : |(6082657081/10000000000 : ℝ)|=(6082657081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191537409/2500000000 : ℝ)|^21 ≤ (1046499827527/25000000000000 : ℝ)^17
        have hw : |(-191537409/2500000000 : ℝ)|=(191537409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4455544477/10000000000 : ℝ)*x 0 + (42162019/80000000 : ℝ)*x 1 + (1238288583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4455544477/10000000000 : ℝ)^21 ≤ (4604677470633/12500000000000 : ℝ)^17 := by
    have hnat : (4455544477 : ℕ)^21*12500000000000^17 ≤ 4604677470633^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455544477 10000000000 4604677470633 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42162019/80000000 : ℝ)^21 ≤ (5666175127049/12500000000000 : ℝ)^17 := by
    have hnat : (42162019 : ℕ)^21*12500000000000^17 ≤ 5666175127049^17*80000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42162019 80000000 5666175127049 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1238288583/5000000000 : ℝ)^21 ≤ (8916589600233/50000000000000 : ℝ)^17 := by
    have hnat : (1238288583 : ℕ)^21*50000000000000^17 ≤ 8916589600233^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238288583 5000000000 8916589600233 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4455544477/10000000000 : ℝ), (42162019/80000000 : ℝ), (1238288583/5000000000 : ℝ)] ![(4604677470633/12500000000000 : ℝ), (5666175127049/12500000000000 : ℝ), (8916589600233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4455544477/10000000000 : ℝ)|^21 ≤ (4604677470633/12500000000000 : ℝ)^17
        have hw : |(4455544477/10000000000 : ℝ)|=(4455544477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42162019/80000000 : ℝ)|^21 ≤ (5666175127049/12500000000000 : ℝ)^17
        have hw : |(42162019/80000000 : ℝ)|=(42162019/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1238288583/5000000000 : ℝ)|^21 ≤ (8916589600233/50000000000000 : ℝ)^17
        have hw : |(1238288583/5000000000 : ℝ)|=(1238288583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-782067961/10000000000 : ℝ)*x 0 + (1021377961/2000000000 : ℝ)*x 1 + (5899501129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782067961/10000000000 : ℝ)^21 ≤ (858739480543/20000000000000 : ℝ)^17 := by
    have hnat : (782067961 : ℕ)^21*20000000000000^17 ≤ 858739480543^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782067961 10000000000 858739480543 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021377961/2000000000 : ℝ)^21 ≤ (10900023484261/25000000000000 : ℝ)^17 := by
    have hnat : (1021377961 : ℕ)^21*25000000000000^17 ≤ 10900023484261^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021377961 2000000000 10900023484261 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5899501129/10000000000 : ℝ)^21 ≤ (52106208641283/100000000000000 : ℝ)^17 := by
    have hnat : (5899501129 : ℕ)^21*100000000000000^17 ≤ 52106208641283^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5899501129 10000000000 52106208641283 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-782067961/10000000000 : ℝ), (1021377961/2000000000 : ℝ), (5899501129/10000000000 : ℝ)] ![(858739480543/20000000000000 : ℝ), (10900023484261/25000000000000 : ℝ), (52106208641283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-782067961/10000000000 : ℝ)|^21 ≤ (858739480543/20000000000000 : ℝ)^17
        have hw : |(-782067961/10000000000 : ℝ)|=(782067961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1021377961/2000000000 : ℝ)|^21 ≤ (10900023484261/25000000000000 : ℝ)^17
        have hw : |(1021377961/2000000000 : ℝ)|=(1021377961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5899501129/10000000000 : ℝ)|^21 ≤ (52106208641283/100000000000000 : ℝ)^17
        have hw : |(5899501129/10000000000 : ℝ)|=(5899501129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4776733933/10000000000 : ℝ)*x 0 + (-1265193509/10000000000 : ℝ)*x 1 + (737095379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4776733933/10000000000 : ℝ)^21 ≤ (401450936499/1000000000000 : ℝ)^17 := by
    have hnat : (4776733933 : ℕ)^21*1000000000000^17 ≤ 401450936499^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776733933 10000000000 401450936499 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265193509/10000000000 : ℝ)^21 ≤ (3889285033863/50000000000000 : ℝ)^17 := by
    have hnat : (1265193509 : ℕ)^21*50000000000000^17 ≤ 3889285033863^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265193509 10000000000 3889285033863 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737095379/1250000000 : ℝ)^21 ≤ (52076336271877/100000000000000 : ℝ)^17 := by
    have hnat : (737095379 : ℕ)^21*100000000000000^17 ≤ 52076336271877^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737095379 1250000000 52076336271877 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4776733933/10000000000 : ℝ), (-1265193509/10000000000 : ℝ), (737095379/1250000000 : ℝ)] ![(401450936499/1000000000000 : ℝ), (3889285033863/50000000000000 : ℝ), (52076336271877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4776733933/10000000000 : ℝ)|^21 ≤ (401450936499/1000000000000 : ℝ)^17
        have hw : |(4776733933/10000000000 : ℝ)|=(4776733933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1265193509/10000000000 : ℝ)|^21 ≤ (3889285033863/50000000000000 : ℝ)^17
        have hw : |(-1265193509/10000000000 : ℝ)|=(1265193509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(737095379/1250000000 : ℝ)|^21 ≤ (52076336271877/100000000000000 : ℝ)^17
        have hw : |(737095379/1250000000 : ℝ)|=(737095379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5898114381/10000000000 : ℝ)*x 0 + (1022388333/2000000000 : ℝ)*x 1 + (-194109311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5898114381/10000000000 : ℝ)^21 ≤ (6511384868621/12500000000000 : ℝ)^17 := by
    have hnat : (5898114381 : ℕ)^21*12500000000000^17 ≤ 6511384868621^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5898114381 10000000000 6511384868621 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022388333/2000000000 : ℝ)^21 ≤ (43653378713153/100000000000000 : ℝ)^17 := by
    have hnat : (1022388333 : ℕ)^21*100000000000000^17 ≤ 43653378713153^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022388333 2000000000 43653378713153 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194109311/2500000000 : ℝ)^21 ≤ (4255542327147/100000000000000 : ℝ)^17 := by
    have hnat : (194109311 : ℕ)^21*100000000000000^17 ≤ 4255542327147^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194109311 2500000000 4255542327147 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5898114381/10000000000 : ℝ), (1022388333/2000000000 : ℝ), (-194109311/2500000000 : ℝ)] ![(6511384868621/12500000000000 : ℝ), (43653378713153/100000000000000 : ℝ), (4255542327147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5898114381/10000000000 : ℝ)|^21 ≤ (6511384868621/12500000000000 : ℝ)^17
        have hw : |(5898114381/10000000000 : ℝ)|=(5898114381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1022388333/2000000000 : ℝ)|^21 ≤ (43653378713153/100000000000000 : ℝ)^17
        have hw : |(1022388333/2000000000 : ℝ)|=(1022388333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194109311/2500000000 : ℝ)|^21 ≤ (4255542327147/100000000000000 : ℝ)^17
        have hw : |(-194109311/2500000000 : ℝ)|=(194109311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (71955839/125000000 : ℝ)*x 0 + (488764299/1250000000 : ℝ)*x 1 + (4895599/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71955839/125000000 : ℝ)^21 ≤ (50550115556029/100000000000000 : ℝ)^17 := by
    have hnat : (71955839 : ℕ)^21*100000000000000^17 ≤ 50550115556029^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71955839 125000000 50550115556029 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488764299/1250000000 : ℝ)^21 ≤ (6269949432699/20000000000000 : ℝ)^17 := by
    have hnat : (488764299 : ℕ)^21*20000000000000^17 ≤ 6269949432699^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488764299 1250000000 6269949432699 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4895599/19531250 : ℝ)^21 ≤ (4525034317993/25000000000000 : ℝ)^17 := by
    have hnat : (4895599 : ℕ)^21*25000000000000^17 ≤ 4525034317993^17*19531250^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895599 19531250 4525034317993 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71955839/125000000 : ℝ), (488764299/1250000000 : ℝ), (4895599/19531250 : ℝ)] ![(50550115556029/100000000000000 : ℝ), (6269949432699/20000000000000 : ℝ), (4525034317993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71955839/125000000 : ℝ)|^21 ≤ (50550115556029/100000000000000 : ℝ)^17
        have hw : |(71955839/125000000 : ℝ)|=(71955839/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(488764299/1250000000 : ℝ)|^21 ≤ (6269949432699/20000000000000 : ℝ)^17
        have hw : |(488764299/1250000000 : ℝ)|=(488764299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4895599/19531250 : ℝ)|^21 ≤ (4525034317993/25000000000000 : ℝ)^17
        have hw : |(4895599/19531250 : ℝ)|=(4895599/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-734495889/10000000000 : ℝ)*x 0 + (5657182979/10000000000 : ℝ)*x 1 + (5384963411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (734495889/10000000000 : ℝ)^21 ≤ (3973409617459/100000000000000 : ℝ)^17 := by
    have hnat : (734495889 : ℕ)^21*100000000000000^17 ≤ 3973409617459^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734495889 10000000000 3973409617459 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5657182979/10000000000 : ℝ)^21 ≤ (49475308910037/100000000000000 : ℝ)^17 := by
    have hnat : (5657182979 : ℕ)^21*100000000000000^17 ≤ 49475308910037^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657182979 10000000000 49475308910037 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384963411/10000000000 : ℝ)^21 ≤ (9310256291953/20000000000000 : ℝ)^17 := by
    have hnat : (5384963411 : ℕ)^21*20000000000000^17 ≤ 9310256291953^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384963411 10000000000 9310256291953 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-734495889/10000000000 : ℝ), (5657182979/10000000000 : ℝ), (5384963411/10000000000 : ℝ)] ![(3973409617459/100000000000000 : ℝ), (49475308910037/100000000000000 : ℝ), (9310256291953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-734495889/10000000000 : ℝ)|^21 ≤ (3973409617459/100000000000000 : ℝ)^17
        have hw : |(-734495889/10000000000 : ℝ)|=(734495889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5657182979/10000000000 : ℝ)|^21 ≤ (49475308910037/100000000000000 : ℝ)^17
        have hw : |(5657182979/10000000000 : ℝ)|=(5657182979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384963411/10000000000 : ℝ)|^21 ≤ (9310256291953/20000000000000 : ℝ)^17
        have hw : |(5384963411/10000000000 : ℝ)|=(5384963411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5938174453/10000000000 : ℝ)*x 0 + (-91719903/1250000000 : ℝ)*x 1 + (2548842323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5938174453/10000000000 : ℝ)^21 ≤ (13132119680099/25000000000000 : ℝ)^17 := by
    have hnat : (5938174453 : ℕ)^21*25000000000000^17 ≤ 13132119680099^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938174453 10000000000 13132119680099 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91719903/1250000000 : ℝ)^21 ≤ (1984243686841/50000000000000 : ℝ)^17 := by
    have hnat : (91719903 : ℕ)^21*50000000000000^17 ≤ 1984243686841^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91719903 1250000000 1984243686841 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548842323/5000000000 : ℝ)^21 ≤ (43503033898849/100000000000000 : ℝ)^17 := by
    have hnat : (2548842323 : ℕ)^21*100000000000000^17 ≤ 43503033898849^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548842323 5000000000 43503033898849 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5938174453/10000000000 : ℝ), (-91719903/1250000000 : ℝ), (2548842323/5000000000 : ℝ)] ![(13132119680099/25000000000000 : ℝ), (1984243686841/50000000000000 : ℝ), (43503033898849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5938174453/10000000000 : ℝ)|^21 ≤ (13132119680099/25000000000000 : ℝ)^17
        have hw : |(5938174453/10000000000 : ℝ)|=(5938174453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91719903/1250000000 : ℝ)|^21 ≤ (1984243686841/50000000000000 : ℝ)^17
        have hw : |(-91719903/1250000000 : ℝ)|=(91719903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2548842323/5000000000 : ℝ)|^21 ≤ (43503033898849/100000000000000 : ℝ)^17
        have hw : |(2548842323/5000000000 : ℝ)|=(2548842323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (591221049/1250000000 : ℝ)*x 0 + (5946771973/10000000000 : ℝ)*x 1 + (-157176009/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (591221049/1250000000 : ℝ)^21 ≤ (3965807318439/10000000000000 : ℝ)^17 := by
    have hnat : (591221049 : ℕ)^21*10000000000000^17 ≤ 3965807318439^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591221049 1250000000 3965807318439 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5946771973/10000000000 : ℝ)^21 ≤ (10524488452541/20000000000000 : ℝ)^17 := by
    have hnat : (5946771973 : ℕ)^21*20000000000000^17 ≤ 10524488452541^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946771973 10000000000 10524488452541 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157176009/1250000000 : ℝ)^21 ≤ (3859742266797/50000000000000 : ℝ)^17 := by
    have hnat : (157176009 : ℕ)^21*50000000000000^17 ≤ 3859742266797^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157176009 1250000000 3859742266797 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(591221049/1250000000 : ℝ), (5946771973/10000000000 : ℝ), (-157176009/1250000000 : ℝ)] ![(3965807318439/10000000000000 : ℝ), (10524488452541/20000000000000 : ℝ), (3859742266797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(591221049/1250000000 : ℝ)|^21 ≤ (3965807318439/10000000000000 : ℝ)^17
        have hw : |(591221049/1250000000 : ℝ)|=(591221049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5946771973/10000000000 : ℝ)|^21 ≤ (10524488452541/20000000000000 : ℝ)^17
        have hw : |(5946771973/10000000000 : ℝ)|=(5946771973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157176009/1250000000 : ℝ)|^21 ≤ (3859742266797/50000000000000 : ℝ)^17
        have hw : |(-157176009/1250000000 : ℝ)|=(157176009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s2_s2_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2957573791/5000000000 : ℝ)*x 0 + (398873037/1250000000 : ℝ)*x 1 + (3078694819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2957573791/5000000000 : ℝ)^21 ≤ (52276972458561/100000000000000 : ℝ)^17 := by
    have hnat : (2957573791 : ℕ)^21*100000000000000^17 ≤ 52276972458561^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957573791 5000000000 52276972458561 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398873037/1250000000 : ℝ)^21 ≤ (24389396779413/100000000000000 : ℝ)^17 := by
    have hnat : (398873037 : ℕ)^21*100000000000000^17 ≤ 24389396779413^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398873037 1250000000 24389396779413 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3078694819/10000000000 : ℝ)^21 ≤ (186669046031/800000000000 : ℝ)^17 := by
    have hnat : (3078694819 : ℕ)^21*800000000000^17 ≤ 186669046031^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3078694819 10000000000 186669046031 800000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2957573791/5000000000 : ℝ), (398873037/1250000000 : ℝ), (3078694819/10000000000 : ℝ)] ![(52276972458561/100000000000000 : ℝ), (24389396779413/100000000000000 : ℝ), (186669046031/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2957573791/5000000000 : ℝ)|^21 ≤ (52276972458561/100000000000000 : ℝ)^17
        have hw : |(2957573791/5000000000 : ℝ)|=(2957573791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(398873037/1250000000 : ℝ)|^21 ≤ (24389396779413/100000000000000 : ℝ)^17
        have hw : |(398873037/1250000000 : ℝ)|=(398873037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3078694819/10000000000 : ℝ)|^21 ≤ (186669046031/800000000000 : ℝ)^17
        have hw : |(3078694819/10000000000 : ℝ)|=(3078694819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323063_s2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((5493/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5493/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5581/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5581/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42681/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42681/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27239/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27239/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13081/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13081/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (5493/12500 : ℝ) ^ (83/16 : ℝ) ≤ (702282112394846119/50000000000000000000 : ℝ) := by
    have hpowers : (5493/12500 : ℝ)^83 ≤ (702282112394846119/50000000000000000000 : ℝ)^16 := by
      have hnat : (5493 : ℕ)^83*50000000000000000000^16 ≤ 702282112394846119^16*12500^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5493 12500 702282112394846119 50000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5493/12500 : ℝ)) (X := (702282112394846119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (50702282112394846119/50000000000000000000 : ℝ) ≤ (5013461864401199/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (50702282112394846119/50000000000000000000 : ℝ)^16 ≤ (5013461864401199/5000000000000000 : ℝ)^83 := by
      have hnat : (50702282112394846119 : ℕ)^16*5000000000000000^83 ≤ 5013461864401199^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50702282112394846119 50000000000000000000 5013461864401199 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013461864401199/5000000000000000 : ℝ)) (X := (50702282112394846119/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (25702282112394846119/25000000000000000000 : ℝ) ≤ (10053548086596947/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (25702282112394846119/25000000000000000000 : ℝ)^16 ≤ (10053548086596947/10000000000000000 : ℝ)^83 := by
      have hnat : (25702282112394846119 : ℕ)^16*10000000000000000^83 ≤ 10053548086596947^83*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25702282112394846119 25000000000000000000 10053548086596947 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053548086596947/10000000000000000 : ℝ)) (X := (25702282112394846119/25000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4487288133733/732400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26624357794549/4394400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (5493/12500 : ℝ)) (alpha := (4487288133733/732400000000000 : ℝ)) (beta := (26624357794549/4394400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5493/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4487288133733/732400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26624357794549/4394400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (5581/12500 : ℝ) ^ (83/16 : ℝ) ≤ (381318550079614791/25000000000000000000 : ℝ) := by
    have hpowers : (5581/12500 : ℝ)^83 ≤ (381318550079614791/25000000000000000000 : ℝ)^16 := by
      have hnat : (5581 : ℕ)^83*25000000000000000000^16 ≤ 381318550079614791^16*12500^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5581 12500 381318550079614791 25000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5581/12500 : ℝ)) (X := (381318550079614791/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (25381318550079614791/25000000000000000000 : ℝ) ≤ (10029223510964849/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (25381318550079614791/25000000000000000000 : ℝ)^16 ≤ (10029223510964849/10000000000000000 : ℝ)^83 := by
      have hnat : (25381318550079614791 : ℕ)^16*10000000000000000^83 ≤ 10029223510964849^83*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25381318550079614791 25000000000000000000 10029223510964849 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029223510964849/10000000000000000 : ℝ)) (X := (25381318550079614791/25000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (12881318550079614791/12500000000000000000 : ℝ) ≤ (5029047368176373/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (12881318550079614791/12500000000000000000 : ℝ)^16 ≤ (5029047368176373/5000000000000000 : ℝ)^83 := by
      have hnat : (12881318550079614791 : ℕ)^16*5000000000000000^83 ≤ 5029047368176373^83*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12881318550079614791 12500000000000000000 5029047368176373 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029047368176373/5000000000000000 : ℝ)) (X := (12881318550079614791/12500000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(29223510964849/4464800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(28871225387897/4464800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (5581/12500 : ℝ)) (alpha := (29223510964849/4464800000000000 : ℝ)) (beta := (28871225387897/4464800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5581/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(29223510964849/4464800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(28871225387897/4464800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (42681/100000 : ℝ) ^ (83/16 : ℝ) ≤ (1207374268821716617/100000000000000000000 : ℝ) := by
    have hpowers : (42681/100000 : ℝ)^83 ≤ (1207374268821716617/100000000000000000000 : ℝ)^16 := by
      have hnat : (42681 : ℕ)^83*100000000000000000000^16 ≤ 1207374268821716617^16*100000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42681 100000 1207374268821716617 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42681/100000 : ℝ)) (X := (1207374268821716617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (101207374268821716617/100000000000000000000 : ℝ) ≤ (10023162081991383/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (101207374268821716617/100000000000000000000 : ℝ)^16 ≤ (10023162081991383/10000000000000000 : ℝ)^83 := by
      have hnat : (101207374268821716617 : ℕ)^16*10000000000000000^83 ≤ 10023162081991383^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101207374268821716617 100000000000000000000 10023162081991383 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023162081991383/10000000000000000 : ℝ)) (X := (101207374268821716617/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (51207374268821716617/50000000000000000000 : ℝ) ≤ (2511525544058991/2500000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (51207374268821716617/50000000000000000000 : ℝ)^16 ≤ (2511525544058991/2500000000000000 : ℝ)^83 := by
      have hnat : (51207374268821716617 : ℕ)^16*2500000000000000^83 ≤ 2511525544058991^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51207374268821716617 50000000000000000000 2511525544058991 2500000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511525544058991/2500000000000000 : ℝ)) (X := (51207374268821716617/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(23162081991383/4268100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7646698081527/1422700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (42681/100000 : ℝ)) (alpha := (23162081991383/4268100000000000 : ℝ)) (beta := (7646698081527/1422700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42681/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(23162081991383/4268100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7646698081527/1422700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1325044161/10000000000 : ℝ)*X 0 0+(5317698207/10000000000 : ℝ)*X 0 1+(1331685531/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5318110011/10000000000 : ℝ)*X 1 0+(-1328254291/10000000000 : ℝ)*X 1 1+(2662007863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5325318091/10000000000 : ℝ)*X 2 0+(5322998539/10000000000 : ℝ)*X 2 1+(-263933199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4111586143/10000000000 : ℝ)*X 0 0+(4110185139/10000000000 : ℝ)*X 0 1+(2052938301/5000000000 : ℝ)*X 0 2+(4111586143/10000000000 : ℝ)*X 1 0+(4110185139/10000000000 : ℝ)*X 1 1+(2052938301/5000000000 : ℝ)*X 1 2+(4111586143/10000000000 : ℝ)*X 2 0+(4110185139/10000000000 : ℝ)*X 2 1+(2052938301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-158424789/1250000000 : ℝ)*X 0 0+(4761423327/10000000000 : ℝ)*X 0 1+(2954894583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1020110893/2000000000 : ℝ)*X 1 0+(-779766161/10000000000 : ℝ)*X 1 1+(5907053287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4926175417/10000000000 : ℝ)*X 2 0+(6082657081/10000000000 : ℝ)*X 2 1+(-191537409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4455544477/10000000000 : ℝ)*X 0 0+(42162019/80000000 : ℝ)*X 0 1+(1238288583/5000000000 : ℝ)*X 0 2+(4455544477/10000000000 : ℝ)*X 1 0+(42162019/80000000 : ℝ)*X 1 1+(1238288583/5000000000 : ℝ)*X 1 2+(4455544477/10000000000 : ℝ)*X 2 0+(42162019/80000000 : ℝ)*X 2 1+(1238288583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-782067961/10000000000 : ℝ)*X 0 0+(1021377961/2000000000 : ℝ)*X 0 1+(5899501129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4776733933/10000000000 : ℝ)*X 1 0+(-1265193509/10000000000 : ℝ)*X 1 1+(737095379/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5898114381/10000000000 : ℝ)*X 2 0+(1022388333/2000000000 : ℝ)*X 2 1+(-194109311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((71955839/125000000 : ℝ)*X 0 0+(488764299/1250000000 : ℝ)*X 0 1+(4895599/19531250 : ℝ)*X 0 2+(71955839/125000000 : ℝ)*X 1 0+(488764299/1250000000 : ℝ)*X 1 1+(4895599/19531250 : ℝ)*X 1 2+(71955839/125000000 : ℝ)*X 2 0+(488764299/1250000000 : ℝ)*X 2 1+(4895599/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-734495889/10000000000 : ℝ)*X 0 0+(5657182979/10000000000 : ℝ)*X 0 1+(5384963411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5938174453/10000000000 : ℝ)*X 1 0+(-91719903/1250000000 : ℝ)*X 1 1+(2548842323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((591221049/1250000000 : ℝ)*X 2 0+(5946771973/10000000000 : ℝ)*X 2 1+(-157176009/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2957573791/5000000000 : ℝ)*X 0 0+(398873037/1250000000 : ℝ)*X 0 1+(3078694819/10000000000 : ℝ)*X 0 2+(2957573791/5000000000 : ℝ)*X 1 0+(398873037/1250000000 : ℝ)*X 1 1+(3078694819/10000000000 : ℝ)*X 1 2+(2957573791/5000000000 : ℝ)*X 2 0+(398873037/1250000000 : ℝ)*X 2 1+(3078694819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((5373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (121367936649639637260440027/6352070960000000000000000000000 : ℝ) := by norm_num
    linear_combination (2191159/500000000000 : ℝ)*(base50) + (80180006031/500000000000 : ℝ)*(base60) + (5921484139759/1000000000000 : ℝ)*(major_s2_0) + (5921484139759/1000000000000 : ℝ)*(major_s2_1) + (5921484139759/1000000000000 : ℝ)*(major_s2_2) + (19268049/500000000000 : ℝ)*(sp_s2_0) + (16038927/1000000000000 : ℝ)*(sp_s2_6) + (8816055610791/1000000000000 : ℝ)*(sp_s2_7) + (1763197262529/200000000000 : ℝ)*(sp_s2_8) + (70528198539/8000000000 : ℝ)*(sp_s2_9) + (1513400728443/500000000000 : ℝ)*(sp_s2_13) + (5026787/100000000000 : ℝ)*(sp_s2_14) + (79051057/500000000000 : ℝ)*(sp_s2_15) + (14949673/125000000000 : ℝ)*(sp_s2_23) + (3026817495813/1000000000000 : ℝ)*(f.failure) + (8816144414759/1000000000000 : ℝ)*(f.sum) + (18082406594268166913/190562128800000000000000000000000 : ℝ)*base62 + (62353068083073/1422700000000000000000000000 : ℝ)*base65 + (1117122333963817/4464800000000000000000000000 : ℝ)*base66 + (1840734084214003/4268100000000000000000000000 : ℝ)*base68 + (3491316767883072141/10419854800000000000000000000000 : ℝ)*base71 + (1182794588206229/4394400000000000000000000000 : ℝ)*base72 + (848605136785889/4464800000000000000000000000 : ℝ)*base74 + (151767375306053/732400000000000000000000000 : ℝ)*base76 + (102655090120280173/2452514640000000000000000000000 : ℝ)*base79 + (9779/50000000000000000 : ℝ)*base86 + (9779/50000000000000000 : ℝ)*base88 + (9779/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27239/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27239/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (486349846447847101257594513/35459274170000000000000000000000 : ℝ) := by norm_num
    linear_combination (889043/250000000000 : ℝ)*(base60) + (6030054940873/1000000000000 : ℝ)*(major_s2_0) + (6030054940873/1000000000000 : ℝ)*(major_s2_1) + (6030054940873/1000000000000 : ℝ)*(major_s2_2) + (49809227/1000000000000 : ℝ)*(sp_s2_0) + (55045599/1000000000000 : ℝ)*(sp_s2_1) + (12762799/125000000000 : ℝ)*(sp_s2_2) + (27326183/500000000000 : ℝ)*(sp_s2_7) + (58532221/1000000000000 : ℝ)*(sp_s2_8) + (8977686454587/1000000000000 : ℝ)*(sp_s2_14) + (8977677338361/1000000000000 : ℝ)*(sp_s2_15) + (2244422203447/250000000000 : ℝ)*(sp_s2_16) + (1541111017001/500000000000 : ℝ)*(sp_s2_20) + (92359647/1000000000000 : ℝ)*(sp_s2_27) + (61646287873/20000000000 : ℝ)*(f.failure) + (448889545809/50000000000 : ℝ)*(f.sum) + (410251152528835169/4647856800000000000000000000000 : ℝ)*base63 + (24491286207891/34700000000000000000000000 : ℝ)*base65 + (952777201808001/4464800000000000000000000000 : ℝ)*base67 + (43041873252611/104100000000000000000000000 : ℝ)*base68 + (209323092433071707/254142800000000000000000000000 : ℝ)*base71 + (1460928726910403/4394400000000000000000000000 : ℝ)*base72 + (2186750848436057/4464800000000000000000000000 : ℝ)*base75 + (224225363451949/732400000000000000000000000 : ℝ)*base77 + (579377248162834339/2452514640000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (241/1000000000000000 : ℝ)*base87 + (241/1000000000000000 : ℝ)*base89 + (241/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13081/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13081/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (122679438708661323057258205333/29076604819400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1170060873/5000000000 : ℝ)*(base40) + (2761966873081/500000000000 : ℝ)*(major_s2_0) + (2761966873081/500000000000 : ℝ)*(major_s2_1) + (2761966873081/500000000000 : ℝ)*(major_s2_2) + (43497397/1000000000000 : ℝ)*(sp_s2_0) + (15871651/500000000000 : ℝ)*(sp_s2_1) + (2995603/250000000000 : ℝ)*(sp_s2_2) + (691051/250000000000 : ℝ)*(sp_s2_8) + (446621/31250000000 : ℝ)*(sp_s2_9) + (17636851/500000000000 : ℝ)*(sp_s2_20) + (8224216392183/1000000000000 : ℝ)*(sp_s2_21) + (4112112691037/500000000000 : ℝ)*(sp_s2_22) + (128503650239/15625000000 : ℝ)*(sp_s2_23) + (564714184529/200000000000 : ℝ)*(sp_s2_27) + (2823606196347/1000000000000 : ℝ)*(f.failure) + (411212994479/50000000000 : ℝ)*(f.sum) + (9782177924269738153/95281064400000000000000000000000 : ℝ)*base63 + (72599204405287/711350000000000000000000000 : ℝ)*base65 + (243867726403377/2232400000000000000000000000 : ℝ)*base67 + (378965021408753/2134050000000000000000000000 : ℝ)*base69 + (756293249481403779/5209927400000000000000000000000 : ℝ)*base71 + (120467065649269/2197200000000000000000000000 : ℝ)*base73 + (370273322369049/2232400000000000000000000000 : ℝ)*base75 + (51283813965933/366200000000000000000000000 : ℝ)*base77 + (3386164051652771/245251464000000000000000000000 : ℝ)*base79 + (25501/50000000000000000 : ℝ)*base86 + (25501/50000000000000000 : ℝ)*base88 + (25501/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((5493/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5493/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5581/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5581/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42681/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42681/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5373/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5373/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27239/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27239/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13081/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13081/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c323063_s2 p hpa hpb X hX hprev1

#print axioms solution

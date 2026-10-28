-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302054_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:40.9358+00:00
-- url     : https://prove2.me/submissions/47a4715e-b6f7-4969-ac31-d067dba376c3

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
theorem collision_support_c302054_s6_s6_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022566691/5000000000 : ℝ)*x 0 + (4571722133/10000000000 : ℝ)*x 1 + (-47676431/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022566691/5000000000 : ℝ)^33 ≤ (307675255787/2500000000000 : ℝ)^25 := by
    have hnat : (1022566691 : ℕ)^33*2500000000000^25 ≤ 307675255787^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022566691 5000000000 307675255787 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571722133/10000000000 : ℝ)^33 ≤ (71176293173/200000000000 : ℝ)^25 := by
    have hnat : (4571722133 : ℕ)^33*200000000000^25 ≤ 71176293173^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571722133 10000000000 71176293173 200000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47676431/78125000 : ℝ)^33 ≤ (3256552697899/6250000000000 : ℝ)^25 := by
    have hnat : (47676431 : ℕ)^33*6250000000000^25 ≤ 3256552697899^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47676431 78125000 3256552697899 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022566691/5000000000 : ℝ), (4571722133/10000000000 : ℝ), (-47676431/78125000 : ℝ)] ![(307675255787/2500000000000 : ℝ), (71176293173/200000000000 : ℝ), (3256552697899/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022566691/5000000000 : ℝ)|^33 ≤ (307675255787/2500000000000 : ℝ)^25
        have hw : |(-1022566691/5000000000 : ℝ)|=(1022566691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571722133/10000000000 : ℝ)|^33 ≤ (71176293173/200000000000 : ℝ)^25
        have hw : |(4571722133/10000000000 : ℝ)|=(4571722133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47676431/78125000 : ℝ)|^33 ≤ (3256552697899/6250000000000 : ℝ)^25
        have hw : |(-47676431/78125000 : ℝ)|=(47676431/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (678055711/1250000000 : ℝ)*x 0 + (-2903104983/10000000000 : ℝ)*x 1 + (-919555067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678055711/1250000000 : ℝ)^33 ≤ (1393795646743/3125000000000 : ℝ)^25 := by
    have hnat : (678055711 : ℕ)^33*3125000000000^25 ≤ 1393795646743^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678055711 1250000000 1393795646743 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2903104983/10000000000 : ℝ)^33 ≤ (19542441401903/100000000000000 : ℝ)^25 := by
    have hnat : (2903104983 : ℕ)^33*100000000000000^25 ≤ 19542441401903^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2903104983 10000000000 19542441401903 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919555067/2000000000 : ℝ)^33 ≤ (35856097895711/100000000000000 : ℝ)^25 := by
    have hnat : (919555067 : ℕ)^33*100000000000000^25 ≤ 35856097895711^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919555067 2000000000 35856097895711 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(678055711/1250000000 : ℝ), (-2903104983/10000000000 : ℝ), (-919555067/2000000000 : ℝ)] ![(1393795646743/3125000000000 : ℝ), (19542441401903/100000000000000 : ℝ), (35856097895711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(678055711/1250000000 : ℝ)|^33 ≤ (1393795646743/3125000000000 : ℝ)^25
        have hw : |(678055711/1250000000 : ℝ)|=(678055711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2903104983/10000000000 : ℝ)|^33 ≤ (19542441401903/100000000000000 : ℝ)^25
        have hw : |(-2903104983/10000000000 : ℝ)|=(2903104983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919555067/2000000000 : ℝ)|^33 ≤ (35856097895711/100000000000000 : ℝ)^25
        have hw : |(-919555067/2000000000 : ℝ)|=(919555067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5031412301/10000000000 : ℝ)*x 0 + (2513864811/5000000000 : ℝ)*x 1 + (2872058403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5031412301/10000000000 : ℝ)^33 ≤ (40385984803037/100000000000000 : ℝ)^25 := by
    have hnat : (5031412301 : ℕ)^33*100000000000000^25 ≤ 40385984803037^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031412301 10000000000 40385984803037 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513864811/5000000000 : ℝ)^33 ≤ (40346970154837/100000000000000 : ℝ)^25 := by
    have hnat : (2513864811 : ℕ)^33*100000000000000^25 ≤ 40346970154837^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513864811 5000000000 40346970154837 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2872058403/10000000000 : ℝ)^33 ≤ (19267045031547/100000000000000 : ℝ)^25 := by
    have hnat : (2872058403 : ℕ)^33*100000000000000^25 ≤ 19267045031547^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2872058403 10000000000 19267045031547 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5031412301/10000000000 : ℝ), (2513864811/5000000000 : ℝ), (2872058403/10000000000 : ℝ)] ![(40385984803037/100000000000000 : ℝ), (40346970154837/100000000000000 : ℝ), (19267045031547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5031412301/10000000000 : ℝ)|^33 ≤ (40385984803037/100000000000000 : ℝ)^25
        have hw : |(5031412301/10000000000 : ℝ)|=(5031412301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513864811/5000000000 : ℝ)|^33 ≤ (40346970154837/100000000000000 : ℝ)^25
        have hw : |(2513864811/5000000000 : ℝ)|=(2513864811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2872058403/10000000000 : ℝ)|^33 ≤ (19267045031547/100000000000000 : ℝ)^25
        have hw : |(2872058403/10000000000 : ℝ)|=(2872058403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2510773617/5000000000 : ℝ)*x 0 + (1003687753/2000000000 : ℝ)*x 1 + (-2894940081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2510773617/5000000000 : ℝ)^33 ≤ (20140746958043/50000000000000 : ℝ)^25 := by
    have hnat : (2510773617 : ℕ)^33*50000000000000^25 ≤ 20140746958043^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510773617 5000000000 20140746958043 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003687753/2000000000 : ℝ)^33 ≤ (100621456459/250000000000 : ℝ)^25 := by
    have hnat : (1003687753 : ℕ)^33*250000000000^25 ≤ 100621456459^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003687753 2000000000 100621456459 250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2894940081/10000000000 : ℝ)^33 ≤ (19469923474129/100000000000000 : ℝ)^25 := by
    have hnat : (2894940081 : ℕ)^33*100000000000000^25 ≤ 19469923474129^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2894940081 10000000000 19469923474129 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2510773617/5000000000 : ℝ), (1003687753/2000000000 : ℝ), (-2894940081/10000000000 : ℝ)] ![(20140746958043/50000000000000 : ℝ), (100621456459/250000000000 : ℝ), (19469923474129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2510773617/5000000000 : ℝ)|^33 ≤ (20140746958043/50000000000000 : ℝ)^25
        have hw : |(2510773617/5000000000 : ℝ)|=(2510773617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003687753/2000000000 : ℝ)|^33 ≤ (100621456459/250000000000 : ℝ)^25
        have hw : |(1003687753/2000000000 : ℝ)|=(1003687753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2894940081/10000000000 : ℝ)|^33 ≤ (19469923474129/100000000000000 : ℝ)^25
        have hw : |(-2894940081/10000000000 : ℝ)|=(2894940081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2007251831/10000000000 : ℝ)*x 0 + (4372452511/10000000000 : ℝ)*x 1 + (-157712439/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007251831/10000000000 : ℝ)^33 ≤ (12006998567699/100000000000000 : ℝ)^25 := by
    have hnat : (2007251831 : ℕ)^33*100000000000000^25 ≤ 12006998567699^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007251831 10000000000 12006998567699 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4372452511/10000000000 : ℝ)^33 ≤ (6710998309419/20000000000000 : ℝ)^25 := by
    have hnat : (4372452511 : ℕ)^33*20000000000000^25 ≤ 6710998309419^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372452511 10000000000 6710998309419 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157712439/250000000 : ℝ)^33 ≤ (13609502468493/25000000000000 : ℝ)^25 := by
    have hnat : (157712439 : ℕ)^33*25000000000000^25 ≤ 13609502468493^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157712439 250000000 13609502468493 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2007251831/10000000000 : ℝ), (4372452511/10000000000 : ℝ), (-157712439/250000000 : ℝ)] ![(12006998567699/100000000000000 : ℝ), (6710998309419/20000000000000 : ℝ), (13609502468493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2007251831/10000000000 : ℝ)|^33 ≤ (12006998567699/100000000000000 : ℝ)^25
        have hw : |(-2007251831/10000000000 : ℝ)|=(2007251831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4372452511/10000000000 : ℝ)|^33 ≤ (6710998309419/20000000000000 : ℝ)^25
        have hw : |(4372452511/10000000000 : ℝ)|=(4372452511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157712439/250000000 : ℝ)|^33 ≤ (13609502468493/25000000000000 : ℝ)^25
        have hw : |(-157712439/250000000 : ℝ)|=(157712439/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2682837939/5000000000 : ℝ)*x 0 + (-649249027/2500000000 : ℝ)*x 1 + (-4915821737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682837939/5000000000 : ℝ)^33 ≤ (43964714175843/100000000000000 : ℝ)^25 := by
    have hnat : (2682837939 : ℕ)^33*100000000000000^25 ≤ 43964714175843^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682837939 5000000000 43964714175843 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649249027/2500000000 : ℝ)^33 ≤ (2108687032809/12500000000000 : ℝ)^25 := by
    have hnat : (649249027 : ℕ)^33*12500000000000^25 ≤ 2108687032809^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649249027 2500000000 2108687032809 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4915821737/10000000000 : ℝ)^33 ≤ (39165789536143/100000000000000 : ℝ)^25 := by
    have hnat : (4915821737 : ℕ)^33*100000000000000^25 ≤ 39165789536143^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4915821737 10000000000 39165789536143 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682837939/5000000000 : ℝ), (-649249027/2500000000 : ℝ), (-4915821737/10000000000 : ℝ)] ![(43964714175843/100000000000000 : ℝ), (2108687032809/12500000000000 : ℝ), (39165789536143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682837939/5000000000 : ℝ)|^33 ≤ (43964714175843/100000000000000 : ℝ)^25
        have hw : |(2682837939/5000000000 : ℝ)|=(2682837939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649249027/2500000000 : ℝ)|^33 ≤ (2108687032809/12500000000000 : ℝ)^25
        have hw : |(-649249027/2500000000 : ℝ)|=(649249027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4915821737/10000000000 : ℝ)|^33 ≤ (39165789536143/100000000000000 : ℝ)^25
        have hw : |(-4915821737/10000000000 : ℝ)|=(4915821737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4943634797/10000000000 : ℝ)*x 0 + (2684159083/5000000000 : ℝ)*x 1 + (1279715567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4943634797/10000000000 : ℝ)^33 ≤ (19729279552273/50000000000000 : ℝ)^25 := by
    have hnat : (4943634797 : ℕ)^33*50000000000000^25 ≤ 19729279552273^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4943634797 10000000000 19729279552273 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2684159083/5000000000 : ℝ)^33 ≤ (43993294563559/100000000000000 : ℝ)^25 := by
    have hnat : (2684159083 : ℕ)^33*100000000000000^25 ≤ 43993294563559^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684159083 5000000000 43993294563559 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279715567/5000000000 : ℝ)^33 ≤ (16548146313421/100000000000000 : ℝ)^25 := by
    have hnat : (1279715567 : ℕ)^33*100000000000000^25 ≤ 16548146313421^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279715567 5000000000 16548146313421 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4943634797/10000000000 : ℝ), (2684159083/5000000000 : ℝ), (1279715567/5000000000 : ℝ)] ![(19729279552273/50000000000000 : ℝ), (43993294563559/100000000000000 : ℝ), (16548146313421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4943634797/10000000000 : ℝ)|^33 ≤ (19729279552273/50000000000000 : ℝ)^25
        have hw : |(4943634797/10000000000 : ℝ)|=(4943634797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2684159083/5000000000 : ℝ)|^33 ≤ (43993294563559/100000000000000 : ℝ)^25
        have hw : |(2684159083/5000000000 : ℝ)|=(2684159083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279715567/5000000000 : ℝ)|^33 ≤ (16548146313421/100000000000000 : ℝ)^25
        have hw : |(1279715567/5000000000 : ℝ)|=(1279715567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (31252743/62500000 : ℝ)*x 0 + (2681636663/5000000000 : ℝ)*x 1 + (-623828267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31252743/62500000 : ℝ)^33 ≤ (1251816709859/3125000000000 : ℝ)^25 := by
    have hnat : (31252743 : ℕ)^33*3125000000000^25 ≤ 1251816709859^25*62500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31252743 62500000 1251816709859 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2681636663/5000000000 : ℝ)^33 ≤ (8787746161757/20000000000000 : ℝ)^25 := by
    have hnat : (2681636663 : ℕ)^33*20000000000000^25 ≤ 8787746161757^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681636663 5000000000 8787746161757 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623828267/2500000000 : ℝ)^33 ≤ (16003134456113/100000000000000 : ℝ)^25 := by
    have hnat : (623828267 : ℕ)^33*100000000000000^25 ≤ 16003134456113^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623828267 2500000000 16003134456113 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31252743/62500000 : ℝ), (2681636663/5000000000 : ℝ), (-623828267/2500000000 : ℝ)] ![(1251816709859/3125000000000 : ℝ), (8787746161757/20000000000000 : ℝ), (16003134456113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31252743/62500000 : ℝ)|^33 ≤ (1251816709859/3125000000000 : ℝ)^25
        have hw : |(31252743/62500000 : ℝ)|=(31252743/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2681636663/5000000000 : ℝ)|^33 ≤ (8787746161757/20000000000000 : ℝ)^25
        have hw : |(2681636663/5000000000 : ℝ)|=(2681636663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623828267/2500000000 : ℝ)|^33 ≤ (16003134456113/100000000000000 : ℝ)^25
        have hw : |(-623828267/2500000000 : ℝ)|=(623828267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1781652881/10000000000 : ℝ)*x 0 + (4563986987/10000000000 : ℝ)*x 1 + (-6290469509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781652881/10000000000 : ℝ)^33 ≤ (1025856193203/10000000000000 : ℝ)^25 := by
    have hnat : (1781652881 : ℕ)^33*10000000000000^25 ≤ 1025856193203^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781652881 10000000000 1025856193203 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4563986987/10000000000 : ℝ)^33 ≤ (3550868625713/10000000000000 : ℝ)^25 := by
    have hnat : (4563986987 : ℕ)^33*10000000000000^25 ≤ 3550868625713^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563986987 10000000000 3550868625713 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6290469509/10000000000 : ℝ)^33 ≤ (54232751795287/100000000000000 : ℝ)^25 := by
    have hnat : (6290469509 : ℕ)^33*100000000000000^25 ≤ 54232751795287^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6290469509 10000000000 54232751795287 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1781652881/10000000000 : ℝ), (4563986987/10000000000 : ℝ), (-6290469509/10000000000 : ℝ)] ![(1025856193203/10000000000000 : ℝ), (3550868625713/10000000000000 : ℝ), (54232751795287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1781652881/10000000000 : ℝ)|^33 ≤ (1025856193203/10000000000000 : ℝ)^25
        have hw : |(-1781652881/10000000000 : ℝ)|=(1781652881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4563986987/10000000000 : ℝ)|^33 ≤ (3550868625713/10000000000000 : ℝ)^25
        have hw : |(4563986987/10000000000 : ℝ)|=(4563986987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6290469509/10000000000 : ℝ)|^33 ≤ (54232751795287/100000000000000 : ℝ)^25
        have hw : |(-6290469509/10000000000 : ℝ)|=(6290469509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5183709141/10000000000 : ℝ)*x 0 + (-702353711/2500000000 : ℝ)*x 1 + (-246326019/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183709141/10000000000 : ℝ)^33 ≤ (42007382883873/100000000000000 : ℝ)^25 := by
    have hnat : (5183709141 : ℕ)^33*100000000000000^25 ≤ 42007382883873^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183709141 10000000000 42007382883873 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702353711/2500000000 : ℝ)^33 ≤ (2339284078963/12500000000000 : ℝ)^25 := by
    have hnat : (702353711 : ℕ)^33*12500000000000^25 ≤ 2339284078963^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702353711 2500000000 2339284078963 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246326019/500000000 : ℝ)^33 ≤ (490979305807/1250000000000 : ℝ)^25 := by
    have hnat : (246326019 : ℕ)^33*1250000000000^25 ≤ 490979305807^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246326019 500000000 490979305807 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183709141/10000000000 : ℝ), (-702353711/2500000000 : ℝ), (-246326019/500000000 : ℝ)] ![(42007382883873/100000000000000 : ℝ), (2339284078963/12500000000000 : ℝ), (490979305807/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183709141/10000000000 : ℝ)|^33 ≤ (42007382883873/100000000000000 : ℝ)^25
        have hw : |(5183709141/10000000000 : ℝ)|=(5183709141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-702353711/2500000000 : ℝ)|^33 ≤ (2339284078963/12500000000000 : ℝ)^25
        have hw : |(-702353711/2500000000 : ℝ)|=(702353711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246326019/500000000 : ℝ)|^33 ≤ (490979305807/1250000000000 : ℝ)^25
        have hw : |(-246326019/500000000 : ℝ)|=(246326019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2689010201/5000000000 : ℝ)*x 0 + (197693261/400000000 : ℝ)*x 1 + (509746361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689010201/5000000000 : ℝ)^33 ≤ (44098277694373/100000000000000 : ℝ)^25 := by
    have hnat : (2689010201 : ℕ)^33*100000000000000^25 ≤ 44098277694373^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689010201 5000000000 44098277694373 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197693261/400000000 : ℝ)^33 ≤ (1972241431547/5000000000000 : ℝ)^25 := by
    have hnat : (197693261 : ℕ)^33*5000000000000^25 ≤ 1972241431547^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197693261 400000000 1972241431547 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509746361/2000000000 : ℝ)^33 ≤ (1645689365551/10000000000000 : ℝ)^25 := by
    have hnat : (509746361 : ℕ)^33*10000000000000^25 ≤ 1645689365551^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509746361 2000000000 1645689365551 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689010201/5000000000 : ℝ), (197693261/400000000 : ℝ), (509746361/2000000000 : ℝ)] ![(44098277694373/100000000000000 : ℝ), (1972241431547/5000000000000 : ℝ), (1645689365551/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689010201/5000000000 : ℝ)|^33 ≤ (44098277694373/100000000000000 : ℝ)^25
        have hw : |(2689010201/5000000000 : ℝ)|=(2689010201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197693261/400000000 : ℝ)|^33 ≤ (1972241431547/5000000000000 : ℝ)^25
        have hw : |(197693261/400000000 : ℝ)|=(197693261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(509746361/2000000000 : ℝ)|^33 ≤ (1645689365551/10000000000000 : ℝ)^25
        have hw : |(509746361/2000000000 : ℝ)|=(509746361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5352135773/10000000000 : ℝ)*x 0 + (4983127441/10000000000 : ℝ)*x 1 + (-1265533049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352135773/10000000000 : ℝ)^33 ≤ (8763665584309/20000000000000 : ℝ)^25 := by
    have hnat : (5352135773 : ℕ)^33*20000000000000^25 ≤ 8763665584309^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352135773 10000000000 8763665584309 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4983127441/10000000000 : ℝ)^33 ≤ (39875177778283/100000000000000 : ℝ)^25 := by
    have hnat : (4983127441 : ℕ)^33*100000000000000^25 ≤ 39875177778283^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983127441 10000000000 39875177778283 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265533049/5000000000 : ℝ)^33 ≤ (326129885661/2000000000000 : ℝ)^25 := by
    have hnat : (1265533049 : ℕ)^33*2000000000000^25 ≤ 326129885661^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265533049 5000000000 326129885661 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352135773/10000000000 : ℝ), (4983127441/10000000000 : ℝ), (-1265533049/5000000000 : ℝ)] ![(8763665584309/20000000000000 : ℝ), (39875177778283/100000000000000 : ℝ), (326129885661/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352135773/10000000000 : ℝ)|^33 ≤ (8763665584309/20000000000000 : ℝ)^25
        have hw : |(5352135773/10000000000 : ℝ)|=(5352135773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4983127441/10000000000 : ℝ)|^33 ≤ (39875177778283/100000000000000 : ℝ)^25
        have hw : |(4983127441/10000000000 : ℝ)|=(4983127441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1265533049/5000000000 : ℝ)|^33 ≤ (326129885661/2000000000000 : ℝ)^25
        have hw : |(-1265533049/5000000000 : ℝ)|=(1265533049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1629171531/10000000000 : ℝ)*x 0 + (981802123/2000000000 : ℝ)*x 1 + (-9719403/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1629171531/10000000000 : ℝ)^33 ≤ (1823165894529/20000000000000 : ℝ)^25 := by
    have hnat : (1629171531 : ℕ)^33*20000000000000^25 ≤ 1823165894529^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629171531 10000000000 1823165894529 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981802123/2000000000 : ℝ)^33 ≤ (9773543508891/25000000000000 : ℝ)^25 := by
    have hnat : (981802123 : ℕ)^33*25000000000000^25 ≤ 9773543508891^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981802123 2000000000 9773543508891 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9719403/16000000 : ℝ)^33 ≤ (25894998239537/50000000000000 : ℝ)^25 := by
    have hnat : (9719403 : ℕ)^33*50000000000000^25 ≤ 25894998239537^25*16000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9719403 16000000 25894998239537 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1629171531/10000000000 : ℝ), (981802123/2000000000 : ℝ), (-9719403/16000000 : ℝ)] ![(1823165894529/20000000000000 : ℝ), (9773543508891/25000000000000 : ℝ), (25894998239537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1629171531/10000000000 : ℝ)|^33 ≤ (1823165894529/20000000000000 : ℝ)^25
        have hw : |(-1629171531/10000000000 : ℝ)|=(1629171531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(981802123/2000000000 : ℝ)|^33 ≤ (9773543508891/25000000000000 : ℝ)^25
        have hw : |(981802123/2000000000 : ℝ)|=(981802123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9719403/16000000 : ℝ)|^33 ≤ (25894998239537/50000000000000 : ℝ)^25
        have hw : |(-9719403/16000000 : ℝ)|=(9719403/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (730728237/1250000000 : ℝ)*x 0 + (-2571239791/10000000000 : ℝ)*x 1 + (-442813887/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730728237/1250000000 : ℝ)^33 ≤ (9846152387967/20000000000000 : ℝ)^25 := by
    have hnat : (730728237 : ℕ)^33*20000000000000^25 ≤ 9846152387967^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730728237 1250000000 9846152387967 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571239791/10000000000 : ℝ)^33 ≤ (16649002022839/100000000000000 : ℝ)^25 := by
    have hnat : (2571239791 : ℕ)^33*100000000000000^25 ≤ 16649002022839^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571239791 10000000000 16649002022839 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442813887/1000000000 : ℝ)^33 ≤ (8530059003251/25000000000000 : ℝ)^25 := by
    have hnat : (442813887 : ℕ)^33*25000000000000^25 ≤ 8530059003251^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442813887 1000000000 8530059003251 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(730728237/1250000000 : ℝ), (-2571239791/10000000000 : ℝ), (-442813887/1000000000 : ℝ)] ![(9846152387967/20000000000000 : ℝ), (16649002022839/100000000000000 : ℝ), (8530059003251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(730728237/1250000000 : ℝ)|^33 ≤ (9846152387967/20000000000000 : ℝ)^25
        have hw : |(730728237/1250000000 : ℝ)|=(730728237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2571239791/10000000000 : ℝ)|^33 ≤ (16649002022839/100000000000000 : ℝ)^25
        have hw : |(-2571239791/10000000000 : ℝ)|=(2571239791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442813887/1000000000 : ℝ)|^33 ≤ (8530059003251/25000000000000 : ℝ)^25
        have hw : |(-442813887/1000000000 : ℝ)|=(442813887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (625437093/1250000000 : ℝ)*x 0 + (2499885923/5000000000 : ℝ)*x 1 + (2938599107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625437093/1250000000 : ℝ)^33 ≤ (1603618920607/4000000000000 : ℝ)^25 := by
    have hnat : (625437093 : ℕ)^33*4000000000000^25 ≤ 1603618920607^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625437093 1250000000 1603618920607 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499885923/5000000000 : ℝ)^33 ≤ (40051081368777/100000000000000 : ℝ)^25 := by
    have hnat : (2499885923 : ℕ)^33*100000000000000^25 ≤ 40051081368777^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499885923 5000000000 40051081368777 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2938599107/10000000000 : ℝ)^33 ≤ (19858445613387/100000000000000 : ℝ)^25 := by
    have hnat : (2938599107 : ℕ)^33*100000000000000^25 ≤ 19858445613387^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938599107 10000000000 19858445613387 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625437093/1250000000 : ℝ), (2499885923/5000000000 : ℝ), (2938599107/10000000000 : ℝ)] ![(1603618920607/4000000000000 : ℝ), (40051081368777/100000000000000 : ℝ), (19858445613387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625437093/1250000000 : ℝ)|^33 ≤ (1603618920607/4000000000000 : ℝ)^25
        have hw : |(625437093/1250000000 : ℝ)|=(625437093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499885923/5000000000 : ℝ)|^33 ≤ (40051081368777/100000000000000 : ℝ)^25
        have hw : |(2499885923/5000000000 : ℝ)|=(2499885923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2938599107/10000000000 : ℝ)|^33 ≤ (19858445613387/100000000000000 : ℝ)^25
        have hw : |(2938599107/10000000000 : ℝ)|=(2938599107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s6_s6_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5084154629/10000000000 : ℝ)*x 0 + (635140491/1250000000 : ℝ)*x 1 + (-2743941371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5084154629/10000000000 : ℝ)^33 ≤ (40945742498117/100000000000000 : ℝ)^25 := by
    have hnat : (5084154629 : ℕ)^33*100000000000000^25 ≤ 40945742498117^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084154629 10000000000 40945742498117 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635140491/1250000000 : ℝ)^33 ≤ (8182705388969/20000000000000 : ℝ)^25 := by
    have hnat : (635140491 : ℕ)^33*20000000000000^25 ≤ 8182705388969^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635140491 1250000000 8182705388969 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743941371/10000000000 : ℝ)^33 ≤ (4535182636349/25000000000000 : ℝ)^25 := by
    have hnat : (2743941371 : ℕ)^33*25000000000000^25 ≤ 4535182636349^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743941371 10000000000 4535182636349 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5084154629/10000000000 : ℝ), (635140491/1250000000 : ℝ), (-2743941371/10000000000 : ℝ)] ![(40945742498117/100000000000000 : ℝ), (8182705388969/20000000000000 : ℝ), (4535182636349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5084154629/10000000000 : ℝ)|^33 ≤ (40945742498117/100000000000000 : ℝ)^25
        have hw : |(5084154629/10000000000 : ℝ)|=(5084154629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635140491/1250000000 : ℝ)|^33 ≤ (8182705388969/20000000000000 : ℝ)^25
        have hw : |(635140491/1250000000 : ℝ)|=(635140491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2743941371/10000000000 : ℝ)|^33 ≤ (4535182636349/25000000000000 : ℝ)^25
        have hw : |(-2743941371/10000000000 : ℝ)|=(2743941371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302054_s6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev5 : (0 : ℝ) ≤ ((28767/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28767/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5987/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5987/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1919/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1919/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6661/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6661/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (28767/100000 : ℝ) ^ (65/16 : ℝ) ≤ (5068146862852383/800000000000000000 : ℝ) := by
    have hpowers : (28767/100000 : ℝ)^65 ≤ (5068146862852383/800000000000000000 : ℝ)^16 := by
      have hnat : (28767 : ℕ)^65*800000000000000000^16 ≤ 5068146862852383^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28767 100000 5068146862852383 800000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28767/100000 : ℝ)) (X := (5068146862852383/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0a : (805068146862852383/800000000000000000 : ℝ) ≤ (10015557198090651/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (805068146862852383/800000000000000000 : ℝ)^16 ≤ (10015557198090651/10000000000000000 : ℝ)^65 := by
      have hnat : (805068146862852383 : ℕ)^16*10000000000000000^65 ≤ 10015557198090651^65*800000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        805068146862852383 800000000000000000 10015557198090651 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015557198090651/10000000000000000 : ℝ)) (X := (805068146862852383/800000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0b : (405068146862852383/400000000000000000 : ℝ) ≤ (5015520370399567/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (405068146862852383/400000000000000000 : ℝ)^16 ≤ (5015520370399567/5000000000000000 : ℝ)^65 := by
      have hnat : (405068146862852383 : ℕ)^16*5000000000000000^65 ≤ 5015520370399567^65*400000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        405068146862852383 400000000000000000 5015520370399567 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015520370399567/5000000000000000 : ℝ)) (X := (405068146862852383/400000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(15557198090651/2876700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15483542708483/2876700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (28767/100000 : ℝ)) (alpha := (15557198090651/2876700000000000 : ℝ)) (beta := (15483542708483/2876700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (28767/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(15557198090651/2876700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15483542708483/2876700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (5987/20000 : ℝ) ^ (65/16 : ℝ) ≤ (744694684320472881/100000000000000000000 : ℝ) := by
    have hpowers : (5987/20000 : ℝ)^65 ≤ (744694684320472881/100000000000000000000 : ℝ)^16 := by
      have hnat : (5987 : ℕ)^65*100000000000000000000^16 ≤ 744694684320472881^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5987 20000 744694684320472881 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5987/20000 : ℝ)) (X := (744694684320472881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1a : (100744694684320472881/100000000000000000000 : ℝ) ≤ (1001827971533061/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100744694684320472881/100000000000000000000 : ℝ)^16 ≤ (1001827971533061/1000000000000000 : ℝ)^65 := by
      have hnat : (100744694684320472881 : ℕ)^16*1000000000000000^65 ≤ 1001827971533061^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100744694684320472881 100000000000000000000 1001827971533061 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001827971533061/1000000000000000 : ℝ)) (X := (100744694684320472881/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1b : (50744694684320472881/50000000000000000000 : ℝ) ≤ (2509114462900201/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50744694684320472881/50000000000000000000 : ℝ)^16 ≤ (2509114462900201/2500000000000000 : ℝ)^65 := by
      have hnat : (50744694684320472881 : ℕ)^16*2500000000000000^65 ≤ 2509114462900201^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50744694684320472881 50000000000000000000 2509114462900201 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509114462900201/2500000000000000 : ℝ)) (X := (50744694684320472881/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1827971533061/299350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(9089068135097/1496750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (5987/20000 : ℝ)) (alpha := (1827971533061/299350000000000 : ℝ)) (beta := (9089068135097/1496750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5987/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1827971533061/299350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(9089068135097/1496750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (1919/10000 : ℝ) ^ (65/16 : ℝ) ≤ (122318482596474839/100000000000000000000 : ℝ) := by
    have hpowers : (1919/10000 : ℝ)^65 ≤ (122318482596474839/100000000000000000000 : ℝ)^16 := by
      have hnat : (1919 : ℕ)^65*100000000000000000000^16 ≤ 122318482596474839^16*10000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1919 10000 122318482596474839 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1919/10000 : ℝ)) (X := (122318482596474839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2a : (100122318482596474839/100000000000000000000 : ℝ) ≤ (10003009529313743/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100122318482596474839/100000000000000000000 : ℝ)^16 ≤ (10003009529313743/10000000000000000 : ℝ)^65 := by
      have hnat : (100122318482596474839 : ℕ)^16*10000000000000000^65 ≤ 10003009529313743^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100122318482596474839 100000000000000000000 10003009529313743 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003009529313743/10000000000000000 : ℝ)) (X := (100122318482596474839/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2b : (50122318482596474839/50000000000000000000 : ℝ) ≤ (10006016288226283/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50122318482596474839/50000000000000000000 : ℝ)^16 ≤ (10006016288226283/10000000000000000 : ℝ)^65 := by
      have hnat : (50122318482596474839 : ℕ)^16*10000000000000000^65 ≤ 10006016288226283^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50122318482596474839 50000000000000000000 10006016288226283 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006016288226283/10000000000000000 : ℝ)) (X := (50122318482596474839/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(3009529313743/1919000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(150337945627/95950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1919/10000 : ℝ)) (alpha := (3009529313743/1919000000000000 : ℝ)) (beta := (150337945627/95950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1919/10000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(3009529313743/1919000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(150337945627/95950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-1022566691/5000000000 : ℝ)*X 0 0+(4571722133/10000000000 : ℝ)*X 0 1+(-47676431/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((678055711/1250000000 : ℝ)*X 1 0+(-2903104983/10000000000 : ℝ)*X 1 1+(-919555067/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((5031412301/10000000000 : ℝ)*X 2 0+(2513864811/5000000000 : ℝ)*X 2 1+(2872058403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((2510773617/5000000000 : ℝ)*X 0 0+(1003687753/2000000000 : ℝ)*X 0 1+(-2894940081/10000000000 : ℝ)*X 0 2+(2510773617/5000000000 : ℝ)*X 1 0+(1003687753/2000000000 : ℝ)*X 1 1+(-2894940081/10000000000 : ℝ)*X 1 2+(2510773617/5000000000 : ℝ)*X 2 0+(1003687753/2000000000 : ℝ)*X 2 1+(-2894940081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2007251831/10000000000 : ℝ)*X 0 0+(4372452511/10000000000 : ℝ)*X 0 1+(-157712439/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((2682837939/5000000000 : ℝ)*X 1 0+(-649249027/2500000000 : ℝ)*X 1 1+(-4915821737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((4943634797/10000000000 : ℝ)*X 2 0+(2684159083/5000000000 : ℝ)*X 2 1+(1279715567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((31252743/62500000 : ℝ)*X 0 0+(2681636663/5000000000 : ℝ)*X 0 1+(-623828267/2500000000 : ℝ)*X 0 2+(31252743/62500000 : ℝ)*X 1 0+(2681636663/5000000000 : ℝ)*X 1 1+(-623828267/2500000000 : ℝ)*X 1 2+(31252743/62500000 : ℝ)*X 2 0+(2681636663/5000000000 : ℝ)*X 2 1+(-623828267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-1781652881/10000000000 : ℝ)*X 0 0+(4563986987/10000000000 : ℝ)*X 0 1+(-6290469509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((5183709141/10000000000 : ℝ)*X 1 0+(-702353711/2500000000 : ℝ)*X 1 1+(-246326019/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((2689010201/5000000000 : ℝ)*X 2 0+(197693261/400000000 : ℝ)*X 2 1+(509746361/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((5352135773/10000000000 : ℝ)*X 0 0+(4983127441/10000000000 : ℝ)*X 0 1+(-1265533049/5000000000 : ℝ)*X 0 2+(5352135773/10000000000 : ℝ)*X 1 0+(4983127441/10000000000 : ℝ)*X 1 1+(-1265533049/5000000000 : ℝ)*X 1 2+(5352135773/10000000000 : ℝ)*X 2 0+(4983127441/10000000000 : ℝ)*X 2 1+(-1265533049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-1629171531/10000000000 : ℝ)*X 0 0+(981802123/2000000000 : ℝ)*X 0 1+(-9719403/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((730728237/1250000000 : ℝ)*X 1 0+(-2571239791/10000000000 : ℝ)*X 1 1+(-442813887/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((625437093/1250000000 : ℝ)*X 2 0+(2499885923/5000000000 : ℝ)*X 2 1+(2938599107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((5084154629/10000000000 : ℝ)*X 0 0+(635140491/1250000000 : ℝ)*X 0 1+(-2743941371/10000000000 : ℝ)*X 0 2+(5084154629/10000000000 : ℝ)*X 1 0+(635140491/1250000000 : ℝ)*X 1 1+(-2743941371/10000000000 : ℝ)*X 1 2+(5084154629/10000000000 : ℝ)*X 2 0+(635140491/1250000000 : ℝ)*X 2 1+(-2743941371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((19983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4487786101575838538398541/358808393750000000000000000000 : ℝ) := by norm_num
    linear_combination (1278905105219/500000000000 : ℝ)*(base39) + (754457/200000000000 : ℝ)*(base50) + (446529056767/500000000000 : ℝ)*(base60) + (7361939946287/500000000000 : ℝ)*(major_s6_0) + (7361939946287/500000000000 : ℝ)*(major_s6_1) + (7361939946287/500000000000 : ℝ)*(major_s6_2) + (9480371/50000000000 : ℝ)*(sp_s6_0) + (9788429178507/500000000000 : ℝ)*(sp_s6_7) + (611782077611/31250000000 : ℝ)*(sp_s6_8) + (19577057104257/1000000000000 : ℝ)*(sp_s6_9) + (394821475969/40000000000 : ℝ)*(sp_s6_13) + (17075233/100000000000 : ℝ)*(sp_s6_14) + (48058303/250000000000 : ℝ)*(sp_s6_15) + (161612507/1000000000000 : ℝ)*(sp_s6_23) + (394821475969/40000000000 : ℝ)*(f.failure) + (4894304679191/250000000000 : ℝ)*(f.sum) + (1656314769316216127/5744526500000000000000000000000 : ℝ)*base63 + (1462812445283/23987500000000000000000000 : ℝ)*base64 + (111628268365643/374187500000000000000000000 : ℝ)*base67 + (50901982808359/959500000000000000000000000 : ℝ)*base68 + (138910230437694779/2760193650000000000000000000000 : ℝ)*base71 + (227707649694239/1438350000000000000000000000 : ℝ)*base72 + (41170263221419/299350000000000000000000000 : ℝ)*base75 + (62558267949053/1438350000000000000000000000 : ℝ)*base76 + (1873775059606748983/21528503625000000000000000000000 : ℝ)*base78 + (27/400000000000000 : ℝ)*base86 + (27/400000000000000 : ℝ)*base88 + (27/400000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10483/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (100514870616210782837736135537/27542132304250000000000000000000000 : ℝ) := by norm_num
    linear_combination (250728789583/100000000000 : ℝ)*(base39) + (2326237/1000000000000 : ℝ)*(base40) + (685699138799/1000000000000 : ℝ)*(base60) + (7378752598931/500000000000 : ℝ)*(major_s6_0) + (7378752598931/500000000000 : ℝ)*(major_s6_1) + (7378752598931/500000000000 : ℝ)*(major_s6_2) + (34292949/1000000000000 : ℝ)*(sp_s6_6) + (28580671/250000000000 : ℝ)*(sp_s6_7) + (71082689/1000000000000 : ℝ)*(sp_s6_8) + (19621816356929/1000000000000 : ℝ)*(sp_s6_14) + (19621859596923/1000000000000 : ℝ)*(sp_s6_15) + (392437703093/20000000000 : ℝ)*(sp_s6_16) + (9893044206657/1000000000000 : ℝ)*(sp_s6_20) + (45524963/1000000000000 : ℝ)*(sp_s6_23) + (4946539249803/500000000000 : ℝ)*(f.failure) + (19621930679613/1000000000000 : ℝ)*(f.sum) + (3428870224549556951/5744526500000000000000000000000 : ℝ)*base63 + (92392431547081/95950000000000000000000000 : ℝ)*base64 + (420714325693343/748375000000000000000000000 : ℝ)*base67 + (506773833407333/959500000000000000000000000 : ℝ)*base69 + (2176876904078105773/2760193650000000000000000000000 : ℝ)*base70 + (701292822113653/1438350000000000000000000000 : ℝ)*base73 + (147053895013983/299350000000000000000000000 : ℝ)*base74 + (918411287300369/1438350000000000000000000000 : ℝ)*base76 + (16486078031375388217/43057007250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1351/5000000000000000 : ℝ)*base87 + (1351/5000000000000000 : ℝ)*base89 + (1351/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6661/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6661/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (238664695507654408852788147927/27542132304250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1915490587989/1000000000000 : ℝ)*(base39) + (1247129/250000000000 : ℝ)*(base50) + (7595501539/100000000000 : ℝ)*(base60) + (1154096801577/125000000000 : ℝ)*(major_s6_0) + (1154096801577/125000000000 : ℝ)*(major_s6_1) + (1154096801577/125000000000 : ℝ)*(major_s6_2) + (13713073/200000000000 : ℝ)*(sp_s6_1) + (35150287/1000000000000 : ℝ)*(sp_s6_2) + (70335647/500000000000 : ℝ)*(sp_s6_13) + (283343657/1000000000000 : ℝ)*(sp_s6_20) + (12276114809429/1000000000000 : ℝ)*(sp_s6_21) + (383626445127/31250000000 : ℝ)*(sp_s6_22) + (6138039829571/500000000000 : ℝ)*(sp_s6_23) + (6189007112363/1000000000000 : ℝ)*(sp_s6_27) + (1237886225463/200000000000 : ℝ)*(f.failure) + (12276114809429/1000000000000 : ℝ)*(f.sum) + (201641586763488809/2872263250000000000000000000000 : ℝ)*base63 + (2842133002301/2998437500000000000000000 : ℝ)*base65 + (901765675111101/748375000000000000000000000 : ℝ)*base66 + (263321615599361/239875000000000000000000000 : ℝ)*base69 + (147023952546634051/460032275000000000000000000000 : ℝ)*base71 + (105401748454371/239725000000000000000000000 : ℝ)*base72 + (189422414628871/299350000000000000000000000 : ℝ)*base75 + (483728937570841/479450000000000000000000000 : ℝ)*base77 + (89273754715551889/448510492187500000000000000000 : ℝ)*base78 + (429/2000000000000000 : ℝ)*base86 + (429/2000000000000000 : ℝ)*base88 + (429/2000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev5 : (0 : ℝ) ≤ ((28767/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28767/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5987/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5987/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1919/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1919/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6661/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6661/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302054_s6 p hpa hpb X hX hprev5

#print axioms solution

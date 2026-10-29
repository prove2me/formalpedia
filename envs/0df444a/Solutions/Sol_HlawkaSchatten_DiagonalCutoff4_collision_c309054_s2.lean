-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:02:33.90084+00:00
-- url     : https://prove2.me/submissions/c2de5ce8-f35f-41f7-ba0c-43194b6ed7a2

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
theorem collision_support_c309054_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5706139737/10000000000 : ℝ)*x 0 + (-2094824731/10000000000 : ℝ)*x 1 + (-1197039809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5706139737/10000000000 : ℝ)^35 ≤ (9664459154039/20000000000000 : ℝ)^27 := by
    have hnat : (5706139737 : ℕ)^35*20000000000000^27 ≤ 9664459154039^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706139737 10000000000 9664459154039 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094824731/10000000000 : ℝ)^35 ≤ (6591378822447/50000000000000 : ℝ)^27 := by
    have hnat : (2094824731 : ℕ)^35*50000000000000^27 ≤ 6591378822447^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094824731 10000000000 6591378822447 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197039809/2500000000 : ℝ)^35 ≤ (19247473288067/50000000000000 : ℝ)^27 := by
    have hnat : (1197039809 : ℕ)^35*50000000000000^27 ≤ 19247473288067^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197039809 2500000000 19247473288067 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5706139737/10000000000 : ℝ), (-2094824731/10000000000 : ℝ), (-1197039809/2500000000 : ℝ)] ![(9664459154039/20000000000000 : ℝ), (6591378822447/50000000000000 : ℝ), (19247473288067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5706139737/10000000000 : ℝ)|^35 ≤ (9664459154039/20000000000000 : ℝ)^27
        have hw : |(5706139737/10000000000 : ℝ)|=(5706139737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094824731/10000000000 : ℝ)|^35 ≤ (6591378822447/50000000000000 : ℝ)^27
        have hw : |(-2094824731/10000000000 : ℝ)|=(2094824731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1197039809/2500000000 : ℝ)|^35 ≤ (19247473288067/50000000000000 : ℝ)^27
        have hw : |(-1197039809/2500000000 : ℝ)|=(1197039809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5331953777/10000000000 : ℝ)*x 0 + (2636663259/5000000000 : ℝ)*x 1 + (-981618303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5331953777/10000000000 : ℝ)^35 ≤ (44255150349233/100000000000000 : ℝ)^27 := by
    have hnat : (5331953777 : ℕ)^35*100000000000000^27 ≤ 44255150349233^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331953777 10000000000 44255150349233 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636663259/5000000000 : ℝ)^35 ≤ (43625395594479/100000000000000 : ℝ)^27 := by
    have hnat : (2636663259 : ℕ)^35*100000000000000^27 ≤ 43625395594479^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636663259 5000000000 43625395594479 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981618303/5000000000 : ℝ)^35 ≤ (484778161521/4000000000000 : ℝ)^27 := by
    have hnat : (981618303 : ℕ)^35*4000000000000^27 ≤ 484778161521^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981618303 5000000000 484778161521 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5331953777/10000000000 : ℝ), (2636663259/5000000000 : ℝ), (-981618303/5000000000 : ℝ)] ![(44255150349233/100000000000000 : ℝ), (43625395594479/100000000000000 : ℝ), (484778161521/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5331953777/10000000000 : ℝ)|^35 ≤ (44255150349233/100000000000000 : ℝ)^27
        have hw : |(5331953777/10000000000 : ℝ)|=(5331953777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636663259/5000000000 : ℝ)|^35 ≤ (43625395594479/100000000000000 : ℝ)^27
        have hw : |(2636663259/5000000000 : ℝ)|=(2636663259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-981618303/5000000000 : ℝ)|^35 ≤ (484778161521/4000000000000 : ℝ)^27
        have hw : |(-981618303/5000000000 : ℝ)|=(981618303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-209050553/5000000000 : ℝ)*x 0 + (3812590371/10000000000 : ℝ)*x 1 + (-7570888723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209050553/5000000000 : ℝ)^35 ≤ (163219512657/10000000000000 : ℝ)^27 := by
    have hnat : (209050553 : ℕ)^35*10000000000000^27 ≤ 163219512657^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209050553 5000000000 163219512657 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3812590371/10000000000 : ℝ)^35 ≤ (3581353910123/12500000000000 : ℝ)^27 := by
    have hnat : (3812590371 : ℕ)^35*12500000000000^27 ≤ 3581353910123^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3812590371 10000000000 3581353910123 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7570888723/10000000000 : ℝ)^35 ≤ (6971697357717/10000000000000 : ℝ)^27 := by
    have hnat : (7570888723 : ℕ)^35*10000000000000^27 ≤ 6971697357717^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7570888723 10000000000 6971697357717 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209050553/5000000000 : ℝ), (3812590371/10000000000 : ℝ), (-7570888723/10000000000 : ℝ)] ![(163219512657/10000000000000 : ℝ), (3581353910123/12500000000000 : ℝ), (6971697357717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209050553/5000000000 : ℝ)|^35 ≤ (163219512657/10000000000000 : ℝ)^27
        have hw : |(-209050553/5000000000 : ℝ)|=(209050553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3812590371/10000000000 : ℝ)|^35 ≤ (3581353910123/12500000000000 : ℝ)^27
        have hw : |(3812590371/10000000000 : ℝ)|=(3812590371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7570888723/10000000000 : ℝ)|^35 ≤ (6971697357717/10000000000000 : ℝ)^27
        have hw : |(-7570888723/10000000000 : ℝ)|=(7570888723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (637313843/1250000000 : ℝ)*x 0 + (-221576267/2500000000 : ℝ)*x 1 + (-1552343157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (637313843/1250000000 : ℝ)^35 ≤ (10439985424263/25000000000000 : ℝ)^27 := by
    have hnat : (637313843 : ℕ)^35*25000000000000^27 ≤ 10439985424263^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637313843 1250000000 10439985424263 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221576267/2500000000 : ℝ)^35 ≤ (540338677311/12500000000000 : ℝ)^27 := by
    have hnat : (221576267 : ℕ)^35*12500000000000^27 ≤ 540338677311^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221576267 2500000000 540338677311 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552343157/2500000000 : ℝ)^35 ≤ (10783469773741/20000000000000 : ℝ)^27 := by
    have hnat : (1552343157 : ℕ)^35*20000000000000^27 ≤ 10783469773741^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552343157 2500000000 10783469773741 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(637313843/1250000000 : ℝ), (-221576267/2500000000 : ℝ), (-1552343157/2500000000 : ℝ)] ![(10439985424263/25000000000000 : ℝ), (540338677311/12500000000000 : ℝ), (10783469773741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(637313843/1250000000 : ℝ)|^35 ≤ (10439985424263/25000000000000 : ℝ)^27
        have hw : |(637313843/1250000000 : ℝ)|=(637313843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221576267/2500000000 : ℝ)|^35 ≤ (540338677311/12500000000000 : ℝ)^27
        have hw : |(-221576267/2500000000 : ℝ)|=(221576267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1552343157/2500000000 : ℝ)|^35 ≤ (10783469773741/20000000000000 : ℝ)^27
        have hw : |(-1552343157/2500000000 : ℝ)|=(1552343157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (36016017/78125000 : ℝ)*x 0 + (3416757867/5000000000 : ℝ)*x 1 + (545830697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36016017/78125000 : ℝ)^35 ≤ (36649063592113/100000000000000 : ℝ)^27 := by
    have hnat : (36016017 : ℕ)^35*100000000000000^27 ≤ 36649063592113^27*78125000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36016017 78125000 36649063592113 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3416757867/5000000000 : ℝ)^35 ≤ (61044970361851/100000000000000 : ℝ)^27 := by
    have hnat : (3416757867 : ℕ)^35*100000000000000^27 ≤ 61044970361851^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416757867 5000000000 61044970361851 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545830697/10000000000 : ℝ)^35 ≤ (461193207161/20000000000000 : ℝ)^27 := by
    have hnat : (545830697 : ℕ)^35*20000000000000^27 ≤ 461193207161^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545830697 10000000000 461193207161 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36016017/78125000 : ℝ), (3416757867/5000000000 : ℝ), (545830697/10000000000 : ℝ)] ![(36649063592113/100000000000000 : ℝ), (61044970361851/100000000000000 : ℝ), (461193207161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36016017/78125000 : ℝ)|^35 ≤ (36649063592113/100000000000000 : ℝ)^27
        have hw : |(36016017/78125000 : ℝ)|=(36016017/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3416757867/5000000000 : ℝ)|^35 ≤ (61044970361851/100000000000000 : ℝ)^27
        have hw : |(3416757867/5000000000 : ℝ)|=(3416757867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545830697/10000000000 : ℝ)|^35 ≤ (461193207161/20000000000000 : ℝ)^27
        have hw : |(545830697/10000000000 : ℝ)|=(545830697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4811157607/10000000000 : ℝ)*x 0 + (3325886677/5000000000 : ℝ)*x 1 + (-109549511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4811157607/10000000000 : ℝ)^35 ≤ (9683699882439/25000000000000 : ℝ)^27 := by
    have hnat : (4811157607 : ℕ)^35*25000000000000^27 ≤ 9683699882439^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811157607 10000000000 9683699882439 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3325886677/5000000000 : ℝ)^35 ≤ (29474365693429/50000000000000 : ℝ)^27 := by
    have hnat : (3325886677 : ℕ)^35*50000000000000^27 ≤ 29474365693429^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3325886677 5000000000 29474365693429 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109549511/2000000000 : ℝ)^35 ≤ (579117268093/25000000000000 : ℝ)^27 := by
    have hnat : (109549511 : ℕ)^35*25000000000000^27 ≤ 579117268093^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109549511 2000000000 579117268093 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4811157607/10000000000 : ℝ), (3325886677/5000000000 : ℝ), (-109549511/2000000000 : ℝ)] ![(9683699882439/25000000000000 : ℝ), (29474365693429/50000000000000 : ℝ), (579117268093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4811157607/10000000000 : ℝ)|^35 ≤ (9683699882439/25000000000000 : ℝ)^27
        have hw : |(4811157607/10000000000 : ℝ)|=(4811157607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3325886677/5000000000 : ℝ)|^35 ≤ (29474365693429/50000000000000 : ℝ)^27
        have hw : |(3325886677/5000000000 : ℝ)|=(3325886677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109549511/2000000000 : ℝ)|^35 ≤ (579117268093/25000000000000 : ℝ)^27
        have hw : |(-109549511/2000000000 : ℝ)|=(109549511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3213793/10000000000 : ℝ)*x 0 + (422432007/1000000000 : ℝ)*x 1 + (-3682648859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3213793/10000000000 : ℝ)^35 ≤ (2965242673/100000000000000 : ℝ)^27 := by
    have hnat : (3213793 : ℕ)^35*100000000000000^27 ≤ 2965242673^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3213793 10000000000 2965242673 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422432007/1000000000 : ℝ)^35 ≤ (16362134252053/50000000000000 : ℝ)^27 := by
    have hnat : (422432007 : ℕ)^35*50000000000000^27 ≤ 16362134252053^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422432007 1000000000 16362134252053 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3682648859/5000000000 : ℝ)^35 ≤ (67272766243297/100000000000000 : ℝ)^27 := by
    have hnat : (3682648859 : ℕ)^35*100000000000000^27 ≤ 67272766243297^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682648859 5000000000 67272766243297 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3213793/10000000000 : ℝ), (422432007/1000000000 : ℝ), (-3682648859/5000000000 : ℝ)] ![(2965242673/100000000000000 : ℝ), (16362134252053/50000000000000 : ℝ), (67272766243297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3213793/10000000000 : ℝ)|^35 ≤ (2965242673/100000000000000 : ℝ)^27
        have hw : |(-3213793/10000000000 : ℝ)|=(3213793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422432007/1000000000 : ℝ)|^35 ≤ (16362134252053/50000000000000 : ℝ)^27
        have hw : |(422432007/1000000000 : ℝ)|=(422432007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3682648859/5000000000 : ℝ)|^35 ≤ (67272766243297/100000000000000 : ℝ)^27
        have hw : |(-3682648859/5000000000 : ℝ)|=(3682648859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4755531723/10000000000 : ℝ)*x 0 + (-287724093/2000000000 : ℝ)*x 1 + (-387130789/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4755531723/10000000000 : ℝ)^35 ≤ (7631051115739/20000000000000 : ℝ)^27 := by
    have hnat : (4755531723 : ℕ)^35*20000000000000^27 ≤ 7631051115739^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755531723 10000000000 7631051115739 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287724093/2000000000 : ℝ)^35 ≤ (8099324920457/100000000000000 : ℝ)^27 := by
    have hnat : (287724093 : ℕ)^35*100000000000000^27 ≤ 8099324920457^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287724093 2000000000 8099324920457 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387130789/625000000 : ℝ)^35 ≤ (53745419484753/100000000000000 : ℝ)^27 := by
    have hnat : (387130789 : ℕ)^35*100000000000000^27 ≤ 53745419484753^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387130789 625000000 53745419484753 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4755531723/10000000000 : ℝ), (-287724093/2000000000 : ℝ), (-387130789/625000000 : ℝ)] ![(7631051115739/20000000000000 : ℝ), (8099324920457/100000000000000 : ℝ), (53745419484753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4755531723/10000000000 : ℝ)|^35 ≤ (7631051115739/20000000000000 : ℝ)^27
        have hw : |(4755531723/10000000000 : ℝ)|=(4755531723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287724093/2000000000 : ℝ)|^35 ≤ (8099324920457/100000000000000 : ℝ)^27
        have hw : |(-287724093/2000000000 : ℝ)|=(287724093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387130789/625000000 : ℝ)|^35 ≤ (53745419484753/100000000000000 : ℝ)^27
        have hw : |(-387130789/625000000 : ℝ)|=(387130789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3443153869/5000000000 : ℝ)*x 0 + (903059103/2000000000 : ℝ)*x 1 + (610720339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3443153869/5000000000 : ℝ)^35 ≤ (15414250541583/25000000000000 : ℝ)^27 := by
    have hnat : (3443153869 : ℕ)^35*25000000000000^27 ≤ 15414250541583^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443153869 5000000000 15414250541583 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903059103/2000000000 : ℝ)^35 ≤ (7135114857377/20000000000000 : ℝ)^27 := by
    have hnat : (903059103 : ℕ)^35*20000000000000^27 ≤ 7135114857377^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903059103 2000000000 7135114857377 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610720339/10000000000 : ℝ)^35 ≤ (266742353593/10000000000000 : ℝ)^27 := by
    have hnat : (610720339 : ℕ)^35*10000000000000^27 ≤ 266742353593^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610720339 10000000000 266742353593 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3443153869/5000000000 : ℝ), (903059103/2000000000 : ℝ), (610720339/10000000000 : ℝ)] ![(15414250541583/25000000000000 : ℝ), (7135114857377/20000000000000 : ℝ), (266742353593/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3443153869/5000000000 : ℝ)|^35 ≤ (15414250541583/25000000000000 : ℝ)^27
        have hw : |(3443153869/5000000000 : ℝ)|=(3443153869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903059103/2000000000 : ℝ)|^35 ≤ (7135114857377/20000000000000 : ℝ)^27
        have hw : |(903059103/2000000000 : ℝ)|=(903059103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(610720339/10000000000 : ℝ)|^35 ≤ (266742353593/10000000000000 : ℝ)^27
        have hw : |(610720339/10000000000 : ℝ)|=(610720339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1605774899/2500000000 : ℝ)*x 0 + (1186119791/2500000000 : ℝ)*x 1 + (-108586157/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1605774899/2500000000 : ℝ)^35 ≤ (56335234946513/100000000000000 : ℝ)^27 := by
    have hnat : (1605774899 : ℕ)^35*100000000000000^27 ≤ 56335234946513^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605774899 2500000000 56335234946513 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1186119791/2500000000 : ℝ)^35 ≤ (19020170813031/50000000000000 : ℝ)^27 := by
    have hnat : (1186119791 : ℕ)^35*50000000000000^27 ≤ 19020170813031^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186119791 2500000000 19020170813031 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108586157/1000000000 : ℝ)^35 ≤ (5624423418091/100000000000000 : ℝ)^27 := by
    have hnat : (108586157 : ℕ)^35*100000000000000^27 ≤ 5624423418091^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108586157 1000000000 5624423418091 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1605774899/2500000000 : ℝ), (1186119791/2500000000 : ℝ), (-108586157/1000000000 : ℝ)] ![(56335234946513/100000000000000 : ℝ), (19020170813031/50000000000000 : ℝ), (5624423418091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1605774899/2500000000 : ℝ)|^35 ≤ (56335234946513/100000000000000 : ℝ)^27
        have hw : |(1605774899/2500000000 : ℝ)|=(1605774899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1186119791/2500000000 : ℝ)|^35 ≤ (19020170813031/50000000000000 : ℝ)^27
        have hw : |(1186119791/2500000000 : ℝ)|=(1186119791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108586157/1000000000 : ℝ)|^35 ≤ (5624423418091/100000000000000 : ℝ)^27
        have hw : |(-108586157/1000000000 : ℝ)|=(108586157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (352961/5000000000 : ℝ)*x 0 + (5432275239/10000000000 : ℝ)*x 1 + (-3137714739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352961/5000000000 : ℝ)^35 ≤ (103919899/25000000000000 : ℝ)^27 := by
    have hnat : (352961 : ℕ)^35*25000000000000^27 ≤ 103919899^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352961 5000000000 103919899 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432275239/10000000000 : ℝ)^35 ≤ (45337528887811/100000000000000 : ℝ)^27 := by
    have hnat : (5432275239 : ℕ)^35*100000000000000^27 ≤ 45337528887811^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432275239 10000000000 45337528887811 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3137714739/5000000000 : ℝ)^35 ≤ (3416378463773/6250000000000 : ℝ)^27 := by
    have hnat : (3137714739 : ℕ)^35*6250000000000^27 ≤ 3416378463773^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137714739 5000000000 3416378463773 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(352961/5000000000 : ℝ), (5432275239/10000000000 : ℝ), (-3137714739/5000000000 : ℝ)] ![(103919899/25000000000000 : ℝ), (45337528887811/100000000000000 : ℝ), (3416378463773/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(352961/5000000000 : ℝ)|^35 ≤ (103919899/25000000000000 : ℝ)^27
        have hw : |(352961/5000000000 : ℝ)|=(352961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432275239/10000000000 : ℝ)|^35 ≤ (45337528887811/100000000000000 : ℝ)^27
        have hw : |(5432275239/10000000000 : ℝ)|=(5432275239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3137714739/5000000000 : ℝ)|^35 ≤ (3416378463773/6250000000000 : ℝ)^27
        have hw : |(-3137714739/5000000000 : ℝ)|=(3137714739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3325229187/5000000000 : ℝ)*x 0 + (-264166381/2000000000 : ℝ)*x 1 + (-866526499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3325229187/5000000000 : ℝ)^35 ≤ (11786725089563/20000000000000 : ℝ)^27 := by
    have hnat : (3325229187 : ℕ)^35*20000000000000^27 ≤ 11786725089563^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3325229187 5000000000 11786725089563 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264166381/2000000000 : ℝ)^35 ≤ (906291588687/12500000000000 : ℝ)^27 := by
    have hnat : (264166381 : ℕ)^35*12500000000000^27 ≤ 906291588687^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264166381 2000000000 906291588687 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866526499/2000000000 : ℝ)^35 ≤ (33816041820909/100000000000000 : ℝ)^27 := by
    have hnat : (866526499 : ℕ)^35*100000000000000^27 ≤ 33816041820909^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866526499 2000000000 33816041820909 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3325229187/5000000000 : ℝ), (-264166381/2000000000 : ℝ), (-866526499/2000000000 : ℝ)] ![(11786725089563/20000000000000 : ℝ), (906291588687/12500000000000 : ℝ), (33816041820909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3325229187/5000000000 : ℝ)|^35 ≤ (11786725089563/20000000000000 : ℝ)^27
        have hw : |(3325229187/5000000000 : ℝ)|=(3325229187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264166381/2000000000 : ℝ)|^35 ≤ (906291588687/12500000000000 : ℝ)^27
        have hw : |(-264166381/2000000000 : ℝ)|=(264166381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-866526499/2000000000 : ℝ)|^35 ≤ (33816041820909/100000000000000 : ℝ)^27
        have hw : |(-866526499/2000000000 : ℝ)|=(866526499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5183405229/10000000000 : ℝ)*x 0 + (1410556663/2500000000 : ℝ)*x 1 + (103455067/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183405229/10000000000 : ℝ)^35 ≤ (42663520747073/100000000000000 : ℝ)^27 := by
    have hnat : (5183405229 : ℕ)^35*100000000000000^27 ≤ 42663520747073^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183405229 10000000000 42663520747073 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410556663/2500000000 : ℝ)^35 ≤ (23810923757849/50000000000000 : ℝ)^27 := by
    have hnat : (1410556663 : ℕ)^35*50000000000000^27 ≤ 23810923757849^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410556663 2500000000 23810923757849 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103455067/625000000 : ℝ)^35 ≤ (2428657930141/25000000000000 : ℝ)^27 := by
    have hnat : (103455067 : ℕ)^35*25000000000000^27 ≤ 2428657930141^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103455067 625000000 2428657930141 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183405229/10000000000 : ℝ), (1410556663/2500000000 : ℝ), (103455067/625000000 : ℝ)] ![(42663520747073/100000000000000 : ℝ), (23810923757849/50000000000000 : ℝ), (2428657930141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183405229/10000000000 : ℝ)|^35 ≤ (42663520747073/100000000000000 : ℝ)^27
        have hw : |(5183405229/10000000000 : ℝ)|=(5183405229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1410556663/2500000000 : ℝ)|^35 ≤ (23810923757849/50000000000000 : ℝ)^27
        have hw : |(1410556663/2500000000 : ℝ)|=(1410556663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103455067/625000000 : ℝ)|^35 ≤ (2428657930141/25000000000000 : ℝ)^27
        have hw : |(103455067/625000000 : ℝ)|=(103455067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6000547191/10000000000 : ℝ)*x 0 + (4779873721/10000000000 : ℝ)*x 1 + (-1694334019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6000547191/10000000000 : ℝ)^35 ≤ (12894652307533/25000000000000 : ℝ)^27 := by
    have hnat : (6000547191 : ℕ)^35*25000000000000^27 ≤ 12894652307533^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6000547191 10000000000 12894652307533 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4779873721/10000000000 : ℝ)^35 ≤ (38408619400979/100000000000000 : ℝ)^27 := by
    have hnat : (4779873721 : ℕ)^35*100000000000000^27 ≤ 38408619400979^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779873721 10000000000 38408619400979 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1694334019/10000000000 : ℝ)^35 ≤ (1251596419611/12500000000000 : ℝ)^27 := by
    have hnat : (1694334019 : ℕ)^35*12500000000000^27 ≤ 1251596419611^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694334019 10000000000 1251596419611 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6000547191/10000000000 : ℝ), (4779873721/10000000000 : ℝ), (-1694334019/10000000000 : ℝ)] ![(12894652307533/25000000000000 : ℝ), (38408619400979/100000000000000 : ℝ), (1251596419611/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6000547191/10000000000 : ℝ)|^35 ≤ (12894652307533/25000000000000 : ℝ)^27
        have hw : |(6000547191/10000000000 : ℝ)|=(6000547191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4779873721/10000000000 : ℝ)|^35 ≤ (38408619400979/100000000000000 : ℝ)^27
        have hw : |(4779873721/10000000000 : ℝ)|=(4779873721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1694334019/10000000000 : ℝ)|^35 ≤ (1251596419611/12500000000000 : ℝ)^27
        have hw : |(-1694334019/10000000000 : ℝ)|=(1694334019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309054_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((18249/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18249/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77471/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64251/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64251/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-22247/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s2_pow0 : (18249/25000 : ℝ) ^ (69/16 : ℝ) ≤ (12866108556998720743/50000000000000000000 : ℝ) := by
    have hpowers : (18249/25000 : ℝ)^69 ≤ (12866108556998720743/50000000000000000000 : ℝ)^16 := by
      have hnat : (18249 : ℕ)^69*50000000000000000000^16 ≤ 12866108556998720743^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18249 25000 12866108556998720743 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18249/25000 : ℝ)) (X := (12866108556998720743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (62866108556998720743/50000000000000000000 : ℝ) ≤ (2636331894262733/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (62866108556998720743/50000000000000000000 : ℝ)^16 ≤ (2636331894262733/2500000000000000 : ℝ)^69 := by
      have hnat : (62866108556998720743 : ℕ)^16*2500000000000000^69 ≤ 2636331894262733^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62866108556998720743 50000000000000000000 2636331894262733 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2636331894262733/2500000000000000 : ℝ)) (X := (62866108556998720743/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (37866108556998720743/25000000000000000000 : ℝ) ≤ (1101060465344133/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (37866108556998720743/25000000000000000000 : ℝ)^16 ≤ (1101060465344133/1000000000000000 : ℝ)^69 := by
      have hnat : (37866108556998720743 : ℕ)^16*1000000000000000^69 ≤ 1101060465344133^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37866108556998720743 25000000000000000000 1101060465344133 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1101060465344133/1000000000000000 : ℝ)) (X := (37866108556998720743/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(136331894262733/1824900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(232638538195199/3649800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (18249/25000 : ℝ)) (alpha := (136331894262733/1824900000000000 : ℝ)) (beta := (232638538195199/3649800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18249/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(136331894262733/1824900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(232638538195199/3649800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (77471/100000 : ℝ) ^ (69/16 : ℝ) ≤ (16629632049131667469/50000000000000000000 : ℝ) := by
    have hpowers : (77471/100000 : ℝ)^69 ≤ (16629632049131667469/50000000000000000000 : ℝ)^16 := by
      have hnat : (77471 : ℕ)^69*50000000000000000000^16 ≤ 16629632049131667469^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77471 100000 16629632049131667469 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77471/100000 : ℝ)) (X := (16629632049131667469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (66629632049131667469/50000000000000000000 : ℝ) ≤ (1068846505259901/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (66629632049131667469/50000000000000000000 : ℝ)^16 ≤ (1068846505259901/1000000000000000 : ℝ)^69 := by
      have hnat : (66629632049131667469 : ℕ)^16*1000000000000000^69 ≤ 1068846505259901^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66629632049131667469 50000000000000000000 1068846505259901 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1068846505259901/1000000000000000 : ℝ)) (X := (66629632049131667469/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (41629632049131667469/25000000000000000000 : ℝ) ≤ (11255210918890529/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (41629632049131667469/25000000000000000000 : ℝ)^16 ≤ (11255210918890529/10000000000000000 : ℝ)^69 := by
      have hnat : (41629632049131667469 : ℕ)^16*10000000000000000^69 ≤ 11255210918890529^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41629632049131667469 25000000000000000000 11255210918890529 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11255210918890529/10000000000000000 : ℝ)) (X := (41629632049131667469/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(68846505259901/774710000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(566745866291519/7747100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (77471/100000 : ℝ)) (alpha := (68846505259901/774710000000000 : ℝ)) (beta := (566745866291519/7747100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (77471/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(68846505259901/774710000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(566745866291519/7747100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (64251/100000 : ℝ) ^ (69/16 : ℝ) ≤ (7420822367488251249/50000000000000000000 : ℝ) := by
    have hpowers : (64251/100000 : ℝ)^69 ≤ (7420822367488251249/50000000000000000000 : ℝ)^16 := by
      have hnat : (64251 : ℕ)^69*50000000000000000000^16 ≤ 7420822367488251249^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64251 100000 7420822367488251249 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64251/100000 : ℝ)) (X := (7420822367488251249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (57420822367488251249/50000000000000000000 : ℝ) ≤ (10326094462250849/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (57420822367488251249/50000000000000000000 : ℝ)^16 ≤ (10326094462250849/10000000000000000 : ℝ)^69 := by
      have hnat : (57420822367488251249 : ℕ)^16*10000000000000000^69 ≤ 10326094462250849^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57420822367488251249 50000000000000000000 10326094462250849 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10326094462250849/10000000000000000 : ℝ)) (X := (57420822367488251249/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (32420822367488251249/25000000000000000000 : ℝ) ≤ (10621259120299861/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (32420822367488251249/25000000000000000000 : ℝ)^16 ≤ (10621259120299861/10000000000000000 : ℝ)^69 := by
      have hnat : (32420822367488251249 : ℕ)^16*10000000000000000^69 ≤ 10621259120299861^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32420822367488251249 25000000000000000000 10621259120299861 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10621259120299861/10000000000000000 : ℝ)) (X := (32420822367488251249/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(326094462250849/6425100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(73791164512253/1606275000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (64251/100000 : ℝ)) (alpha := (326094462250849/6425100000000000 : ℝ)) (beta := (73791164512253/1606275000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64251/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(326094462250849/6425100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(73791164512253/1606275000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((5706139737/10000000000 : ℝ)*X 1 0+(-2094824731/10000000000 : ℝ)*X 1 1+(-1197039809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5331953777/10000000000 : ℝ)*X 0 0+(2636663259/5000000000 : ℝ)*X 0 1+(-981618303/5000000000 : ℝ)*X 0 2+(5331953777/10000000000 : ℝ)*X 1 0+(2636663259/5000000000 : ℝ)*X 1 1+(-981618303/5000000000 : ℝ)*X 1 2+(5331953777/10000000000 : ℝ)*X 2 0+(2636663259/5000000000 : ℝ)*X 2 1+(-981618303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-209050553/5000000000 : ℝ)*X 0 0+(3812590371/10000000000 : ℝ)*X 0 1+(-7570888723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((637313843/1250000000 : ℝ)*X 1 0+(-221576267/2500000000 : ℝ)*X 1 1+(-1552343157/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((36016017/78125000 : ℝ)*X 2 0+(3416757867/5000000000 : ℝ)*X 2 1+(545830697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4811157607/10000000000 : ℝ)*X 0 0+(3325886677/5000000000 : ℝ)*X 0 1+(-109549511/2000000000 : ℝ)*X 0 2+(4811157607/10000000000 : ℝ)*X 1 0+(3325886677/5000000000 : ℝ)*X 1 1+(-109549511/2000000000 : ℝ)*X 1 2+(4811157607/10000000000 : ℝ)*X 2 0+(3325886677/5000000000 : ℝ)*X 2 1+(-109549511/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-3213793/10000000000 : ℝ)*X 0 0+(422432007/1000000000 : ℝ)*X 0 1+(-3682648859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4755531723/10000000000 : ℝ)*X 1 0+(-287724093/2000000000 : ℝ)*X 1 1+(-387130789/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3443153869/5000000000 : ℝ)*X 2 0+(903059103/2000000000 : ℝ)*X 2 1+(610720339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1605774899/2500000000 : ℝ)*X 0 0+(1186119791/2500000000 : ℝ)*X 0 1+(-108586157/1000000000 : ℝ)*X 0 2+(1605774899/2500000000 : ℝ)*X 1 0+(1186119791/2500000000 : ℝ)*X 1 1+(-108586157/1000000000 : ℝ)*X 1 2+(1605774899/2500000000 : ℝ)*X 2 0+(1186119791/2500000000 : ℝ)*X 2 1+(-108586157/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((352961/5000000000 : ℝ)*X 0 0+(5432275239/10000000000 : ℝ)*X 0 1+(-3137714739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3325229187/5000000000 : ℝ)*X 1 0+(-264166381/2000000000 : ℝ)*X 1 1+(-866526499/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((5183405229/10000000000 : ℝ)*X 2 0+(1410556663/2500000000 : ℝ)*X 2 1+(103455067/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6000547191/10000000000 : ℝ)*X 0 0+(4779873721/10000000000 : ℝ)*X 0 1+(-1694334019/10000000000 : ℝ)*X 0 2+(6000547191/10000000000 : ℝ)*X 1 0+(4779873721/10000000000 : ℝ)*X 1 1+(-1694334019/10000000000 : ℝ)*X 1 2+(6000547191/10000000000 : ℝ)*X 2 0+(4779873721/10000000000 : ℝ)*X 2 1+(-1694334019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((6871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6843235293928758732954511/592180050000000000000000000000 : ℝ) := by norm_num
    linear_combination (9279781/500000000000 : ℝ)*(base23) + (22234872009/125000000000 : ℝ)*(base39) + (374699422937/1000000000000 : ℝ)*(base60) + (1782005779541/500000000000 : ℝ)*(major_s2_0) + (1782005779541/500000000000 : ℝ)*(major_s2_1) + (1782005779541/500000000000 : ℝ)*(major_s2_2) + (27569617/1000000000000 : ℝ)*(sp_s2_6) + (2444966600381/500000000000 : ℝ)*(sp_s2_7) + (977978829533/200000000000 : ℝ)*(sp_s2_8) + (488992551481/100000000000 : ℝ)*(sp_s2_9) + (13987577691/6250000000 : ℝ)*(sp_s2_13) + (23032611/500000000000 : ℝ)*(sp_s2_14) + (85118319/1000000000000 : ℝ)*(sp_s2_15) + (8797903/250000000000 : ℝ)*(sp_s2_23) + (2238040000177/1000000000000 : ℝ)*(f.failure) + (76405926031/15625000000 : ℝ)*(f.sum) + (188480276091745397/124439730525000000000000000000000 : ℝ)*base63 + (32554669560763/803137500000000000000000000 : ℝ)*base65 + (638586430388741/3873550000000000000000000000 : ℝ)*base67 + (411646564445821/3212550000000000000000000000 : ℝ)*base68 + (120773830022514701/888270075000000000000000000000 : ℝ)*base71 + (226543046374879/1824900000000000000000000000 : ℝ)*base73 + (25215087566909/154942000000000000000000000 : ℝ)*base74 + (44820480310103/912450000000000000000000000 : ℝ)*base77 + (6374012185996391833/141376827900000000000000000000000 : ℝ)*base78 + (13281/100000000000000000 : ℝ)*base86 + (13281/100000000000000000 : ℝ)*base88 + (13281/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29277/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80028034482147180454376687117/3823065054462500000000000000000000 : ℝ) := by norm_num
    linear_combination (48797843/781250000 : ℝ)*(base7) + (10755696433/125000000000 : ℝ)*(base39) + (41314755023/1000000000000 : ℝ)*(base60) + (950682503501/250000000000 : ℝ)*(major_s2_0) + (950682503501/250000000000 : ℝ)*(major_s2_1) + (950682503501/250000000000 : ℝ)*(major_s2_2) + (15438509/1000000000000 : ℝ)*(sp_s2_1) + (5901921/31250000000 : ℝ)*(sp_s2_8) + (1035893597581/200000000000 : ℝ)*(sp_s2_14) + (1035855315231/200000000000 : ℝ)*(sp_s2_15) + (647435109517/125000000000 : ℝ)*(sp_s2_16) + (2450382073279/1000000000000 : ℝ)*(sp_s2_20) + (12888231/1000000000000 : ℝ)*(sp_s2_21) + (11844211/500000000000 : ℝ)*(sp_s2_27) + (1193972261331/500000000000 : ℝ)*(f.failure) + (647435109517/125000000000 : ℝ)*(f.sum) + (178763185647192652463/248879461050000000000000000000000 : ℝ)*base63 + (1248834431407889/3212550000000000000000000000 : ℝ)*base65 + (617303861801579/1936775000000000000000000000 : ℝ)*base66 + (1451619095819219/1606275000000000000000000000 : ℝ)*base69 + (183501709655522527/888270075000000000000000000000 : ℝ)*base71 + (157930717024841/912450000000000000000000000 : ℝ)*base72 + (52763673875797/77471000000000000000000000 : ℝ)*base75 + (70437030293657/114056250000000000000000000 : ℝ)*base77 + (865027191419187647/70688413950000000000000000000000 : ℝ)*base79 + (22243/50000000000000000 : ℝ)*base86 + (22243/50000000000000000 : ℝ)*base88 + (22243/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-22247/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (78000690518235679563641/7402250625000000000000000000 : ℝ) := by norm_num
    linear_combination (3209798841/250000000000 : ℝ)*(base7) + (498403/125000000000 : ℝ)*(base15) + (540725484387/1000000000000 : ℝ)*(base39) + (595619/250000000000 : ℝ)*(base60) + (4181893873601/1000000000000 : ℝ)*(major_s2_0) + (4181893873601/1000000000000 : ℝ)*(major_s2_1) + (4181893873601/1000000000000 : ℝ)*(major_s2_2) + (31478531/1000000000000 : ℝ)*(sp_s2_9) + (1352159/250000000000 : ℝ)*(sp_s2_16) + (78036777/1000000000000 : ℝ)*(sp_s2_20) + (143248124809/25000000000 : ℝ)*(sp_s2_21) + (358120062821/62500000000 : ℝ)*(sp_s2_22) + (716236013149/125000000000 : ℝ)*(sp_s2_23) + (105552145681/40000000000 : ℝ)*(sp_s2_27) + (1313021241719/500000000000 : ℝ)*(f.failure) + (143248124809/25000000000 : ℝ)*(f.sum) + (196554827620812214481/497758922100000000000000000000000 : ℝ)*base62 + (775205870272391/3212550000000000000000000000 : ℝ)*base65 + (371722295383969/7747100000000000000000000000 : ℝ)*base66 + (3049632302257561/6425100000000000000000000000 : ℝ)*base68 + (533827073079422797/3553080300000000000000000000000 : ℝ)*base71 + (882762288987101/3649800000000000000000000000 : ℝ)*base72 + (49490385162639/96838750000000000000000000 : ℝ)*base75 + (1018631968813343/1824900000000000000000000000 : ℝ)*base77 + (25461659467799123867/282753655800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (24407/50000000000000000 : ℝ)*base86 + (24407/50000000000000000 : ℝ)*base88 + (24407/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((18249/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18249/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77471/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64251/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64251/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-22247/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309054_s2 p hpa hpb X hX hprev1

#print axioms solution

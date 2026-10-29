-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:17.320686+00:00
-- url     : https://prove2.me/submissions/91e8b4a0-9c44-4138-b4fc-66bb87b33992

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
theorem collision_support_c315054_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-14765189/250000000 : ℝ)*x 0 + (2282605681/5000000000 : ℝ)*x 1 + (-83717807/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14765189/250000000 : ℝ)^19 ≤ (347180572751/12500000000000 : ℝ)^15 := by
    have hnat : (14765189 : ℕ)^19*12500000000000^15 ≤ 347180572751^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14765189 250000000 347180572751 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282605681/5000000000 : ℝ)^19 ≤ (18519125053389/50000000000000 : ℝ)^15 := by
    have hnat : (2282605681 : ℕ)^19*50000000000000^15 ≤ 18519125053389^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282605681 5000000000 18519125053389 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83717807/125000000 : ℝ)^19 ≤ (60184305294033/100000000000000 : ℝ)^15 := by
    have hnat : (83717807 : ℕ)^19*100000000000000^15 ≤ 60184305294033^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83717807 125000000 60184305294033 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14765189/250000000 : ℝ), (2282605681/5000000000 : ℝ), (-83717807/125000000 : ℝ)] ![(347180572751/12500000000000 : ℝ), (18519125053389/50000000000000 : ℝ), (60184305294033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14765189/250000000 : ℝ)|^19 ≤ (347180572751/12500000000000 : ℝ)^15
        have hw : |(-14765189/250000000 : ℝ)|=(14765189/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282605681/5000000000 : ℝ)|^19 ≤ (18519125053389/50000000000000 : ℝ)^15
        have hw : |(2282605681/5000000000 : ℝ)|=(2282605681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83717807/125000000 : ℝ)|^19 ≤ (60184305294033/100000000000000 : ℝ)^15
        have hw : |(-83717807/125000000 : ℝ)|=(83717807/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (228672249/400000000 : ℝ)*x 0 + (-1819864051/10000000000 : ℝ)*x 1 + (-4774090143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228672249/400000000 : ℝ)^19 ≤ (24624328822147/50000000000000 : ℝ)^15 := by
    have hnat : (228672249 : ℕ)^19*50000000000000^15 ≤ 24624328822147^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228672249 400000000 24624328822147 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1819864051/10000000000 : ℝ)^19 ≤ (11553564639943/100000000000000 : ℝ)^15 := by
    have hnat : (1819864051 : ℕ)^19*100000000000000^15 ≤ 11553564639943^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819864051 10000000000 11553564639943 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774090143/10000000000 : ℝ)^19 ≤ (39197777703507/100000000000000 : ℝ)^15 := by
    have hnat : (4774090143 : ℕ)^19*100000000000000^15 ≤ 39197777703507^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774090143 10000000000 39197777703507 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228672249/400000000 : ℝ), (-1819864051/10000000000 : ℝ), (-4774090143/10000000000 : ℝ)] ![(24624328822147/50000000000000 : ℝ), (11553564639943/100000000000000 : ℝ), (39197777703507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228672249/400000000 : ℝ)|^19 ≤ (24624328822147/50000000000000 : ℝ)^15
        have hw : |(228672249/400000000 : ℝ)|=(228672249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1819864051/10000000000 : ℝ)|^19 ≤ (11553564639943/100000000000000 : ℝ)^15
        have hw : |(-1819864051/10000000000 : ℝ)|=(1819864051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4774090143/10000000000 : ℝ)|^19 ≤ (39197777703507/100000000000000 : ℝ)^15
        have hw : |(-4774090143/10000000000 : ℝ)|=(4774090143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2673604723/5000000000 : ℝ)*x 0 + (5287845501/10000000000 : ℝ)*x 1 + (1640863209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673604723/5000000000 : ℝ)^19 ≤ (5656369786987/12500000000000 : ℝ)^15 := by
    have hnat : (2673604723 : ℕ)^19*12500000000000^15 ≤ 5656369786987^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673604723 5000000000 5656369786987 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5287845501/10000000000 : ℝ)^19 ≤ (8923113597511/20000000000000 : ℝ)^15 := by
    have hnat : (5287845501 : ℕ)^19*20000000000000^15 ≤ 8923113597511^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287845501 10000000000 8923113597511 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1640863209/10000000000 : ℝ)^19 ≤ (10133473703107/100000000000000 : ℝ)^15 := by
    have hnat : (1640863209 : ℕ)^19*100000000000000^15 ≤ 10133473703107^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640863209 10000000000 10133473703107 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673604723/5000000000 : ℝ), (5287845501/10000000000 : ℝ), (1640863209/10000000000 : ℝ)] ![(5656369786987/12500000000000 : ℝ), (8923113597511/20000000000000 : ℝ), (10133473703107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673604723/5000000000 : ℝ)|^19 ≤ (5656369786987/12500000000000 : ℝ)^15
        have hw : |(2673604723/5000000000 : ℝ)|=(2673604723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5287845501/10000000000 : ℝ)|^19 ≤ (8923113597511/20000000000000 : ℝ)^15
        have hw : |(5287845501/10000000000 : ℝ)|=(5287845501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1640863209/10000000000 : ℝ)|^19 ≤ (10133473703107/100000000000000 : ℝ)^15
        have hw : |(1640863209/10000000000 : ℝ)|=(1640863209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1068220841/2000000000 : ℝ)*x 0 + (2647326671/5000000000 : ℝ)*x 1 + (-1639925227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068220841/2000000000 : ℝ)^19 ≤ (9037104975751/20000000000000 : ℝ)^15 := by
    have hnat : (1068220841 : ℕ)^19*20000000000000^15 ≤ 9037104975751^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068220841 2000000000 9037104975751 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2647326671/5000000000 : ℝ)^19 ≤ (44688338249101/100000000000000 : ℝ)^15 := by
    have hnat : (2647326671 : ℕ)^19*100000000000000^15 ≤ 44688338249101^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647326671 5000000000 44688338249101 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639925227/10000000000 : ℝ)^19 ≤ (10126136851989/100000000000000 : ℝ)^15 := by
    have hnat : (1639925227 : ℕ)^19*100000000000000^15 ≤ 10126136851989^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639925227 10000000000 10126136851989 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068220841/2000000000 : ℝ), (2647326671/5000000000 : ℝ), (-1639925227/10000000000 : ℝ)] ![(9037104975751/20000000000000 : ℝ), (44688338249101/100000000000000 : ℝ), (10126136851989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068220841/2000000000 : ℝ)|^19 ≤ (9037104975751/20000000000000 : ℝ)^15
        have hw : |(1068220841/2000000000 : ℝ)|=(1068220841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2647326671/5000000000 : ℝ)|^19 ≤ (44688338249101/100000000000000 : ℝ)^15
        have hw : |(2647326671/5000000000 : ℝ)|=(2647326671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1639925227/10000000000 : ℝ)|^19 ≤ (10126136851989/100000000000000 : ℝ)^15
        have hw : |(-1639925227/10000000000 : ℝ)|=(1639925227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-751641/15625000 : ℝ)*x 0 + (451293303/1250000000 : ℝ)*x 1 + (-1515019891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751641/15625000 : ℝ)^19 ≤ (2141778486171/100000000000000 : ℝ)^15 := by
    have hnat : (751641 : ℕ)^19*100000000000000^15 ≤ 2141778486171^15*15625000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751641 15625000 2141778486171 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451293303/1250000000 : ℝ)^19 ≤ (27514518008453/100000000000000 : ℝ)^15 := by
    have hnat : (451293303 : ℕ)^19*100000000000000^15 ≤ 27514518008453^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451293303 1250000000 27514518008453 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1515019891/2000000000 : ℝ)^19 ≤ (4396481468717/6250000000000 : ℝ)^15 := by
    have hnat : (1515019891 : ℕ)^19*6250000000000^15 ≤ 4396481468717^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515019891 2000000000 4396481468717 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-751641/15625000 : ℝ), (451293303/1250000000 : ℝ), (-1515019891/2000000000 : ℝ)] ![(2141778486171/100000000000000 : ℝ), (27514518008453/100000000000000 : ℝ), (4396481468717/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-751641/15625000 : ℝ)|^19 ≤ (2141778486171/100000000000000 : ℝ)^15
        have hw : |(-751641/15625000 : ℝ)|=(751641/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451293303/1250000000 : ℝ)|^19 ≤ (27514518008453/100000000000000 : ℝ)^15
        have hw : |(451293303/1250000000 : ℝ)|=(451293303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1515019891/2000000000 : ℝ)|^19 ≤ (4396481468717/6250000000000 : ℝ)^15
        have hw : |(-1515019891/2000000000 : ℝ)|=(1515019891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4895422057/10000000000 : ℝ)*x 0 + (-735300337/10000000000 : ℝ)*x 1 + (-6315462383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4895422057/10000000000 : ℝ)^19 ≤ (809277575739/2000000000000 : ℝ)^15 := by
    have hnat : (4895422057 : ℕ)^19*2000000000000^15 ≤ 809277575739^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895422057 10000000000 809277575739 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735300337/10000000000 : ℝ)^19 ≤ (3665968275517/100000000000000 : ℝ)^15 := by
    have hnat : (735300337 : ℕ)^19*100000000000000^15 ≤ 3665968275517^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735300337 10000000000 3665968275517 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6315462383/10000000000 : ℝ)^19 ≤ (55870152921151/100000000000000 : ℝ)^15 := by
    have hnat : (6315462383 : ℕ)^19*100000000000000^15 ≤ 55870152921151^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6315462383 10000000000 55870152921151 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4895422057/10000000000 : ℝ), (-735300337/10000000000 : ℝ), (-6315462383/10000000000 : ℝ)] ![(809277575739/2000000000000 : ℝ), (3665968275517/100000000000000 : ℝ), (55870152921151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4895422057/10000000000 : ℝ)|^19 ≤ (809277575739/2000000000000 : ℝ)^15
        have hw : |(4895422057/10000000000 : ℝ)|=(4895422057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735300337/10000000000 : ℝ)|^19 ≤ (3665968275517/100000000000000 : ℝ)^15
        have hw : |(-735300337/10000000000 : ℝ)|=(735300337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6315462383/10000000000 : ℝ)|^19 ≤ (55870152921151/100000000000000 : ℝ)^15
        have hw : |(-6315462383/10000000000 : ℝ)|=(6315462383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (13617061/31250000 : ℝ)*x 0 + (6939500057/10000000000 : ℝ)*x 1 + (479093471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13617061/31250000 : ℝ)^19 ≤ (17458178461209/50000000000000 : ℝ)^15 := by
    have hnat : (13617061 : ℕ)^19*50000000000000^15 ≤ 17458178461209^15*31250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13617061 31250000 17458178461209 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6939500057/10000000000 : ℝ)^19 ≤ (62952893928813/100000000000000 : ℝ)^15 := by
    have hnat : (6939500057 : ℕ)^19*100000000000000^15 ≤ 62952893928813^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6939500057 10000000000 62952893928813 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479093471/10000000000 : ℝ)^19 ≤ (426149825933/20000000000000 : ℝ)^15 := by
    have hnat : (479093471 : ℕ)^19*20000000000000^15 ≤ 426149825933^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479093471 10000000000 426149825933 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13617061/31250000 : ℝ), (6939500057/10000000000 : ℝ), (479093471/10000000000 : ℝ)] ![(17458178461209/50000000000000 : ℝ), (62952893928813/100000000000000 : ℝ), (426149825933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13617061/31250000 : ℝ)|^19 ≤ (17458178461209/50000000000000 : ℝ)^15
        have hw : |(13617061/31250000 : ℝ)|=(13617061/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6939500057/10000000000 : ℝ)|^19 ≤ (62952893928813/100000000000000 : ℝ)^15
        have hw : |(6939500057/10000000000 : ℝ)|=(6939500057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(479093471/10000000000 : ℝ)|^19 ≤ (426149825933/20000000000000 : ℝ)^15
        have hw : |(479093471/10000000000 : ℝ)|=(479093471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (917667283/2000000000 : ℝ)*x 0 + (211354923/312500000 : ℝ)*x 1 + (-16687179/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (917667283/2000000000 : ℝ)^19 ≤ (37276058681591/100000000000000 : ℝ)^15 := by
    have hnat : (917667283 : ℕ)^19*100000000000000^15 ≤ 37276058681591^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917667283 2000000000 37276058681591 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211354923/312500000 : ℝ)^19 ≤ (15233942574731/25000000000000 : ℝ)^15 := by
    have hnat : (211354923 : ℕ)^19*25000000000000^15 ≤ 15233942574731^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211354923 312500000 15233942574731 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16687179/400000000 : ℝ)^19 ≤ (1788171005809/100000000000000 : ℝ)^15 := by
    have hnat : (16687179 : ℕ)^19*100000000000000^15 ≤ 1788171005809^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16687179 400000000 1788171005809 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(917667283/2000000000 : ℝ), (211354923/312500000 : ℝ), (-16687179/400000000 : ℝ)] ![(37276058681591/100000000000000 : ℝ), (15233942574731/25000000000000 : ℝ), (1788171005809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(917667283/2000000000 : ℝ)|^19 ≤ (37276058681591/100000000000000 : ℝ)^15
        have hw : |(917667283/2000000000 : ℝ)|=(917667283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211354923/312500000 : ℝ)|^19 ≤ (15233942574731/25000000000000 : ℝ)^15
        have hw : |(211354923/312500000 : ℝ)|=(211354923/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16687179/400000000 : ℝ)|^19 ≤ (1788171005809/100000000000000 : ℝ)^15
        have hw : |(-16687179/400000000 : ℝ)|=(16687179/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151053/2000000000 : ℝ)*x 0 + (1937748337/5000000000 : ℝ)*x 1 + (-470998873/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151053/2000000000 : ℝ)^19 ≤ (17380145703/100000000000000 : ℝ)^15 := by
    have hnat : (2151053 : ℕ)^19*100000000000000^15 ≤ 17380145703^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151053 2000000000 17380145703 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937748337/5000000000 : ℝ)^19 ≤ (7524679536453/25000000000000 : ℝ)^15 := by
    have hnat : (1937748337 : ℕ)^19*25000000000000^15 ≤ 7524679536453^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937748337 5000000000 7524679536453 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470998873/625000000 : ℝ)^19 ≤ (34941950846097/50000000000000 : ℝ)^15 := by
    have hnat : (470998873 : ℕ)^19*50000000000000^15 ≤ 34941950846097^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470998873 625000000 34941950846097 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151053/2000000000 : ℝ), (1937748337/5000000000 : ℝ), (-470998873/625000000 : ℝ)] ![(17380145703/100000000000000 : ℝ), (7524679536453/25000000000000 : ℝ), (34941950846097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151053/2000000000 : ℝ)|^19 ≤ (17380145703/100000000000000 : ℝ)^15
        have hw : |(-2151053/2000000000 : ℝ)|=(2151053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1937748337/5000000000 : ℝ)|^19 ≤ (7524679536453/25000000000000 : ℝ)^15
        have hw : |(1937748337/5000000000 : ℝ)|=(1937748337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470998873/625000000 : ℝ)|^19 ≤ (34941950846097/50000000000000 : ℝ)^15
        have hw : |(-470998873/625000000 : ℝ)|=(470998873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (206355023/500000000 : ℝ)*x 0 + (-390603297/2500000000 : ℝ)*x 1 + (-6494267451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206355023/500000000 : ℝ)^19 ≤ (651899098071/2000000000000 : ℝ)^15 := by
    have hnat : (206355023 : ℕ)^19*2000000000000^15 ≤ 651899098071^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206355023 500000000 651899098071 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390603297/2500000000 : ℝ)^19 ≤ (9523753255569/100000000000000 : ℝ)^15 := by
    have hnat : (390603297 : ℕ)^19*100000000000000^15 ≤ 9523753255569^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390603297 2500000000 9523753255569 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6494267451/10000000000 : ℝ)^19 ≤ (28940645914169/50000000000000 : ℝ)^15 := by
    have hnat : (6494267451 : ℕ)^19*50000000000000^15 ≤ 28940645914169^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6494267451 10000000000 28940645914169 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206355023/500000000 : ℝ), (-390603297/2500000000 : ℝ), (-6494267451/10000000000 : ℝ)] ![(651899098071/2000000000000 : ℝ), (9523753255569/100000000000000 : ℝ), (28940645914169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206355023/500000000 : ℝ)|^19 ≤ (651899098071/2000000000000 : ℝ)^15
        have hw : |(206355023/500000000 : ℝ)|=(206355023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390603297/2500000000 : ℝ)|^19 ≤ (9523753255569/100000000000000 : ℝ)^15
        have hw : |(-390603297/2500000000 : ℝ)|=(390603297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6494267451/10000000000 : ℝ)|^19 ≤ (28940645914169/50000000000000 : ℝ)^15
        have hw : |(-6494267451/10000000000 : ℝ)|=(6494267451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7155236931/10000000000 : ℝ)*x 0 + (4052785441/10000000000 : ℝ)*x 1 + (578346191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7155236931/10000000000 : ℝ)^19 ≤ (65442079463799/100000000000000 : ℝ)^15 := by
    have hnat : (7155236931 : ℕ)^19*100000000000000^15 ≤ 65442079463799^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7155236931 10000000000 65442079463799 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4052785441/10000000000 : ℝ)^19 ≤ (15926655270309/50000000000000 : ℝ)^15 := by
    have hnat : (4052785441 : ℕ)^19*50000000000000^15 ≤ 15926655270309^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052785441 10000000000 15926655270309 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578346191/10000000000 : ℝ)^19 ≤ (2704609988201/100000000000000 : ℝ)^15 := by
    have hnat : (578346191 : ℕ)^19*100000000000000^15 ≤ 2704609988201^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578346191 10000000000 2704609988201 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7155236931/10000000000 : ℝ), (4052785441/10000000000 : ℝ), (578346191/10000000000 : ℝ)] ![(65442079463799/100000000000000 : ℝ), (15926655270309/50000000000000 : ℝ), (2704609988201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7155236931/10000000000 : ℝ)|^19 ≤ (65442079463799/100000000000000 : ℝ)^15
        have hw : |(7155236931/10000000000 : ℝ)|=(7155236931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4052785441/10000000000 : ℝ)|^19 ≤ (15926655270309/50000000000000 : ℝ)^15
        have hw : |(4052785441/10000000000 : ℝ)|=(4052785441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578346191/10000000000 : ℝ)|^19 ≤ (2704609988201/100000000000000 : ℝ)^15
        have hw : |(578346191/10000000000 : ℝ)|=(578346191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6725513353/10000000000 : ℝ)*x 0 + (2147058873/5000000000 : ℝ)*x 1 + (-6075563/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6725513353/10000000000 : ℝ)^19 ≤ (12100840932153/20000000000000 : ℝ)^15 := by
    have hnat : (6725513353 : ℕ)^19*20000000000000^15 ≤ 12100840932153^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6725513353 10000000000 12100840932153 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147058873/5000000000 : ℝ)^19 ≤ (34274700492057/100000000000000 : ℝ)^15 := by
    have hnat : (2147058873 : ℕ)^19*100000000000000^15 ≤ 34274700492057^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147058873 5000000000 34274700492057 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6075563/62500000 : ℝ)^19 ≤ (5221094825379/100000000000000 : ℝ)^15 := by
    have hnat : (6075563 : ℕ)^19*100000000000000^15 ≤ 5221094825379^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6075563 62500000 5221094825379 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6725513353/10000000000 : ℝ), (2147058873/5000000000 : ℝ), (-6075563/62500000 : ℝ)] ![(12100840932153/20000000000000 : ℝ), (34274700492057/100000000000000 : ℝ), (5221094825379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6725513353/10000000000 : ℝ)|^19 ≤ (12100840932153/20000000000000 : ℝ)^15
        have hw : |(6725513353/10000000000 : ℝ)|=(6725513353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2147058873/5000000000 : ℝ)|^19 ≤ (34274700492057/100000000000000 : ℝ)^15
        have hw : |(2147058873/5000000000 : ℝ)|=(2147058873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6075563/62500000 : ℝ)|^19 ≤ (5221094825379/100000000000000 : ℝ)^15
        have hw : |(-6075563/62500000 : ℝ)|=(6075563/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (337/625000000 : ℝ)*x 0 + (5544787217/10000000000 : ℝ)*x 1 + (-1204734297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337/625000000 : ℝ)^19 ≤ (1148727/100000000000000 : ℝ)^15 := by
    have hnat : (337 : ℕ)^19*100000000000000^15 ≤ 1148727^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337 625000000 1148727 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5544787217/10000000000 : ℝ)^19 ≤ (23689588934803/50000000000000 : ℝ)^15 := by
    have hnat : (5544787217 : ℕ)^19*50000000000000^15 ≤ 23689588934803^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544787217 10000000000 23689588934803 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204734297/2000000000 : ℝ)^19 ≤ (26310410486673/50000000000000 : ℝ)^15 := by
    have hnat : (1204734297 : ℕ)^19*50000000000000^15 ≤ 26310410486673^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204734297 2000000000 26310410486673 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337/625000000 : ℝ), (5544787217/10000000000 : ℝ), (-1204734297/2000000000 : ℝ)] ![(1148727/100000000000000 : ℝ), (23689588934803/50000000000000 : ℝ), (26310410486673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337/625000000 : ℝ)|^19 ≤ (1148727/100000000000000 : ℝ)^15
        have hw : |(337/625000000 : ℝ)|=(337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5544787217/10000000000 : ℝ)|^19 ≤ (23689588934803/50000000000000 : ℝ)^15
        have hw : |(5544787217/10000000000 : ℝ)|=(5544787217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1204734297/2000000000 : ℝ)|^19 ≤ (26310410486673/50000000000000 : ℝ)^15
        have hw : |(-1204734297/2000000000 : ℝ)|=(1204734297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (274701317/400000000 : ℝ)*x 0 + (-1407299327/10000000000 : ℝ)*x 1 + (-3817625149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274701317/400000000 : ℝ)^19 ≤ (3106354058907/5000000000000 : ℝ)^15 := by
    have hnat : (274701317 : ℕ)^19*5000000000000^15 ≤ 3106354058907^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274701317 400000000 3106354058907 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407299327/10000000000 : ℝ)^19 ≤ (8342371797603/100000000000000 : ℝ)^15 := by
    have hnat : (1407299327 : ℕ)^19*100000000000000^15 ≤ 8342371797603^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407299327 10000000000 8342371797603 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3817625149/10000000000 : ℝ)^19 ≤ (29530547012841/100000000000000 : ℝ)^15 := by
    have hnat : (3817625149 : ℕ)^19*100000000000000^15 ≤ 29530547012841^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3817625149 10000000000 29530547012841 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(274701317/400000000 : ℝ), (-1407299327/10000000000 : ℝ), (-3817625149/10000000000 : ℝ)] ![(3106354058907/5000000000000 : ℝ), (8342371797603/100000000000000 : ℝ), (29530547012841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(274701317/400000000 : ℝ)|^19 ≤ (3106354058907/5000000000000 : ℝ)^15
        have hw : |(274701317/400000000 : ℝ)|=(274701317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1407299327/10000000000 : ℝ)|^19 ≤ (8342371797603/100000000000000 : ℝ)^15
        have hw : |(-1407299327/10000000000 : ℝ)|=(1407299327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3817625149/10000000000 : ℝ)|^19 ≤ (29530547012841/100000000000000 : ℝ)^15
        have hw : |(-3817625149/10000000000 : ℝ)|=(3817625149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (183739153/400000000 : ℝ)*x 0 + (28599347/50000000 : ℝ)*x 1 + (255563519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183739153/400000000 : ℝ)^19 ≤ (933224615757/2500000000000 : ℝ)^15 := by
    have hnat : (183739153 : ℕ)^19*2500000000000^15 ≤ 933224615757^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183739153 400000000 933224615757 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28599347/50000000 : ℝ)^19 ≤ (12320521328427/25000000000000 : ℝ)^15 := by
    have hnat : (28599347 : ℕ)^19*25000000000000^15 ≤ 12320521328427^15*50000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28599347 50000000 12320521328427 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255563519/1250000000 : ℝ)^19 ≤ (6694465020017/50000000000000 : ℝ)^15 := by
    have hnat : (255563519 : ℕ)^19*50000000000000^15 ≤ 6694465020017^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255563519 1250000000 6694465020017 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(183739153/400000000 : ℝ), (28599347/50000000 : ℝ), (255563519/1250000000 : ℝ)] ![(933224615757/2500000000000 : ℝ), (12320521328427/25000000000000 : ℝ), (6694465020017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(183739153/400000000 : ℝ)|^19 ≤ (933224615757/2500000000000 : ℝ)^15
        have hw : |(183739153/400000000 : ℝ)|=(183739153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28599347/50000000 : ℝ)|^19 ≤ (12320521328427/25000000000000 : ℝ)^15
        have hw : |(28599347/50000000 : ℝ)|=(28599347/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(255563519/1250000000 : ℝ)|^19 ≤ (6694465020017/50000000000000 : ℝ)^15
        have hw : |(255563519/1250000000 : ℝ)|=(255563519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315054_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3212488199/5000000000 : ℝ)*x 0 + (2107028627/5000000000 : ℝ)*x 1 + (-1550589673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3212488199/5000000000 : ℝ)^19 ≤ (3568759626579/6250000000000 : ℝ)^15 := by
    have hnat : (3212488199 : ℕ)^19*6250000000000^15 ≤ 3568759626579^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3212488199 5000000000 3568759626579 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107028627/5000000000 : ℝ)^19 ≤ (6693458000193/20000000000000 : ℝ)^15 := by
    have hnat : (2107028627 : ℕ)^19*20000000000000^15 ≤ 6693458000193^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107028627 5000000000 6693458000193 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1550589673/10000000000 : ℝ)^19 ≤ (188651119237/2000000000000 : ℝ)^15 := by
    have hnat : (1550589673 : ℕ)^19*2000000000000^15 ≤ 188651119237^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550589673 10000000000 188651119237 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3212488199/5000000000 : ℝ), (2107028627/5000000000 : ℝ), (-1550589673/10000000000 : ℝ)] ![(3568759626579/6250000000000 : ℝ), (6693458000193/20000000000000 : ℝ), (188651119237/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3212488199/5000000000 : ℝ)|^19 ≤ (3568759626579/6250000000000 : ℝ)^15
        have hw : |(3212488199/5000000000 : ℝ)|=(3212488199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107028627/5000000000 : ℝ)|^19 ≤ (6693458000193/20000000000000 : ℝ)^15
        have hw : |(2107028627/5000000000 : ℝ)|=(2107028627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1550589673/10000000000 : ℝ)|^19 ≤ (188651119237/2000000000000 : ℝ)^15
        have hw : |(-1550589673/10000000000 : ℝ)|=(1550589673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315054_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((15301/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15301/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16011/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16011/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35329/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35329/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28439/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28439/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-45201/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (15301/20000 : ℝ) ^ (75/16 : ℝ) ≤ (28496795699536585119/100000000000000000000 : ℝ) := by
    have hpowers : (15301/20000 : ℝ)^75 ≤ (28496795699536585119/100000000000000000000 : ℝ)^16 := by
      have hnat : (15301 : ℕ)^75*100000000000000000000^16 ≤ 28496795699536585119^16*20000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15301 20000 28496795699536585119 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15301/20000 : ℝ)) (X := (28496795699536585119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (128496795699536585119/100000000000000000000 : ℝ) ≤ (1318682885947487/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (128496795699536585119/100000000000000000000 : ℝ)^16 ≤ (1318682885947487/1250000000000000 : ℝ)^75 := by
      have hnat : (128496795699536585119 : ℕ)^16*1250000000000000^75 ≤ 1318682885947487^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128496795699536585119 100000000000000000000 1318682885947487 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1318682885947487/1250000000000000 : ℝ)) (X := (128496795699536585119/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (78496795699536585119/50000000000000000000 : ℝ) ≤ (11010020913157529/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (78496795699536585119/50000000000000000000 : ℝ)^16 ≤ (11010020913157529/10000000000000000 : ℝ)^75 := by
      have hnat : (78496795699536585119 : ℕ)^16*10000000000000000^75 ≤ 11010020913157529^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78496795699536585119 50000000000000000000 11010020913157529 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11010020913157529/10000000000000000 : ℝ)) (X := (78496795699536585119/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(68682885947487/956312500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(460557825577633/7650500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (15301/20000 : ℝ)) (alpha := (68682885947487/956312500000000 : ℝ)) (beta := (460557825577633/7650500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15301/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(68682885947487/956312500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(460557825577633/7650500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16011/20000 : ℝ) ^ (75/16 : ℝ) ≤ (176239567879812329/500000000000000000 : ℝ) := by
    have hpowers : (16011/20000 : ℝ)^75 ≤ (176239567879812329/500000000000000000 : ℝ)^16 := by
      have hnat : (16011 : ℕ)^75*500000000000000000^16 ≤ 176239567879812329^16*20000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16011 20000 176239567879812329 500000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16011/20000 : ℝ)) (X := (176239567879812329/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (676239567879812329/500000000000000000 : ℝ) ≤ (2133067104194919/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (676239567879812329/500000000000000000 : ℝ)^16 ≤ (2133067104194919/2000000000000000 : ℝ)^75 := by
      have hnat : (676239567879812329 : ℕ)^16*2000000000000000^75 ≤ 2133067104194919^75*500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        676239567879812329 500000000000000000 2133067104194919 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2133067104194919/2000000000000000 : ℝ)) (X := (676239567879812329/500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (426239567879812329/250000000000000000 : ℝ) ≤ (560276325725021/500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (426239567879812329/250000000000000000 : ℝ)^16 ≤ (560276325725021/500000000000000 : ℝ)^75 := by
      have hnat : (426239567879812329 : ℕ)^16*500000000000000^75 ≤ 560276325725021^75*250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        426239567879812329 250000000000000000 560276325725021 500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (560276325725021/500000000000000 : ℝ)) (X := (426239567879812329/250000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(133067104194919/1601100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(21607639741033/320220000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (16011/20000 : ℝ)) (alpha := (133067104194919/1601100000000000 : ℝ)) (beta := (21607639741033/320220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (16011/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(133067104194919/1601100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(21607639741033/320220000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35329/50000 : ℝ) ^ (75/16 : ℝ) ≤ (19631061480575029367/100000000000000000000 : ℝ) := by
    have hpowers : (35329/50000 : ℝ)^75 ≤ (19631061480575029367/100000000000000000000 : ℝ)^16 := by
      have hnat : (35329 : ℕ)^75*100000000000000000000^16 ≤ 19631061480575029367^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35329 50000 19631061480575029367 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35329/50000 : ℝ)) (X := (19631061480575029367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (119631061480575029367/100000000000000000000 : ℝ) ≤ (1298723573688001/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (119631061480575029367/100000000000000000000 : ℝ)^16 ≤ (1298723573688001/1250000000000000 : ℝ)^75 := by
      have hnat : (119631061480575029367 : ℕ)^16*1250000000000000^75 ≤ 1298723573688001^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119631061480575029367 100000000000000000000 1298723573688001 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1298723573688001/1250000000000000 : ℝ)) (X := (119631061480575029367/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (69631061480575029367/50000000000000000000 : ℝ) ≤ (1341511465406797/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (69631061480575029367/50000000000000000000 : ℝ)^16 ≤ (1341511465406797/1250000000000000 : ℝ)^75 := by
      have hnat : (69631061480575029367 : ℕ)^16*1250000000000000^75 ≤ 1341511465406797^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69631061480575029367 50000000000000000000 1341511465406797 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1341511465406797/1250000000000000 : ℝ)) (X := (69631061480575029367/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(48723573688001/883225000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1528138989957/31543750000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (35329/50000 : ℝ)) (alpha := (48723573688001/883225000000000 : ℝ)) (beta := (1528138989957/31543750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35329/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(48723573688001/883225000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1528138989957/31543750000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-14765189/250000000 : ℝ)*X 0 0+(2282605681/5000000000 : ℝ)*X 0 1+(-83717807/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((228672249/400000000 : ℝ)*X 1 0+(-1819864051/10000000000 : ℝ)*X 1 1+(-4774090143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2673604723/5000000000 : ℝ)*X 2 0+(5287845501/10000000000 : ℝ)*X 2 1+(1640863209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1068220841/2000000000 : ℝ)*X 0 0+(2647326671/5000000000 : ℝ)*X 0 1+(-1639925227/10000000000 : ℝ)*X 0 2+(1068220841/2000000000 : ℝ)*X 1 0+(2647326671/5000000000 : ℝ)*X 1 1+(-1639925227/10000000000 : ℝ)*X 1 2+(1068220841/2000000000 : ℝ)*X 2 0+(2647326671/5000000000 : ℝ)*X 2 1+(-1639925227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-751641/15625000 : ℝ)*X 0 0+(451293303/1250000000 : ℝ)*X 0 1+(-1515019891/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4895422057/10000000000 : ℝ)*X 1 0+(-735300337/10000000000 : ℝ)*X 1 1+(-6315462383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((13617061/31250000 : ℝ)*X 2 0+(6939500057/10000000000 : ℝ)*X 2 1+(479093471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((917667283/2000000000 : ℝ)*X 0 0+(211354923/312500000 : ℝ)*X 0 1+(-16687179/400000000 : ℝ)*X 0 2+(917667283/2000000000 : ℝ)*X 1 0+(211354923/312500000 : ℝ)*X 1 1+(-16687179/400000000 : ℝ)*X 1 2+(917667283/2000000000 : ℝ)*X 2 0+(211354923/312500000 : ℝ)*X 2 1+(-16687179/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2151053/2000000000 : ℝ)*X 0 0+(1937748337/5000000000 : ℝ)*X 0 1+(-470998873/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((206355023/500000000 : ℝ)*X 1 0+(-390603297/2500000000 : ℝ)*X 1 1+(-6494267451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7155236931/10000000000 : ℝ)*X 2 0+(4052785441/10000000000 : ℝ)*X 2 1+(578346191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((6725513353/10000000000 : ℝ)*X 0 0+(2147058873/5000000000 : ℝ)*X 0 1+(-6075563/62500000 : ℝ)*X 0 2+(6725513353/10000000000 : ℝ)*X 1 0+(2147058873/5000000000 : ℝ)*X 1 1+(-6075563/62500000 : ℝ)*X 1 2+(6725513353/10000000000 : ℝ)*X 2 0+(2147058873/5000000000 : ℝ)*X 2 1+(-6075563/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((337/625000000 : ℝ)*X 0 0+(5544787217/10000000000 : ℝ)*X 0 1+(-1204734297/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((274701317/400000000 : ℝ)*X 1 0+(-1407299327/10000000000 : ℝ)*X 1 1+(-3817625149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((183739153/400000000 : ℝ)*X 2 0+(28599347/50000000 : ℝ)*X 2 1+(255563519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3212488199/5000000000 : ℝ)*X 0 0+(2107028627/5000000000 : ℝ)*X 0 1+(-1550589673/10000000000 : ℝ)*X 0 2+(3212488199/5000000000 : ℝ)*X 1 0+(2107028627/5000000000 : ℝ)*X 1 1+(-1550589673/10000000000 : ℝ)*X 1 2+(3212488199/5000000000 : ℝ)*X 2 0+(2107028627/5000000000 : ℝ)*X 2 1+(-1550589673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((26977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14160767179177444203429057/742539875000000000000000000000 : ℝ) := by norm_num
    linear_combination (28491157293/100000000000 : ℝ)*(base7) + (136254121621/1000000000000 : ℝ)*(base39) + (153393346191/500000000000 : ℝ)*(base60) + (1507133979949/500000000000 : ℝ)*(major_s1_0) + (1507133979949/500000000000 : ℝ)*(major_s1_1) + (1507133979949/500000000000 : ℝ)*(major_s1_2) + (2468929/200000000000 : ℝ)*(sp_s1_0) + (4136705415761/1000000000000 : ℝ)*(sp_s1_7) + (2068468930337/500000000000 : ℝ)*(sp_s1_8) + (4136945073247/1000000000000 : ℝ)*(sp_s1_9) + (1005356627503/500000000000 : ℝ)*(sp_s1_13) + (234321689/1000000000000 : ℝ)*(sp_s1_14) + (711071/50000000000 : ℝ)*(sp_s1_22) + (438053/62500000000 : ℝ)*(sp_s1_23) + (431450420519/250000000000 : ℝ)*(f.failure) + (827390416419/200000000000 : ℝ)*(f.sum) + (5486484167153251/88383221718750000000000000000 : ℝ)*base62 + (63784740339357/63087500000000000000000000 : ℝ)*base65 + (5911108696549/16011000000000000000000000 : ℝ)*base66 + (370085480615409/441612500000000000000000000 : ℝ)*base69 + (419920892617595753/742539875000000000000000000000 : ℝ)*base71 + (131345636987691/294250000000000000000000000 : ℝ)*base72 + (483567234109981/800550000000000000000000000 : ℝ)*base75 + (188599138760033/294250000000000000000000000 : ℝ)*base77 + (1725602617240867049/4711236750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (21979/25000000000000000 : ℝ)*base86 + (21979/25000000000000000 : ℝ)*base88 + (21979/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28439/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28439/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4816284793108713147315821083/247683457054687500000000000000000 : ℝ) := by norm_num
    linear_combination (504307663441/1000000000000 : ℝ)*(base7) + (26053268473/1000000000000 : ℝ)*(base39) + (2693166183001/1000000000000 : ℝ)*(major_s1_0) + (2693166183001/1000000000000 : ℝ)*(major_s1_1) + (2693166183001/1000000000000 : ℝ)*(major_s1_2) + (16157419/1000000000000 : ℝ)*(sp_s1_1) + (4094447/250000000000 : ℝ)*(sp_s1_2) + (108137497/1000000000000 : ℝ)*(sp_s1_8) + (1775462578031/500000000000 : ℝ)*(sp_s1_14) + (887703364489/250000000000 : ℝ)*(sp_s1_15) + (710184275017/200000000000 : ℝ)*(sp_s1_16) + (409250987089/200000000000 : ℝ)*(sp_s1_20) + (12596811/1000000000000 : ℝ)*(sp_s1_21) + (2361343/250000000000 : ℝ)*(sp_s1_27) + (24093073709/15625000000 : ℝ)*(f.failure) + (3550937752873/1000000000000 : ℝ)*(f.sum) + (109750031764664297/323230068000000000000000000000 : ℝ)*base62 + (15911293763157/36050000000000000000000000 : ℝ)*base64 + (137699196616721/320220000000000000000000000 : ℝ)*base67 + (29852296808389/252350000000000000000000000 : ℝ)*base68 + (222164978911411313/689501312500000000000000000000 : ℝ)*base70 + (4921693973114367/7650500000000000000000000000 : ℝ)*base72 + (1070791017907721/1601100000000000000000000000 : ℝ)*base74 + (1751983399951827/3825250000000000000000000000 : ℝ)*base76 + (12042863846940590353/30623038875000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (2337/3125000000000000 : ℝ)*base87 + (2337/3125000000000000 : ℝ)*base89 + (2337/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-45201/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53004051226153503652535207183/3962935312875000000000000000000000 : ℝ) := by norm_num
    linear_combination (239341325997/500000000000 : ℝ)*(base7) + (491951/250000000000 : ℝ)*(base15) + (251624496291/500000000000 : ℝ)*(base39) + (1508048648903/500000000000 : ℝ)*(major_s1_0) + (1508048648903/500000000000 : ℝ)*(major_s1_1) + (1508048648903/500000000000 : ℝ)*(major_s1_2) + (28940823/500000000000 : ℝ)*(sp_s1_2) + (9712223/500000000000 : ℝ)*(sp_s1_6) + (4579151/200000000000 : ℝ)*(sp_s1_9) + (23837817/250000000000 : ℝ)*(sp_s1_20) + (805363915463/200000000000 : ℝ)*(sp_s1_21) + (4026817609511/1000000000000 : ℝ)*(sp_s1_22) + (2013369399957/500000000000 : ℝ)*(sp_s1_23) + (2205416935193/1000000000000 : ℝ)*(sp_s1_27) + (53964033091/31250000000 : ℝ)*(f.failure) + (805363915463/200000000000 : ℝ)*(f.sum) + (341621993099388859/1131305238000000000000000000000 : ℝ)*base62 + (3669211716959/252350000000000000000000000 : ℝ)*base64 + (33500800001993/160110000000000000000000000 : ℝ)*base66 + (90259698121277/1766450000000000000000000000 : ℝ)*base69 + (4571980926753030059/19306036750000000000000000000000 : ℝ)*base70 + (553223352270651/3825250000000000000000000000 : ℝ)*base72 + (44053297719913/800550000000000000000000000 : ℝ)*base74 + (57281524212487/3825250000000000000000000000 : ℝ)*base76 + (747559119863282143/30623038875000000000000000000000 : ℝ)*base78 + (2781/3125000000000000 : ℝ)*base86 + (2781/3125000000000000 : ℝ)*base88 + (2781/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((15301/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15301/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16011/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16011/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35329/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35329/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28439/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28439/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-45201/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315054_s1 p hpa hpb X hX hprev0

#print axioms solution

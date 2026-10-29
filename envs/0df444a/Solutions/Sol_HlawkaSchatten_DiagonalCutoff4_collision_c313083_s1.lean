-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:35:37.793833+00:00
-- url     : https://prove2.me/submissions/41437335-de86-4ec1-981e-2a5731a5bc7a

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
theorem collision_support_c313083_s1_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-134748779/625000000 : ℝ)*x 0 + (4900185961/10000000000 : ℝ)*x 1 + (5406761309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134748779/625000000 : ℝ)^37 ≤ (2823922011827/20000000000000 : ℝ)^29 := by
    have hnat : (134748779 : ℕ)^37*20000000000000^29 ≤ 2823922011827^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134748779 625000000 2823922011827 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4900185961/10000000000 : ℝ)^37 ≤ (8049778933041/20000000000000 : ℝ)^29 := by
    have hnat : (4900185961 : ℕ)^37*20000000000000^29 ≤ 8049778933041^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900185961 10000000000 8049778933041 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406761309/10000000000 : ℝ)^37 ≤ (45631495257169/100000000000000 : ℝ)^29 := by
    have hnat : (5406761309 : ℕ)^37*100000000000000^29 ≤ 45631495257169^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406761309 10000000000 45631495257169 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134748779/625000000 : ℝ), (4900185961/10000000000 : ℝ), (5406761309/10000000000 : ℝ)] ![(2823922011827/20000000000000 : ℝ), (8049778933041/20000000000000 : ℝ), (45631495257169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134748779/625000000 : ℝ)|^37 ≤ (2823922011827/20000000000000 : ℝ)^29
        have hw : |(-134748779/625000000 : ℝ)|=(134748779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4900185961/10000000000 : ℝ)|^37 ≤ (8049778933041/20000000000000 : ℝ)^29
        have hw : |(4900185961/10000000000 : ℝ)|=(4900185961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406761309/10000000000 : ℝ)|^37 ≤ (45631495257169/100000000000000 : ℝ)^29
        have hw : |(5406761309/10000000000 : ℝ)|=(5406761309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3555972179/10000000000 : ℝ)*x 0 + (6570566677/10000000000 : ℝ)*x 1 + (-2230727631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3555972179/10000000000 : ℝ)^37 ≤ (13367641855343/50000000000000 : ℝ)^29 := by
    have hnat : (3555972179 : ℕ)^37*50000000000000^29 ≤ 13367641855343^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3555972179 10000000000 13367641855343 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6570566677/10000000000 : ℝ)^37 ≤ (58517581036761/100000000000000 : ℝ)^29 := by
    have hnat : (6570566677 : ℕ)^37*100000000000000^29 ≤ 58517581036761^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6570566677 10000000000 58517581036761 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230727631/10000000000 : ℝ)^37 ≤ (368678381041/2500000000000 : ℝ)^29 := by
    have hnat : (2230727631 : ℕ)^37*2500000000000^29 ≤ 368678381041^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230727631 10000000000 368678381041 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3555972179/10000000000 : ℝ), (6570566677/10000000000 : ℝ), (-2230727631/10000000000 : ℝ)] ![(13367641855343/50000000000000 : ℝ), (58517581036761/100000000000000 : ℝ), (368678381041/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3555972179/10000000000 : ℝ)|^37 ≤ (13367641855343/50000000000000 : ℝ)^29
        have hw : |(3555972179/10000000000 : ℝ)|=(3555972179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6570566677/10000000000 : ℝ)|^37 ≤ (58517581036761/100000000000000 : ℝ)^29
        have hw : |(6570566677/10000000000 : ℝ)|=(6570566677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230727631/10000000000 : ℝ)|^37 ≤ (368678381041/2500000000000 : ℝ)^29
        have hw : |(-2230727631/10000000000 : ℝ)|=(2230727631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1513916603/5000000000 : ℝ)*x 0 + (1153553093/2500000000 : ℝ)*x 1 + (1241660599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1513916603/5000000000 : ℝ)^37 ≤ (10888446896979/50000000000000 : ℝ)^29 := by
    have hnat : (1513916603 : ℕ)^37*50000000000000^29 ≤ 10888446896979^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513916603 5000000000 10888446896979 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153553093/2500000000 : ℝ)^37 ≤ (18638237733161/50000000000000 : ℝ)^29 := by
    have hnat : (1153553093 : ℕ)^37*50000000000000^29 ≤ 18638237733161^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153553093 2500000000 18638237733161 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241660599/2500000000 : ℝ)^37 ≤ (40946630721669/100000000000000 : ℝ)^29 := by
    have hnat : (1241660599 : ℕ)^37*100000000000000^29 ≤ 40946630721669^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241660599 2500000000 40946630721669 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1513916603/5000000000 : ℝ), (1153553093/2500000000 : ℝ), (1241660599/2500000000 : ℝ)] ![(10888446896979/50000000000000 : ℝ), (18638237733161/50000000000000 : ℝ), (40946630721669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1513916603/5000000000 : ℝ)|^37 ≤ (10888446896979/50000000000000 : ℝ)^29
        have hw : |(1513916603/5000000000 : ℝ)|=(1513916603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1153553093/2500000000 : ℝ)|^37 ≤ (18638237733161/50000000000000 : ℝ)^29
        have hw : |(1153553093/2500000000 : ℝ)|=(1153553093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1241660599/2500000000 : ℝ)|^37 ≤ (40946630721669/100000000000000 : ℝ)^29
        have hw : |(1241660599/2500000000 : ℝ)|=(1241660599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2260581181/10000000000 : ℝ)*x 0 + (4786019821/10000000000 : ℝ)*x 1 + (543578529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260581181/10000000000 : ℝ)^37 ≤ (14999401511623/100000000000000 : ℝ)^29 := by
    have hnat : (2260581181 : ℕ)^37*100000000000000^29 ≤ 14999401511623^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260581181 10000000000 14999401511623 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4786019821/10000000000 : ℝ)^37 ≤ (39056344639053/100000000000000 : ℝ)^29 := by
    have hnat : (4786019821 : ℕ)^37*100000000000000^29 ≤ 39056344639053^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786019821 10000000000 39056344639053 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543578529/1000000000 : ℝ)^37 ≤ (45944253841431/100000000000000 : ℝ)^29 := by
    have hnat : (543578529 : ℕ)^37*100000000000000^29 ≤ 45944253841431^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543578529 1000000000 45944253841431 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2260581181/10000000000 : ℝ), (4786019821/10000000000 : ℝ), (543578529/1000000000 : ℝ)] ![(14999401511623/100000000000000 : ℝ), (39056344639053/100000000000000 : ℝ), (45944253841431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2260581181/10000000000 : ℝ)|^37 ≤ (14999401511623/100000000000000 : ℝ)^29
        have hw : |(-2260581181/10000000000 : ℝ)|=(2260581181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4786019821/10000000000 : ℝ)|^37 ≤ (39056344639053/100000000000000 : ℝ)^29
        have hw : |(4786019821/10000000000 : ℝ)|=(4786019821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543578529/1000000000 : ℝ)|^37 ≤ (45944253841431/100000000000000 : ℝ)^29
        have hw : |(543578529/1000000000 : ℝ)|=(543578529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6262112021/10000000000 : ℝ)*x 0 + (466619/10000000000 : ℝ)*x 1 + (2672340753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6262112021/10000000000 : ℝ)^37 ≤ (1719862955431/3125000000000 : ℝ)^29 := by
    have hnat : (6262112021 : ℕ)^37*3125000000000^29 ≤ 1719862955431^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6262112021 10000000000 1719862955431 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466619/10000000000 : ℝ)^37 ≤ (297984333/100000000000000 : ℝ)^29 := by
    have hnat : (466619 : ℕ)^37*100000000000000^29 ≤ 297984333^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466619 10000000000 297984333 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2672340753/5000000000 : ℝ)^37 ≤ (11241021856079/25000000000000 : ℝ)^29 := by
    have hnat : (2672340753 : ℕ)^37*25000000000000^29 ≤ 11241021856079^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672340753 5000000000 11241021856079 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6262112021/10000000000 : ℝ), (466619/10000000000 : ℝ), (2672340753/5000000000 : ℝ)] ![(1719862955431/3125000000000 : ℝ), (297984333/100000000000000 : ℝ), (11241021856079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6262112021/10000000000 : ℝ)|^37 ≤ (1719862955431/3125000000000 : ℝ)^29
        have hw : |(6262112021/10000000000 : ℝ)|=(6262112021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(466619/10000000000 : ℝ)|^37 ≤ (297984333/100000000000000 : ℝ)^29
        have hw : |(466619/10000000000 : ℝ)|=(466619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2672340753/5000000000 : ℝ)|^37 ≤ (11241021856079/25000000000000 : ℝ)^29
        have hw : |(2672340753/5000000000 : ℝ)|=(2672340753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (356918983/1250000000 : ℝ)*x 0 + (1900218973/2500000000 : ℝ)*x 1 + (-1557390833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356918983/1250000000 : ℝ)^37 ≤ (20206764230159/100000000000000 : ℝ)^29 := by
    have hnat : (356918983 : ℕ)^37*100000000000000^29 ≤ 20206764230159^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356918983 1250000000 20206764230159 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900218973/2500000000 : ℝ)^37 ≤ (35234526803457/50000000000000 : ℝ)^29 := by
    have hnat : (1900218973 : ℕ)^37*50000000000000^29 ≤ 35234526803457^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900218973 2500000000 35234526803457 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557390833/10000000000 : ℝ)^37 ≤ (4662091074947/50000000000000 : ℝ)^29 := by
    have hnat : (1557390833 : ℕ)^37*50000000000000^29 ≤ 4662091074947^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557390833 10000000000 4662091074947 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(356918983/1250000000 : ℝ), (1900218973/2500000000 : ℝ), (-1557390833/10000000000 : ℝ)] ![(20206764230159/100000000000000 : ℝ), (35234526803457/50000000000000 : ℝ), (4662091074947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(356918983/1250000000 : ℝ)|^37 ≤ (20206764230159/100000000000000 : ℝ)^29
        have hw : |(356918983/1250000000 : ℝ)|=(356918983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1900218973/2500000000 : ℝ)|^37 ≤ (35234526803457/50000000000000 : ℝ)^29
        have hw : |(1900218973/2500000000 : ℝ)|=(1900218973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1557390833/10000000000 : ℝ)|^37 ≤ (4662091074947/50000000000000 : ℝ)^29
        have hw : |(-1557390833/10000000000 : ℝ)|=(1557390833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (762465139/2500000000 : ℝ)*x 0 + (4734009113/10000000000 : ℝ)*x 1 + (4829070981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (762465139/2500000000 : ℝ)^37 ≤ (549480647161/2500000000000 : ℝ)^29 := by
    have hnat : (762465139 : ℕ)^37*2500000000000^29 ≤ 549480647161^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762465139 2500000000 549480647161 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4734009113/10000000000 : ℝ)^37 ≤ (4814454950873/12500000000000 : ℝ)^29 := by
    have hnat : (4734009113 : ℕ)^37*12500000000000^29 ≤ 4814454950873^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4734009113 10000000000 4814454950873 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829070981/10000000000 : ℝ)^37 ≤ (39505134486399/100000000000000 : ℝ)^29 := by
    have hnat : (4829070981 : ℕ)^37*100000000000000^29 ≤ 39505134486399^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829070981 10000000000 39505134486399 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(762465139/2500000000 : ℝ), (4734009113/10000000000 : ℝ), (4829070981/10000000000 : ℝ)] ![(549480647161/2500000000000 : ℝ), (4814454950873/12500000000000 : ℝ), (39505134486399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(762465139/2500000000 : ℝ)|^37 ≤ (549480647161/2500000000000 : ℝ)^29
        have hw : |(762465139/2500000000 : ℝ)|=(762465139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4734009113/10000000000 : ℝ)|^37 ≤ (4814454950873/12500000000000 : ℝ)^29
        have hw : |(4734009113/10000000000 : ℝ)|=(4734009113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829070981/10000000000 : ℝ)|^37 ≤ (39505134486399/100000000000000 : ℝ)^29
        have hw : |(4829070981/10000000000 : ℝ)|=(4829070981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036770179/10000000000 : ℝ)*x 0 + (3401990497/10000000000 : ℝ)*x 1 + (3746042083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036770179/10000000000 : ℝ)^37 ≤ (5548130069087/100000000000000 : ℝ)^29 := by
    have hnat : (1036770179 : ℕ)^37*100000000000000^29 ≤ 5548130069087^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036770179 10000000000 5548130069087 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3401990497/10000000000 : ℝ)^37 ≤ (25267136073529/100000000000000 : ℝ)^29 := by
    have hnat : (3401990497 : ℕ)^37*100000000000000^29 ≤ 25267136073529^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3401990497 10000000000 25267136073529 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3746042083/5000000000 : ℝ)^37 ≤ (34592366920351/50000000000000 : ℝ)^29 := by
    have hnat : (3746042083 : ℕ)^37*50000000000000^29 ≤ 34592366920351^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746042083 5000000000 34592366920351 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036770179/10000000000 : ℝ), (3401990497/10000000000 : ℝ), (3746042083/5000000000 : ℝ)] ![(5548130069087/100000000000000 : ℝ), (25267136073529/100000000000000 : ℝ), (34592366920351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036770179/10000000000 : ℝ)|^37 ≤ (5548130069087/100000000000000 : ℝ)^29
        have hw : |(-1036770179/10000000000 : ℝ)|=(1036770179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3401990497/10000000000 : ℝ)|^37 ≤ (25267136073529/100000000000000 : ℝ)^29
        have hw : |(3401990497/10000000000 : ℝ)|=(3401990497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3746042083/5000000000 : ℝ)|^37 ≤ (34592366920351/50000000000000 : ℝ)^29
        have hw : |(3746042083/5000000000 : ℝ)|=(3746042083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (523289487/625000000 : ℝ)*x 0 + (-21189139/1000000000 : ℝ)*x 1 + (1390924109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523289487/625000000 : ℝ)^37 ≤ (39861399870393/50000000000000 : ℝ)^29 := by
    have hnat : (523289487 : ℕ)^37*50000000000000^29 ≤ 39861399870393^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523289487 625000000 39861399870393 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21189139/1000000000 : ℝ)^37 ≤ (73173101679/10000000000000 : ℝ)^29 := by
    have hnat : (21189139 : ℕ)^37*10000000000000^29 ≤ 73173101679^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21189139 1000000000 73173101679 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390924109/5000000000 : ℝ)^37 ≤ (9772734614049/50000000000000 : ℝ)^29 := by
    have hnat : (1390924109 : ℕ)^37*50000000000000^29 ≤ 9772734614049^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390924109 5000000000 9772734614049 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523289487/625000000 : ℝ), (-21189139/1000000000 : ℝ), (1390924109/5000000000 : ℝ)] ![(39861399870393/50000000000000 : ℝ), (73173101679/10000000000000 : ℝ), (9772734614049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523289487/625000000 : ℝ)|^37 ≤ (39861399870393/50000000000000 : ℝ)^29
        have hw : |(523289487/625000000 : ℝ)|=(523289487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21189139/1000000000 : ℝ)|^37 ≤ (73173101679/10000000000000 : ℝ)^29
        have hw : |(-21189139/1000000000 : ℝ)|=(21189139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1390924109/5000000000 : ℝ)|^37 ≤ (9772734614049/50000000000000 : ℝ)^29
        have hw : |(1390924109/5000000000 : ℝ)|=(1390924109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3749079511/10000000000 : ℝ)*x 0 + (7086629973/10000000000 : ℝ)*x 1 + (-247530741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3749079511/10000000000 : ℝ)^37 ≤ (28601356009711/100000000000000 : ℝ)^29 := by
    have hnat : (3749079511 : ℕ)^37*100000000000000^29 ≤ 28601356009711^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749079511 10000000000 28601356009711 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7086629973/10000000000 : ℝ)^37 ≤ (32221945811469/50000000000000 : ℝ)^29 := by
    have hnat : (7086629973 : ℕ)^37*50000000000000^29 ≤ 32221945811469^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7086629973 10000000000 32221945811469 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247530741/2000000000 : ℝ)^37 ≤ (6954752341153/100000000000000 : ℝ)^29 := by
    have hnat : (247530741 : ℕ)^37*100000000000000^29 ≤ 6954752341153^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247530741 2000000000 6954752341153 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3749079511/10000000000 : ℝ), (7086629973/10000000000 : ℝ), (-247530741/2000000000 : ℝ)] ![(28601356009711/100000000000000 : ℝ), (32221945811469/50000000000000 : ℝ), (6954752341153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3749079511/10000000000 : ℝ)|^37 ≤ (28601356009711/100000000000000 : ℝ)^29
        have hw : |(3749079511/10000000000 : ℝ)|=(3749079511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7086629973/10000000000 : ℝ)|^37 ≤ (32221945811469/50000000000000 : ℝ)^29
        have hw : |(7086629973/10000000000 : ℝ)|=(7086629973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247530741/2000000000 : ℝ)|^37 ≤ (6954752341153/100000000000000 : ℝ)^29
        have hw : |(-247530741/2000000000 : ℝ)|=(247530741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2452050457/10000000000 : ℝ)*x 0 + (3574525159/10000000000 : ℝ)*x 1 + (6387702523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2452050457/10000000000 : ℝ)^37 ≤ (1039929116357/6250000000000 : ℝ)^29 := by
    have hnat : (2452050457 : ℕ)^37*6250000000000^29 ≤ 1039929116357^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452050457 10000000000 1039929116357 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574525159/10000000000 : ℝ)^37 ≤ (26913380412783/100000000000000 : ℝ)^29 := by
    have hnat : (3574525159 : ℕ)^37*100000000000000^29 ≤ 26913380412783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574525159 10000000000 26913380412783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6387702523/10000000000 : ℝ)^37 ≤ (2257910148101/4000000000000 : ℝ)^29 := by
    have hnat : (6387702523 : ℕ)^37*4000000000000^29 ≤ 2257910148101^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6387702523 10000000000 2257910148101 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2452050457/10000000000 : ℝ), (3574525159/10000000000 : ℝ), (6387702523/10000000000 : ℝ)] ![(1039929116357/6250000000000 : ℝ), (26913380412783/100000000000000 : ℝ), (2257910148101/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2452050457/10000000000 : ℝ)|^37 ≤ (1039929116357/6250000000000 : ℝ)^29
        have hw : |(2452050457/10000000000 : ℝ)|=(2452050457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3574525159/10000000000 : ℝ)|^37 ≤ (26913380412783/100000000000000 : ℝ)^29
        have hw : |(3574525159/10000000000 : ℝ)|=(3574525159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6387702523/10000000000 : ℝ)|^37 ≤ (2257910148101/4000000000000 : ℝ)^29
        have hw : |(6387702523/10000000000 : ℝ)|=(6387702523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-39712103/250000000 : ℝ)*x 0 + (1419625413/2500000000 : ℝ)*x 1 + (5053272443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39712103/250000000 : ℝ)^37 ≤ (4781171976733/50000000000000 : ℝ)^29 := by
    have hnat : (39712103 : ℕ)^37*50000000000000^29 ≤ 4781171976733^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39712103 250000000 4781171976733 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1419625413/2500000000 : ℝ)^37 ≤ (48577613151149/100000000000000 : ℝ)^29 := by
    have hnat : (1419625413 : ℕ)^37*100000000000000^29 ≤ 48577613151149^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419625413 2500000000 48577613151149 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053272443/10000000000 : ℝ)^37 ≤ (41860042886259/100000000000000 : ℝ)^29 := by
    have hnat : (5053272443 : ℕ)^37*100000000000000^29 ≤ 41860042886259^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053272443 10000000000 41860042886259 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39712103/250000000 : ℝ), (1419625413/2500000000 : ℝ), (5053272443/10000000000 : ℝ)] ![(4781171976733/50000000000000 : ℝ), (48577613151149/100000000000000 : ℝ), (41860042886259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39712103/250000000 : ℝ)|^37 ≤ (4781171976733/50000000000000 : ℝ)^29
        have hw : |(-39712103/250000000 : ℝ)|=(39712103/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1419625413/2500000000 : ℝ)|^37 ≤ (48577613151149/100000000000000 : ℝ)^29
        have hw : |(1419625413/2500000000 : ℝ)|=(1419625413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5053272443/10000000000 : ℝ)|^37 ≤ (41860042886259/100000000000000 : ℝ)^29
        have hw : |(5053272443/10000000000 : ℝ)|=(5053272443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7568768709/10000000000 : ℝ)*x 0 + (25727/625000000 : ℝ)*x 1 + (3882901259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7568768709/10000000000 : ℝ)^37 ≤ (35044743779783/50000000000000 : ℝ)^29 := by
    have hnat : (7568768709 : ℕ)^37*50000000000000^29 ≤ 35044743779783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7568768709 10000000000 35044743779783 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25727/625000000 : ℝ)^37 ≤ (5078653/2000000000000 : ℝ)^29 := by
    have hnat : (25727 : ℕ)^37*2000000000000^29 ≤ 5078653^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25727 625000000 5078653 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3882901259/10000000000 : ℝ)^37 ≤ (7477564625783/25000000000000 : ℝ)^29 := by
    have hnat : (3882901259 : ℕ)^37*25000000000000^29 ≤ 7477564625783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3882901259 10000000000 7477564625783 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7568768709/10000000000 : ℝ), (25727/625000000 : ℝ), (3882901259/10000000000 : ℝ)] ![(35044743779783/50000000000000 : ℝ), (5078653/2000000000000 : ℝ), (7477564625783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7568768709/10000000000 : ℝ)|^37 ≤ (35044743779783/50000000000000 : ℝ)^29
        have hw : |(7568768709/10000000000 : ℝ)|=(7568768709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25727/625000000 : ℝ)|^37 ≤ (5078653/2000000000000 : ℝ)^29
        have hw : |(25727/625000000 : ℝ)|=(25727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3882901259/10000000000 : ℝ)|^37 ≤ (7477564625783/25000000000000 : ℝ)^29
        have hw : |(3882901259/10000000000 : ℝ)|=(3882901259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3472428273/10000000000 : ℝ)*x 0 + (3358865763/5000000000 : ℝ)*x 1 + (-2125877429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3472428273/10000000000 : ℝ)^37 ≤ (81051573887/312500000000 : ℝ)^29 := by
    have hnat : (3472428273 : ℕ)^37*312500000000^29 ≤ 81051573887^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472428273 10000000000 81051573887 312500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3358865763/5000000000 : ℝ)^37 ≤ (15048732861563/25000000000000 : ℝ)^29 := by
    have hnat : (3358865763 : ℕ)^37*25000000000000^29 ≤ 15048732861563^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3358865763 5000000000 15048732861563 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125877429/10000000000 : ℝ)^37 ≤ (13868564902003/100000000000000 : ℝ)^29 := by
    have hnat : (2125877429 : ℕ)^37*100000000000000^29 ≤ 13868564902003^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125877429 10000000000 13868564902003 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3472428273/10000000000 : ℝ), (3358865763/5000000000 : ℝ), (-2125877429/10000000000 : ℝ)] ![(81051573887/312500000000 : ℝ), (15048732861563/25000000000000 : ℝ), (13868564902003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3472428273/10000000000 : ℝ)|^37 ≤ (81051573887/312500000000 : ℝ)^29
        have hw : |(3472428273/10000000000 : ℝ)|=(3472428273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3358865763/5000000000 : ℝ)|^37 ≤ (15048732861563/25000000000000 : ℝ)^29
        have hw : |(3358865763/5000000000 : ℝ)|=(3358865763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125877429/10000000000 : ℝ)|^37 ≤ (13868564902003/100000000000000 : ℝ)^29
        have hw : |(-2125877429/10000000000 : ℝ)|=(2125877429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313083_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (396985509/1000000000 : ℝ)*x 0 + (4481311749/10000000000 : ℝ)*x 1 + (845158319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396985509/1000000000 : ℝ)^37 ≤ (30767471016633/100000000000000 : ℝ)^29 := by
    have hnat : (396985509 : ℕ)^37*100000000000000^29 ≤ 30767471016633^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396985509 1000000000 30767471016633 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481311749/10000000000 : ℝ)^37 ≤ (7182424317001/20000000000000 : ℝ)^29 := by
    have hnat : (4481311749 : ℕ)^37*20000000000000^29 ≤ 7182424317001^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481311749 10000000000 7182424317001 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845158319/2000000000 : ℝ)^37 ≤ (16660203691609/50000000000000 : ℝ)^29 := by
    have hnat : (845158319 : ℕ)^37*50000000000000^29 ≤ 16660203691609^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845158319 2000000000 16660203691609 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(396985509/1000000000 : ℝ), (4481311749/10000000000 : ℝ), (845158319/2000000000 : ℝ)] ![(30767471016633/100000000000000 : ℝ), (7182424317001/20000000000000 : ℝ), (16660203691609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(396985509/1000000000 : ℝ)|^37 ≤ (30767471016633/100000000000000 : ℝ)^29
        have hw : |(396985509/1000000000 : ℝ)|=(396985509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481311749/10000000000 : ℝ)|^37 ≤ (7182424317001/20000000000000 : ℝ)^29
        have hw : |(4481311749/10000000000 : ℝ)|=(4481311749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845158319/2000000000 : ℝ)|^37 ≤ (16660203691609/50000000000000 : ℝ)^29
        have hw : |(845158319/2000000000 : ℝ)|=(845158319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313083_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((72471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((36847/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(36847/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79577/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79577/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10903/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10903/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((38337/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(38337/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47089/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47089/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s1_pow0 : (72471/100000 : ℝ) ^ (73/16 : ℝ) ≤ (23014386854965156367/100000000000000000000 : ℝ) := by
    have hpowers : (72471/100000 : ℝ)^73 ≤ (23014386854965156367/100000000000000000000 : ℝ)^16 := by
      have hnat : (72471 : ℕ)^73*100000000000000000000^16 ≤ 23014386854965156367^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72471 100000 23014386854965156367 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72471/100000 : ℝ)) (X := (23014386854965156367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (123014386854965156367/100000000000000000000 : ℝ) ≤ (327014029209691/312500000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (123014386854965156367/100000000000000000000 : ℝ)^16 ≤ (327014029209691/312500000000000 : ℝ)^73 := by
      have hnat : (123014386854965156367 : ℕ)^16*312500000000000^73 ≤ 327014029209691^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123014386854965156367 100000000000000000000 327014029209691 312500000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (327014029209691/312500000000000 : ℝ)) (X := (123014386854965156367/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (73014386854965156367/50000000000000000000 : ℝ) ≤ (10865289479005331/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (73014386854965156367/50000000000000000000 : ℝ)^16 ≤ (10865289479005331/10000000000000000 : ℝ)^73 := by
      have hnat : (73014386854965156367 : ℕ)^16*10000000000000000^73 ≤ 10865289479005331^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73014386854965156367 50000000000000000000 10865289479005331 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10865289479005331/10000000000000000 : ℝ)) (X := (73014386854965156367/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14514029209691/226471875000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2726806423777/49300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (72471/100000 : ℝ)) (alpha := (14514029209691/226471875000000 : ℝ)) (beta := (2726806423777/49300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72471/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14514029209691/226471875000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2726806423777/49300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (36847/50000 : ℝ) ^ (73/16 : ℝ) ≤ (12420214536201703901/50000000000000000000 : ℝ) := by
    have hpowers : (36847/50000 : ℝ)^73 ≤ (12420214536201703901/50000000000000000000 : ℝ)^16 := by
      have hnat : (36847 : ℕ)^73*50000000000000000000^16 ≤ 12420214536201703901^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36847 50000 12420214536201703901 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36847/50000 : ℝ)) (X := (12420214536201703901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (62420214536201703901/50000000000000000000 : ℝ) ≤ (10498299527479883/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (62420214536201703901/50000000000000000000 : ℝ)^16 ≤ (10498299527479883/10000000000000000 : ℝ)^73 := by
      have hnat : (62420214536201703901 : ℕ)^16*10000000000000000^73 ≤ 10498299527479883^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62420214536201703901 50000000000000000000 10498299527479883 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10498299527479883/10000000000000000 : ℝ)) (X := (62420214536201703901/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (37420214536201703901/25000000000000000000 : ℝ) ≤ (5462137269375483/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (37420214536201703901/25000000000000000000 : ℝ)^16 ≤ (5462137269375483/5000000000000000 : ℝ)^73 := by
      have hnat : (37420214536201703901 : ℕ)^16*5000000000000000^73 ≤ 5462137269375483^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37420214536201703901 25000000000000000000 5462137269375483 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5462137269375483/5000000000000000 : ℝ)) (X := (37420214536201703901/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(498299527479883/7369400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(425975011271083/7369400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (36847/50000 : ℝ)) (alpha := (498299527479883/7369400000000000 : ℝ)) (beta := (425975011271083/7369400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (36847/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(498299527479883/7369400000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(425975011271083/7369400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (79577/100000 : ℝ) ^ (73/16 : ℝ) ≤ (705298969973113309/2000000000000000000 : ℝ) := by
    have hpowers : (79577/100000 : ℝ)^73 ≤ (705298969973113309/2000000000000000000 : ℝ)^16 := by
      have hnat : (79577 : ℕ)^73*2000000000000000000^16 ≤ 705298969973113309^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79577 100000 705298969973113309 2000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79577/100000 : ℝ)) (X := (705298969973113309/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2705298969973113309/2000000000000000000 : ℝ) ≤ (1335558603111379/1250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2705298969973113309/2000000000000000000 : ℝ)^16 ≤ (1335558603111379/1250000000000000 : ℝ)^73 := by
      have hnat : (2705298969973113309 : ℕ)^16*1250000000000000^73 ≤ 1335558603111379^73*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2705298969973113309 2000000000000000000 1335558603111379 1250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1335558603111379/1250000000000000 : ℝ)) (X := (2705298969973113309/2000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1705298969973113309/1000000000000000000 : ℝ) ≤ (281025419145997/250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (1705298969973113309/1000000000000000000 : ℝ)^16 ≤ (281025419145997/250000000000000 : ℝ)^73 := by
      have hnat : (1705298969973113309 : ℕ)^16*250000000000000^73 ≤ 281025419145997^73*1000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1705298969973113309 1000000000000000000 281025419145997 250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (281025419145997/250000000000000 : ℝ)) (X := (1705298969973113309/1000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(85558603111379/994712500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(34784246309303/497356250000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (79577/100000 : ℝ)) (alpha := (85558603111379/994712500000000 : ℝ)) (beta := (34784246309303/497356250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (79577/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(85558603111379/994712500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(34784246309303/497356250000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-134748779/625000000 : ℝ)*X 0 0+(4900185961/10000000000 : ℝ)*X 0 1+(5406761309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3555972179/10000000000 : ℝ)*X 2 0+(6570566677/10000000000 : ℝ)*X 2 1+(-2230727631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1513916603/5000000000 : ℝ)*X 0 0+(1153553093/2500000000 : ℝ)*X 0 1+(1241660599/2500000000 : ℝ)*X 0 2+(1513916603/5000000000 : ℝ)*X 1 0+(1153553093/2500000000 : ℝ)*X 1 1+(1241660599/2500000000 : ℝ)*X 1 2+(1513916603/5000000000 : ℝ)*X 2 0+(1153553093/2500000000 : ℝ)*X 2 1+(1241660599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2260581181/10000000000 : ℝ)*X 0 0+(4786019821/10000000000 : ℝ)*X 0 1+(543578529/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((6262112021/10000000000 : ℝ)*X 1 0+(466619/10000000000 : ℝ)*X 1 1+(2672340753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((356918983/1250000000 : ℝ)*X 2 0+(1900218973/2500000000 : ℝ)*X 2 1+(-1557390833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((762465139/2500000000 : ℝ)*X 0 0+(4734009113/10000000000 : ℝ)*X 0 1+(4829070981/10000000000 : ℝ)*X 0 2+(762465139/2500000000 : ℝ)*X 1 0+(4734009113/10000000000 : ℝ)*X 1 1+(4829070981/10000000000 : ℝ)*X 1 2+(762465139/2500000000 : ℝ)*X 2 0+(4734009113/10000000000 : ℝ)*X 2 1+(4829070981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1036770179/10000000000 : ℝ)*X 0 0+(3401990497/10000000000 : ℝ)*X 0 1+(3746042083/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((523289487/625000000 : ℝ)*X 1 0+(-21189139/1000000000 : ℝ)*X 1 1+(1390924109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3749079511/10000000000 : ℝ)*X 2 0+(7086629973/10000000000 : ℝ)*X 2 1+(-247530741/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2452050457/10000000000 : ℝ)*X 0 0+(3574525159/10000000000 : ℝ)*X 0 1+(6387702523/10000000000 : ℝ)*X 0 2+(2452050457/10000000000 : ℝ)*X 1 0+(3574525159/10000000000 : ℝ)*X 1 1+(6387702523/10000000000 : ℝ)*X 1 2+(2452050457/10000000000 : ℝ)*X 2 0+(3574525159/10000000000 : ℝ)*X 2 1+(6387702523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-39712103/250000000 : ℝ)*X 0 0+(1419625413/2500000000 : ℝ)*X 0 1+(5053272443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7568768709/10000000000 : ℝ)*X 1 0+(25727/625000000 : ℝ)*X 1 1+(3882901259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3472428273/10000000000 : ℝ)*X 2 0+(3358865763/5000000000 : ℝ)*X 2 1+(-2125877429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((396985509/1000000000 : ℝ)*X 0 0+(4481311749/10000000000 : ℝ)*X 0 1+(845158319/2000000000 : ℝ)*X 0 2+(396985509/1000000000 : ℝ)*X 1 0+(4481311749/10000000000 : ℝ)*X 1 1+(845158319/2000000000 : ℝ)*X 1 2+(396985509/1000000000 : ℝ)*X 2 0+(4481311749/10000000000 : ℝ)*X 2 1+(845158319/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((10903/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10903/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11708848594551146873182376883/1700660757020000000000000000000000 : ℝ) := by norm_num
    linear_combination (173093289953/500000000000 : ℝ)*(base7) + (759168052537/1000000000000 : ℝ)*(base49) + (333943021463/1000000000000 : ℝ)*(base60) + (3454906053757/1000000000000 : ℝ)*(major_s1_0) + (3454906053757/1000000000000 : ℝ)*(major_s1_1) + (3454906053757/1000000000000 : ℝ)*(major_s1_2) + (176225221/500000000000 : ℝ)*(sp_s1_0) + (22872397/100000000000 : ℝ)*(sp_s1_6) + (233339457491/50000000000 : ℝ)*(sp_s1_7) + (4667136836693/1000000000000 : ℝ)*(sp_s1_8) + (4667141888891/1000000000000 : ℝ)*(sp_s1_9) + (14902542839/6250000000 : ℝ)*(sp_s1_13) + (288629/1000000000000 : ℝ)*(sp_s1_14) + (5052197/1000000000000 : ℝ)*(sp_s1_22) + (407689799661/200000000000 : ℝ)*(f.failure) + (4667141888891/1000000000000 : ℝ)*(f.sum) + (239214655568519194211/586434743800000000000000000000000 : ℝ)*base62 + (1031488082349793/3978850000000000000000000000 : ℝ)*base65 + (589435146172449/7369400000000000000000000000 : ℝ)*base66 + (642085657828251/1989425000000000000000000000 : ℝ)*base69 + (7164027942553278131/16961837550000000000000000000000 : ℝ)*base71 + (23909387782059/49300000000000000000000000 : ℝ)*base73 + (2882956580631791/7369400000000000000000000000 : ℝ)*base74 + (112923683163367/905887500000000000000000000 : ℝ)*base76 + (1105146545221493709/3633114200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (3907/20000000000000000 : ℝ)*base87 + (3907/20000000000000000 : ℝ)*base89 + (3907/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((38337/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(38337/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1920203994968001850399068903/146608685950000000000000000000000 : ℝ) := by norm_num
    linear_combination (636139/200000000000 : ℝ)*(base21) + (2796043/200000000000 : ℝ)*(base33) + (782708134691/1000000000000 : ℝ)*(base40) + (147087785977/200000000000 : ℝ)*(base49) + (654161434467/1000000000000 : ℝ)*(base60) + (2734931515901/1000000000000 : ℝ)*(major_s1_0) + (683736374029/250000000000 : ℝ)*(major_s1_1) + (683736374029/250000000000 : ℝ)*(major_s1_2) + (14508741/1000000000000 : ℝ)*(sp_s1_2) + (964056424737/250000000000 : ℝ)*(sp_s1_14) + (964031233511/250000000000 : ℝ)*(sp_s1_15) + (3856194029297/1000000000000 : ℝ)*(sp_s1_16) + (322732185491/200000000000 : ℝ)*(sp_s1_20) + (86784689/1000000000000 : ℝ)*(sp_s1_22) + (322732185491/200000000000 : ℝ)*(f.failure) + (964056424737/250000000000 : ℝ)*(f.sum) + (1841241088250177049/18326085743750000000000000000000 : ℝ)*base62 + (310845178748201/3978850000000000000000000000 : ℝ)*base64 + (15841399449897/115146875000000000000000000 : ℝ)*base67 + (3269301770871/994712500000000000000000000 : ℝ)*base68 + (5329599483637023013/16961837550000000000000000000000 : ℝ)*base71 + (14519840241363/49300000000000000000000000 : ℝ)*base72 + (68877536363729/921175000000000000000000000 : ℝ)*base75 + (838273139559509/3623550000000000000000000000 : ℝ)*base76 + (262847889957478331/1816557100000000000000000000000 : ℝ)*base79 + (6883/20000000000000000 : ℝ)*base86 + (6883/20000000000000000 : ℝ)*base88 + (6883/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47089/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47089/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (602761703862250223600653838617/41666188546990000000000000000000000 : ℝ) := by norm_num
    linear_combination (201974933513/1000000000000 : ℝ)*(base7) + (28085155209/40000000000 : ℝ)*(base40) + (246273104711/250000000000 : ℝ)*(base49) + (3617741/1000000000000 : ℝ)*(base60) + (2344505672263/500000000000 : ℝ)*(major_s1_0) + (2344505672263/500000000000 : ℝ)*(major_s1_1) + (2344505672263/500000000000 : ℝ)*(major_s1_2) + (29613167/200000000000 : ℝ)*(sp_s1_2) + (11448469/1000000000000 : ℝ)*(sp_s1_8) + (3639573/40000000000 : ℝ)*(sp_s1_16) + (1623070068157/250000000000 : ℝ)*(sp_s1_21) + (6492268824159/1000000000000 : ℝ)*(sp_s1_22) + (6492041217469/1000000000000 : ℝ)*(sp_s1_23) + (92767671711/31250000000 : ℝ)*(sp_s1_27) + (1383295280619/500000000000 : ℝ)*(f.failure) + (1623070068157/250000000000 : ℝ)*(f.sum) + (52464960620618973429/293217371900000000000000000000000 : ℝ)*base62 + (33720689411813/124339062500000000000000000 : ℝ)*base64 + (1352615511239451/3684700000000000000000000000 : ℝ)*base66 + (533378878773671/994712500000000000000000000 : ℝ)*base68 + (2967329580514072637/16961837550000000000000000000000 : ℝ)*base70 + (801420480303/3081250000000000000000000 : ℝ)*base72 + (2128065925877619/3684700000000000000000000000 : ℝ)*base74 + (2124544518634777/1811775000000000000000000000 : ℝ)*base76 + (160559511663184901/1816557100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (27547/50000000000000000 : ℝ)*base86 + (27547/50000000000000000 : ℝ)*base88 + (27547/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((72471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((36847/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(36847/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79577/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79577/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10903/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10903/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((38337/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(38337/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47089/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47089/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313083_s1 p hpa hpb X hX hprev0

#print axioms solution

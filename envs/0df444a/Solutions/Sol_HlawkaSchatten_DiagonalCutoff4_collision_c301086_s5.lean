-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301086_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:44:51.390993+00:00
-- url     : https://prove2.me/submissions/b4cd5c72-ffc8-4373-aa9a-8b3c097ceeba

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
theorem collision_support_c301086_s5_s5_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-972188421/10000000000 : ℝ)*x 0 + (-2920502841/5000000000 : ℝ)*x 1 + (5610259679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972188421/10000000000 : ℝ)^65 ≤ (2270858017489/50000000000000 : ℝ)^49 := by
    have hnat : (972188421 : ℕ)^65*50000000000000^49 ≤ 2270858017489^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972188421 10000000000 2270858017489 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2920502841/5000000000 : ℝ)^65 ≤ (49004807906607/100000000000000 : ℝ)^49 := by
    have hnat : (2920502841 : ℕ)^65*100000000000000^49 ≤ 49004807906607^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2920502841 5000000000 49004807906607 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5610259679/10000000000 : ℝ)^65 ≤ (23226738020053/50000000000000 : ℝ)^49 := by
    have hnat : (5610259679 : ℕ)^65*50000000000000^49 ≤ 23226738020053^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610259679 10000000000 23226738020053 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-972188421/10000000000 : ℝ), (-2920502841/5000000000 : ℝ), (5610259679/10000000000 : ℝ)] ![(2270858017489/50000000000000 : ℝ), (49004807906607/100000000000000 : ℝ), (23226738020053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-972188421/10000000000 : ℝ)|^65 ≤ (2270858017489/50000000000000 : ℝ)^49
        have hw : |(-972188421/10000000000 : ℝ)|=(972188421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2920502841/5000000000 : ℝ)|^65 ≤ (49004807906607/100000000000000 : ℝ)^49
        have hw : |(-2920502841/5000000000 : ℝ)|=(2920502841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5610259679/10000000000 : ℝ)|^65 ≤ (23226738020053/50000000000000 : ℝ)^49
        have hw : |(5610259679/10000000000 : ℝ)|=(5610259679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5685216337/10000000000 : ℝ)*x 0 + (-1899054839/5000000000 : ℝ)*x 1 + (-704066401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5685216337/10000000000 : ℝ)^65 ≤ (11819643841803/25000000000000 : ℝ)^49 := by
    have hnat : (5685216337 : ℕ)^65*25000000000000^49 ≤ 11819643841803^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5685216337 10000000000 11819643841803 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899054839/5000000000 : ℝ)^65 ≤ (1730467463223/6250000000000 : ℝ)^49 := by
    have hnat : (1899054839 : ℕ)^65*6250000000000^49 ≤ 1730467463223^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899054839 5000000000 1730467463223 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (704066401/2000000000 : ℝ)^65 ≤ (5006789039627/20000000000000 : ℝ)^49 := by
    have hnat : (704066401 : ℕ)^65*20000000000000^49 ≤ 5006789039627^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704066401 2000000000 5006789039627 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5685216337/10000000000 : ℝ), (-1899054839/5000000000 : ℝ), (-704066401/2000000000 : ℝ)] ![(11819643841803/25000000000000 : ℝ), (1730467463223/6250000000000 : ℝ), (5006789039627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5685216337/10000000000 : ℝ)|^65 ≤ (11819643841803/25000000000000 : ℝ)^49
        have hw : |(5685216337/10000000000 : ℝ)|=(5685216337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1899054839/5000000000 : ℝ)|^65 ≤ (1730467463223/6250000000000 : ℝ)^49
        have hw : |(-1899054839/5000000000 : ℝ)|=(1899054839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-704066401/2000000000 : ℝ)|^65 ≤ (5006789039627/20000000000000 : ℝ)^49
        have hw : |(-704066401/2000000000 : ℝ)|=(704066401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-746146321/10000000000 : ℝ)*x 0 + (-3431464113/5000000000 : ℝ)*x 1 + (2320091411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (746146321/10000000000 : ℝ)^65 ≤ (639435183797/20000000000000 : ℝ)^49 := by
    have hnat : (746146321 : ℕ)^65*20000000000000^49 ≤ 639435183797^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746146321 10000000000 639435183797 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3431464113/5000000000 : ℝ)^65 ≤ (60691069380679/100000000000000 : ℝ)^49 := by
    have hnat : (3431464113 : ℕ)^65*100000000000000^49 ≤ 60691069380679^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431464113 5000000000 60691069380679 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320091411/5000000000 : ℝ)^65 ≤ (36111754678161/100000000000000 : ℝ)^49 := by
    have hnat : (2320091411 : ℕ)^65*100000000000000^49 ≤ 36111754678161^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320091411 5000000000 36111754678161 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-746146321/10000000000 : ℝ), (-3431464113/5000000000 : ℝ), (2320091411/5000000000 : ℝ)] ![(639435183797/20000000000000 : ℝ), (60691069380679/100000000000000 : ℝ), (36111754678161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-746146321/10000000000 : ℝ)|^65 ≤ (639435183797/20000000000000 : ℝ)^49
        have hw : |(-746146321/10000000000 : ℝ)|=(746146321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3431464113/5000000000 : ℝ)|^65 ≤ (60691069380679/100000000000000 : ℝ)^49
        have hw : |(-3431464113/5000000000 : ℝ)|=(3431464113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2320091411/5000000000 : ℝ)|^65 ≤ (36111754678161/100000000000000 : ℝ)^49
        have hw : |(2320091411/5000000000 : ℝ)|=(2320091411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5930290867/10000000000 : ℝ)*x 0 + (177625579/500000000 : ℝ)*x 1 + (1740366353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5930290867/10000000000 : ℝ)^65 ≤ (2500048103817/5000000000000 : ℝ)^49 := by
    have hnat : (5930290867 : ℕ)^65*5000000000000^49 ≤ 2500048103817^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5930290867 10000000000 2500048103817 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177625579/500000000 : ℝ)^65 ≤ (1583622275453/6250000000000 : ℝ)^49 := by
    have hnat : (177625579 : ℕ)^65*6250000000000^49 ≤ 1583622275453^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177625579 500000000 1583622275453 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1740366353/5000000000 : ℝ)^65 ≤ (1541317594287/6250000000000 : ℝ)^49 := by
    have hnat : (1740366353 : ℕ)^65*6250000000000^49 ≤ 1541317594287^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740366353 5000000000 1541317594287 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5930290867/10000000000 : ℝ), (177625579/500000000 : ℝ), (1740366353/5000000000 : ℝ)] ![(2500048103817/5000000000000 : ℝ), (1583622275453/6250000000000 : ℝ), (1541317594287/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5930290867/10000000000 : ℝ)|^65 ≤ (2500048103817/5000000000000 : ℝ)^49
        have hw : |(5930290867/10000000000 : ℝ)|=(5930290867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177625579/500000000 : ℝ)|^65 ≤ (1583622275453/6250000000000 : ℝ)^49
        have hw : |(177625579/500000000 : ℝ)|=(177625579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1740366353/5000000000 : ℝ)|^65 ≤ (1541317594287/6250000000000 : ℝ)^49
        have hw : |(1740366353/5000000000 : ℝ)|=(1740366353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5959779717/10000000000 : ℝ)*x 0 + (-3552666893/10000000000 : ℝ)*x 1 + (-861349083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5959779717/10000000000 : ℝ)^65 ≤ (25165524957921/50000000000000 : ℝ)^49 := by
    have hnat : (5959779717 : ℕ)^65*50000000000000^49 ≤ 25165524957921^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959779717 10000000000 25165524957921 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3552666893/10000000000 : ℝ)^65 ≤ (25339425889237/100000000000000 : ℝ)^49 := by
    have hnat : (3552666893 : ℕ)^65*100000000000000^49 ≤ 25339425889237^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552666893 10000000000 25339425889237 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861349083/2500000000 : ℝ)^65 ≤ (24329524183457/100000000000000 : ℝ)^49 := by
    have hnat : (861349083 : ℕ)^65*100000000000000^49 ≤ 24329524183457^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861349083 2500000000 24329524183457 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5959779717/10000000000 : ℝ), (-3552666893/10000000000 : ℝ), (-861349083/2500000000 : ℝ)] ![(25165524957921/50000000000000 : ℝ), (25339425889237/100000000000000 : ℝ), (24329524183457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5959779717/10000000000 : ℝ)|^65 ≤ (25165524957921/50000000000000 : ℝ)^49
        have hw : |(5959779717/10000000000 : ℝ)|=(5959779717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3552666893/10000000000 : ℝ)|^65 ≤ (25339425889237/100000000000000 : ℝ)^49
        have hw : |(-3552666893/10000000000 : ℝ)|=(3552666893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-861349083/2500000000 : ℝ)|^65 ≤ (24329524183457/100000000000000 : ℝ)^49
        have hw : |(-861349083/2500000000 : ℝ)|=(861349083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3500033871/10000000000 : ℝ)*x 0 + (-2228546081/10000000000 : ℝ)*x 1 + (86655033/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3500033871/10000000000 : ℝ)^65 ≤ (24842647605839/100000000000000 : ℝ)^49 := by
    have hnat : (3500033871 : ℕ)^65*100000000000000^49 ≤ 24842647605839^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3500033871 10000000000 24842647605839 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228546081/10000000000 : ℝ)^65 ≤ (13649939254439/100000000000000 : ℝ)^49 := by
    have hnat : (2228546081 : ℕ)^65*100000000000000^49 ≤ 13649939254439^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228546081 10000000000 13649939254439 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86655033/125000000 : ℝ)^65 ≤ (61507413129443/100000000000000 : ℝ)^49 := by
    have hnat : (86655033 : ℕ)^65*100000000000000^49 ≤ 61507413129443^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86655033 125000000 61507413129443 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3500033871/10000000000 : ℝ), (-2228546081/10000000000 : ℝ), (86655033/125000000 : ℝ)] ![(24842647605839/100000000000000 : ℝ), (13649939254439/100000000000000 : ℝ), (61507413129443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3500033871/10000000000 : ℝ)|^65 ≤ (24842647605839/100000000000000 : ℝ)^49
        have hw : |(3500033871/10000000000 : ℝ)|=(3500033871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228546081/10000000000 : ℝ)|^65 ≤ (13649939254439/100000000000000 : ℝ)^49
        have hw : |(-2228546081/10000000000 : ℝ)|=(2228546081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86655033/125000000 : ℝ)|^65 ≤ (61507413129443/100000000000000 : ℝ)^49
        have hw : |(86655033/125000000 : ℝ)|=(86655033/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5810841/200000000 : ℝ)*x 0 + (-2775726537/5000000000 : ℝ)*x 1 + (3110421543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5810841/200000000 : ℝ)^65 ≤ (457477451993/50000000000000 : ℝ)^49 := by
    have hnat : (5810841 : ℕ)^65*50000000000000^49 ≤ 457477451993^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5810841 200000000 457477451993 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2775726537/5000000000 : ℝ)^65 ≤ (45808664183471/100000000000000 : ℝ)^49 := by
    have hnat : (2775726537 : ℕ)^65*100000000000000^49 ≤ 45808664183471^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775726537 5000000000 45808664183471 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3110421543/5000000000 : ℝ)^65 ≤ (5327638089891/10000000000000 : ℝ)^49 := by
    have hnat : (3110421543 : ℕ)^65*10000000000000^49 ≤ 5327638089891^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110421543 5000000000 5327638089891 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5810841/200000000 : ℝ), (-2775726537/5000000000 : ℝ), (3110421543/5000000000 : ℝ)] ![(457477451993/50000000000000 : ℝ), (45808664183471/100000000000000 : ℝ), (5327638089891/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5810841/200000000 : ℝ)|^65 ≤ (457477451993/50000000000000 : ℝ)^49
        have hw : |(-5810841/200000000 : ℝ)|=(5810841/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2775726537/5000000000 : ℝ)|^65 ≤ (45808664183471/100000000000000 : ℝ)^49
        have hw : |(-2775726537/5000000000 : ℝ)|=(2775726537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3110421543/5000000000 : ℝ)|^65 ≤ (5327638089891/10000000000000 : ℝ)^49
        have hw : |(3110421543/5000000000 : ℝ)|=(3110421543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3363614149/5000000000 : ℝ)*x 0 + (26667617/80000000 : ℝ)*x 1 + (2700241027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3363614149/5000000000 : ℝ)^65 ≤ (59104344389277/100000000000000 : ℝ)^49 := by
    have hnat : (3363614149 : ℕ)^65*100000000000000^49 ≤ 59104344389277^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3363614149 5000000000 59104344389277 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26667617/80000000 : ℝ)^65 ≤ (931460776801/4000000000000 : ℝ)^49 := by
    have hnat : (26667617 : ℕ)^65*4000000000000^49 ≤ 931460776801^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26667617 80000000 931460776801 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700241027/10000000000 : ℝ)^65 ≤ (17609136180409/100000000000000 : ℝ)^49 := by
    have hnat : (2700241027 : ℕ)^65*100000000000000^49 ≤ 17609136180409^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700241027 10000000000 17609136180409 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3363614149/5000000000 : ℝ), (26667617/80000000 : ℝ), (2700241027/10000000000 : ℝ)] ![(59104344389277/100000000000000 : ℝ), (931460776801/4000000000000 : ℝ), (17609136180409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3363614149/5000000000 : ℝ)|^65 ≤ (59104344389277/100000000000000 : ℝ)^49
        have hw : |(3363614149/5000000000 : ℝ)|=(3363614149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26667617/80000000 : ℝ)|^65 ≤ (931460776801/4000000000000 : ℝ)^49
        have hw : |(26667617/80000000 : ℝ)|=(26667617/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700241027/10000000000 : ℝ)|^65 ≤ (17609136180409/100000000000000 : ℝ)^49
        have hw : |(2700241027/10000000000 : ℝ)|=(2700241027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1245882007/2000000000 : ℝ)*x 0 + (-3767467187/10000000000 : ℝ)*x 1 + (-57721931/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1245882007/2000000000 : ℝ)^65 ≤ (26686864393201/50000000000000 : ℝ)^49 := by
    have hnat : (1245882007 : ℕ)^65*50000000000000^49 ≤ 26686864393201^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245882007 2000000000 26686864393201 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3767467187/10000000000 : ℝ)^65 ≤ (13695776477583/50000000000000 : ℝ)^49 := by
    have hnat : (3767467187 : ℕ)^65*50000000000000^49 ≤ 13695776477583^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767467187 10000000000 13695776477583 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57721931/200000000 : ℝ)^65 ≤ (4808679560261/25000000000000 : ℝ)^49 := by
    have hnat : (57721931 : ℕ)^65*25000000000000^49 ≤ 4808679560261^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57721931 200000000 4808679560261 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1245882007/2000000000 : ℝ), (-3767467187/10000000000 : ℝ), (-57721931/200000000 : ℝ)] ![(26686864393201/50000000000000 : ℝ), (13695776477583/50000000000000 : ℝ), (4808679560261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1245882007/2000000000 : ℝ)|^65 ≤ (26686864393201/50000000000000 : ℝ)^49
        have hw : |(1245882007/2000000000 : ℝ)|=(1245882007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3767467187/10000000000 : ℝ)|^65 ≤ (13695776477583/50000000000000 : ℝ)^49
        have hw : |(-3767467187/10000000000 : ℝ)|=(3767467187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57721931/200000000 : ℝ)|^65 ≤ (4808679560261/25000000000000 : ℝ)^49
        have hw : |(-57721931/200000000 : ℝ)|=(57721931/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (910115301/2500000000 : ℝ)*x 0 + (-10637743/39062500 : ℝ)*x 1 + (6460673671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910115301/2500000000 : ℝ)^65 ≤ (13086711984991/50000000000000 : ℝ)^49 := by
    have hnat : (910115301 : ℕ)^65*50000000000000^49 ≤ 13086711984991^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910115301 2500000000 13086711984991 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10637743/39062500 : ℝ)^65 ≤ (890428144751/5000000000000 : ℝ)^49 := by
    have hnat : (10637743 : ℕ)^65*5000000000000^49 ≤ 890428144751^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10637743 39062500 890428144751 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6460673671/10000000000 : ℝ)^65 ≤ (2240720524973/4000000000000 : ℝ)^49 := by
    have hnat : (6460673671 : ℕ)^65*4000000000000^49 ≤ 2240720524973^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6460673671 10000000000 2240720524973 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(910115301/2500000000 : ℝ), (-10637743/39062500 : ℝ), (6460673671/10000000000 : ℝ)] ![(13086711984991/50000000000000 : ℝ), (890428144751/5000000000000 : ℝ), (2240720524973/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(910115301/2500000000 : ℝ)|^65 ≤ (13086711984991/50000000000000 : ℝ)^49
        have hw : |(910115301/2500000000 : ℝ)|=(910115301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10637743/39062500 : ℝ)|^65 ≤ (890428144751/5000000000000 : ℝ)^49
        have hw : |(-10637743/39062500 : ℝ)|=(10637743/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6460673671/10000000000 : ℝ)|^65 ≤ (2240720524973/4000000000000 : ℝ)^49
        have hw : |(6460673671/10000000000 : ℝ)|=(6460673671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-9001499/400000000 : ℝ)*x 0 + (-6528777243/10000000000 : ℝ)*x 1 + (5250634249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9001499/400000000 : ℝ)^65 ≤ (651951985609/100000000000000 : ℝ)^49 := by
    have hnat : (9001499 : ℕ)^65*100000000000000^49 ≤ 651951985609^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9001499 400000000 651951985609 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6528777243/10000000000 : ℝ)^65 ≤ (56802674169717/100000000000000 : ℝ)^49 := by
    have hnat : (6528777243 : ℕ)^65*100000000000000^49 ≤ 56802674169717^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6528777243 10000000000 56802674169717 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5250634249/10000000000 : ℝ)^65 ≤ (4254537383729/10000000000000 : ℝ)^49 := by
    have hnat : (5250634249 : ℕ)^65*10000000000000^49 ≤ 4254537383729^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250634249 10000000000 4254537383729 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9001499/400000000 : ℝ), (-6528777243/10000000000 : ℝ), (5250634249/10000000000 : ℝ)] ![(651951985609/100000000000000 : ℝ), (56802674169717/100000000000000 : ℝ), (4254537383729/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9001499/400000000 : ℝ)|^65 ≤ (651951985609/100000000000000 : ℝ)^49
        have hw : |(-9001499/400000000 : ℝ)|=(9001499/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6528777243/10000000000 : ℝ)|^65 ≤ (56802674169717/100000000000000 : ℝ)^49
        have hw : |(-6528777243/10000000000 : ℝ)|=(6528777243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5250634249/10000000000 : ℝ)|^65 ≤ (4254537383729/10000000000000 : ℝ)^49
        have hw : |(5250634249/10000000000 : ℝ)|=(5250634249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (212272923/312500000 : ℝ)*x 0 + (310085931/1000000000 : ℝ)*x 1 + (2856660337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212272923/312500000 : ℝ)^65 ≤ (2993449915707/5000000000000 : ℝ)^49 := by
    have hnat : (212272923 : ℕ)^65*5000000000000^49 ≤ 2993449915707^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212272923 312500000 2993449915707 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310085931/1000000000 : ℝ)^65 ≤ (4231217831721/20000000000000 : ℝ)^49 := by
    have hnat : (310085931 : ℕ)^65*20000000000000^49 ≤ 4231217831721^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310085931 1000000000 4231217831721 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856660337/10000000000 : ℝ)^65 ≤ (9487456253069/50000000000000 : ℝ)^49 := by
    have hnat : (2856660337 : ℕ)^65*50000000000000^49 ≤ 9487456253069^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856660337 10000000000 9487456253069 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212272923/312500000 : ℝ), (310085931/1000000000 : ℝ), (2856660337/10000000000 : ℝ)] ![(2993449915707/5000000000000 : ℝ), (4231217831721/20000000000000 : ℝ), (9487456253069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212272923/312500000 : ℝ)|^65 ≤ (2993449915707/5000000000000 : ℝ)^49
        have hw : |(212272923/312500000 : ℝ)|=(212272923/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(310085931/1000000000 : ℝ)|^65 ≤ (4231217831721/20000000000000 : ℝ)^49
        have hw : |(310085931/1000000000 : ℝ)|=(310085931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856660337/10000000000 : ℝ)|^65 ≤ (9487456253069/50000000000000 : ℝ)^49
        have hw : |(2856660337/10000000000 : ℝ)|=(2856660337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5413991291/10000000000 : ℝ)*x 0 + (-4004317091/10000000000 : ℝ)*x 1 + (-362130501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413991291/10000000000 : ℝ)^65 ≤ (22155057449967/50000000000000 : ℝ)^49 := by
    have hnat : (5413991291 : ℕ)^65*50000000000000^49 ≤ 22155057449967^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413991291 10000000000 22155057449967 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4004317091/10000000000 : ℝ)^65 ≤ (29699000639681/100000000000000 : ℝ)^49 := by
    have hnat : (4004317091 : ℕ)^65*100000000000000^49 ≤ 29699000639681^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4004317091 10000000000 29699000639681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362130501/1000000000 : ℝ)^65 ≤ (5198176887931/20000000000000 : ℝ)^49 := by
    have hnat : (362130501 : ℕ)^65*20000000000000^49 ≤ 5198176887931^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362130501 1000000000 5198176887931 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413991291/10000000000 : ℝ), (-4004317091/10000000000 : ℝ), (-362130501/1000000000 : ℝ)] ![(22155057449967/50000000000000 : ℝ), (29699000639681/100000000000000 : ℝ), (5198176887931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413991291/10000000000 : ℝ)|^65 ≤ (22155057449967/50000000000000 : ℝ)^49
        have hw : |(5413991291/10000000000 : ℝ)|=(5413991291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4004317091/10000000000 : ℝ)|^65 ≤ (29699000639681/100000000000000 : ℝ)^49
        have hw : |(-4004317091/10000000000 : ℝ)|=(4004317091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-362130501/1000000000 : ℝ)|^65 ≤ (5198176887931/20000000000000 : ℝ)^49
        have hw : |(-362130501/1000000000 : ℝ)|=(362130501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s5_s5_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (261872223/500000000 : ℝ)*x 0 + (-180185791/625000000 : ℝ)*x 1 + (2429561599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261872223/500000000 : ℝ)^65 ≤ (10600914576603/25000000000000 : ℝ)^49 := by
    have hnat : (261872223 : ℕ)^65*25000000000000^49 ≤ 10600914576603^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261872223 500000000 10600914576603 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180185791/625000000 : ℝ)^65 ≤ (19207105357199/100000000000000 : ℝ)^49 := by
    have hnat : (180185791 : ℕ)^65*100000000000000^49 ≤ 19207105357199^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180185791 625000000 19207105357199 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2429561599/5000000000 : ℝ)^65 ≤ (38389236326933/100000000000000 : ℝ)^49 := by
    have hnat : (2429561599 : ℕ)^65*100000000000000^49 ≤ 38389236326933^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429561599 5000000000 38389236326933 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261872223/500000000 : ℝ), (-180185791/625000000 : ℝ), (2429561599/5000000000 : ℝ)] ![(10600914576603/25000000000000 : ℝ), (19207105357199/100000000000000 : ℝ), (38389236326933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261872223/500000000 : ℝ)|^65 ≤ (10600914576603/25000000000000 : ℝ)^49
        have hw : |(261872223/500000000 : ℝ)|=(261872223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-180185791/625000000 : ℝ)|^65 ≤ (19207105357199/100000000000000 : ℝ)^49
        have hw : |(-180185791/625000000 : ℝ)|=(180185791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2429561599/5000000000 : ℝ)|^65 ≤ (38389236326933/100000000000000 : ℝ)^49
        have hw : |(2429561599/5000000000 : ℝ)|=(2429561599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301086_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((22163/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22163/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3589/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3589/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16593/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16593/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((528/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(528/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-9919/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9919/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1273/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1273/4000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (22163/50000 : ℝ) ^ (129/32 : ℝ) ≤ (940875709623832713/25000000000000000000 : ℝ) := by
    have hpowers : (22163/50000 : ℝ)^129 ≤ (940875709623832713/25000000000000000000 : ℝ)^32 := by
      have hnat : (22163 : ℕ)^129*25000000000000000000^32 ≤ 940875709623832713^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22163 50000 940875709623832713 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22163/50000 : ℝ)) (X := (940875709623832713/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (25940875709623832713/25000000000000000000 : ℝ) ≤ (126150819122587/125000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25940875709623832713/25000000000000000000 : ℝ)^32 ≤ (126150819122587/125000000000000 : ℝ)^129 := by
      have hnat : (25940875709623832713 : ℕ)^32*125000000000000^129 ≤ 126150819122587^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25940875709623832713 25000000000000000000 126150819122587 125000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (126150819122587/125000000000000 : ℝ)) (X := (25940875709623832713/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (13440875709623832713/12500000000000000000 : ℝ) ≤ (407266134718217/400000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13440875709623832713/12500000000000000000 : ℝ)^32 ≤ (407266134718217/400000000000000 : ℝ)^129 := by
      have hnat : (13440875709623832713 : ℕ)^32*400000000000000^129 ≤ 407266134718217^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13440875709623832713 12500000000000000000 407266134718217 400000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (407266134718217/400000000000000 : ℝ)) (X := (13440875709623832713/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1150819122587/55407500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(17917567629693/886520000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (22163/50000 : ℝ)) (alpha := (1150819122587/55407500000000 : ℝ)) (beta := (17917567629693/886520000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22163/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1150819122587/55407500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(17917567629693/886520000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (3589/5000 : ℝ) ^ (129/32 : ℝ) ≤ (13136628799378771331/50000000000000000000 : ℝ) := by
    have hpowers : (3589/5000 : ℝ)^129 ≤ (13136628799378771331/50000000000000000000 : ℝ)^32 := by
      have hnat : (3589 : ℕ)^129*50000000000000000000^32 ≤ 13136628799378771331^32*5000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3589 5000 13136628799378771331 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3589/5000 : ℝ)) (X := (13136628799378771331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (63136628799378771331/50000000000000000000 : ℝ) ≤ (2648936300861109/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (63136628799378771331/50000000000000000000 : ℝ)^32 ≤ (2648936300861109/2500000000000000 : ℝ)^129 := by
      have hnat : (63136628799378771331 : ℕ)^32*2500000000000000^129 ≤ 2648936300861109^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63136628799378771331 50000000000000000000 2648936300861109 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2648936300861109/2500000000000000 : ℝ)) (X := (63136628799378771331/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (38136628799378771331/25000000000000000000 : ℝ) ≤ (11104401137978767/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (38136628799378771331/25000000000000000000 : ℝ)^32 ≤ (11104401137978767/10000000000000000 : ℝ)^129 := by
      have hnat : (38136628799378771331 : ℕ)^32*10000000000000000^129 ≤ 11104401137978767^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38136628799378771331 25000000000000000000 11104401137978767 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11104401137978767/10000000000000000 : ℝ)) (X := (38136628799378771331/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(148936300861109/1794500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(508655934534331/7178000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (3589/5000 : ℝ)) (alpha := (148936300861109/1794500000000000 : ℝ)) (beta := (508655934534331/7178000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (3589/5000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(148936300861109/1794500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(508655934534331/7178000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (16593/25000 : ℝ) ^ (129/32 : ℝ) ≤ (19159168031621986871/100000000000000000000 : ℝ) := by
    have hpowers : (16593/25000 : ℝ)^129 ≤ (19159168031621986871/100000000000000000000 : ℝ)^32 := by
      have hnat : (16593 : ℕ)^129*100000000000000000000^32 ≤ 19159168031621986871^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16593 25000 19159168031621986871 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16593/25000 : ℝ)) (X := (19159168031621986871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (119159168031621986871/100000000000000000000 : ℝ) ≤ (2611105024116791/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (119159168031621986871/100000000000000000000 : ℝ)^32 ≤ (2611105024116791/2500000000000000 : ℝ)^129 := by
      have hnat : (119159168031621986871 : ℕ)^32*2500000000000000^129 ≤ 2611105024116791^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119159168031621986871 100000000000000000000 2611105024116791 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2611105024116791/2500000000000000 : ℝ)) (X := (119159168031621986871/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (69159168031621986871/50000000000000000000 : ℝ) ≤ (338685760534237/312500000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (69159168031621986871/50000000000000000000 : ℝ)^32 ≤ (338685760534237/312500000000000 : ℝ)^129 := by
      have hnat : (69159168031621986871 : ℕ)^32*312500000000000^129 ≤ 338685760534237^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69159168031621986871 50000000000000000000 338685760534237 312500000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (338685760534237/312500000000000 : ℝ)) (X := (69159168031621986871/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(111105024116791/1659300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6558737343807/110620000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (16593/25000 : ℝ)) (alpha := (111105024116791/1659300000000000 : ℝ)) (beta := (6558737343807/110620000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16593/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(111105024116791/1659300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6558737343807/110620000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-972188421/10000000000 : ℝ)*X 0 0+(-2920502841/5000000000 : ℝ)*X 0 1+(5610259679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((5685216337/10000000000 : ℝ)*X 2 0+(-1899054839/5000000000 : ℝ)*X 2 1+(-704066401/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-746146321/10000000000 : ℝ)*X 0 0+(-3431464113/5000000000 : ℝ)*X 0 1+(2320091411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((5930290867/10000000000 : ℝ)*X 1 0+(177625579/500000000 : ℝ)*X 1 1+(1740366353/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((5959779717/10000000000 : ℝ)*X 2 0+(-3552666893/10000000000 : ℝ)*X 2 1+(-861349083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((3500033871/10000000000 : ℝ)*X 0 0+(-2228546081/10000000000 : ℝ)*X 0 1+(86655033/125000000 : ℝ)*X 0 2+(3500033871/10000000000 : ℝ)*X 1 0+(-2228546081/10000000000 : ℝ)*X 1 1+(86655033/125000000 : ℝ)*X 1 2+(3500033871/10000000000 : ℝ)*X 2 0+(-2228546081/10000000000 : ℝ)*X 2 1+(86655033/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-5810841/200000000 : ℝ)*X 0 0+(-2775726537/5000000000 : ℝ)*X 0 1+(3110421543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((3363614149/5000000000 : ℝ)*X 1 0+(26667617/80000000 : ℝ)*X 1 1+(2700241027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((1245882007/2000000000 : ℝ)*X 2 0+(-3767467187/10000000000 : ℝ)*X 2 1+(-57721931/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((910115301/2500000000 : ℝ)*X 0 0+(-10637743/39062500 : ℝ)*X 0 1+(6460673671/10000000000 : ℝ)*X 0 2+(910115301/2500000000 : ℝ)*X 1 0+(-10637743/39062500 : ℝ)*X 1 1+(6460673671/10000000000 : ℝ)*X 1 2+(910115301/2500000000 : ℝ)*X 2 0+(-10637743/39062500 : ℝ)*X 2 1+(6460673671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-9001499/400000000 : ℝ)*X 0 0+(-6528777243/10000000000 : ℝ)*X 0 1+(5250634249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((212272923/312500000 : ℝ)*X 1 0+(310085931/1000000000 : ℝ)*X 1 1+(2856660337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((5413991291/10000000000 : ℝ)*X 2 0+(-4004317091/10000000000 : ℝ)*X 2 1+(-362130501/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((261872223/500000000 : ℝ)*X 0 0+(-180185791/625000000 : ℝ)*X 0 1+(2429561599/5000000000 : ℝ)*X 0 2+(261872223/500000000 : ℝ)*X 1 0+(-180185791/625000000 : ℝ)*X 1 1+(2429561599/5000000000 : ℝ)*X 1 2+(261872223/500000000 : ℝ)*X 2 0+(-180185791/625000000 : ℝ)*X 2 1+(2429561599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((528/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(528/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (79520765450864733062797577779/5945302320500000000000000000000000 : ℝ) := by norm_num
    linear_combination (16958820731/50000000000 : ℝ)*(base40) + (1364327/500000000000 : ℝ)*(base50) + (6190303/1000000000000 : ℝ)*(base60) + (3738542568811/1000000000000 : ℝ)*(major_s5_0) + (3738542568811/1000000000000 : ℝ)*(major_s5_1) + (3738542568811/1000000000000 : ℝ)*(major_s5_2) + (7488403/500000000000 : ℝ)*(sp_s5_0) + (348119843/1000000000000 : ℝ)*(sp_s5_2) + (4949662687181/1000000000000 : ℝ)*(sp_s5_7) + (4949740579637/1000000000000 : ℝ)*(sp_s5_8) + (4949374590613/1000000000000 : ℝ)*(sp_s5_9) + (1263670049759/500000000000 : ℝ)*(sp_s5_13) + (17869181/1000000000000 : ℝ)*(sp_s5_16) + (1258313/20000000000 : ℝ)*(sp_s5_21) + (1263670049759/500000000000 : ℝ)*(f.failure) + (4949740579637/1000000000000 : ℝ)*(f.sum) + (24548538167589873893/119104554000000000000000000000000 : ℝ)*base63 + (10374550536379/22124000000000000000000000 : ℝ)*base65 + (200437498525699/1794500000000000000000000000 : ℝ)*base67 + (470162271605491/1659300000000000000000000000 : ℝ)*base69 + (628674598439264173/2451671060000000000000000000000 : ℝ)*base71 + (47862486231239/886520000000000000000000000 : ℝ)*base73 + (2132093390974559/7178000000000000000000000000 : ℝ)*base74 + (1570823614647/55407500000000000000000000 : ℝ)*base76 + (797132889272833877/2149811000000000000000000000000 : ℝ)*base79 + (79/12500000000000000 : ℝ)*base87 + (79/12500000000000000 : ℝ)*base89 + (79/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-9919/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9919/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (70704850199208621386236606851/5945302320500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1460137/250000000000 : ℝ)*(base39) + (318443779499/250000000000 : ℝ)*(base40) + (78714878979/200000000000 : ℝ)*(base60) + (5637438544089/1000000000000 : ℝ)*(major_s5_0) + (5637438544089/1000000000000 : ℝ)*(major_s5_1) + (5637438544089/1000000000000 : ℝ)*(major_s5_2) + (12757547/500000000000 : ℝ)*(sp_s5_0) + (522609/3125000000 : ℝ)*(sp_s5_13) + (932976311559/125000000000 : ℝ)*(sp_s5_14) + (7463643874761/1000000000000 : ℝ)*(sp_s5_15) + (7463836007567/1000000000000 : ℝ)*(sp_s5_16) + (3810838774473/1000000000000 : ℝ)*(sp_s5_20) + (96066403/500000000000 : ℝ)*(sp_s5_22) + (3888383/125000000000 : ℝ)*(sp_s5_27) + (3811037116417/1000000000000 : ℝ)*(f.failure) + (7463836007567/1000000000000 : ℝ)*(f.sum) + (11435777387068473931/39701518000000000000000000000000 : ℝ)*base62 + (20715791181683/22124000000000000000000000 : ℝ)*base64 + (1177705854514851/1794500000000000000000000000 : ℝ)*base67 + (143129756827727/553100000000000000000000000 : ℝ)*base68 + (2209926463518518607/2451671060000000000000000000000 : ℝ)*base70 + (840190412818229/886520000000000000000000000 : ℝ)*base73 + (496808068344859/7178000000000000000000000000 : ℝ)*base75 + (121618033821677/221630000000000000000000000 : ℝ)*base76 + (2037180166448518023/2149811000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (7923/25000000000000000 : ℝ)*base86 + (7923/25000000000000000 : ℝ)*base88 + (7923/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1273/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1273/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9267830961353140352966619699/2378120928200000000000000000000000 : ℝ) := by norm_num
    linear_combination (1599149/1000000000000 : ℝ)*(base39) + (1363244655517/1000000000000 : ℝ)*(base40) + (72189/1000000000000 : ℝ)*(base50) + (5363472256923/1000000000000 : ℝ)*(major_s5_0) + (5363472256923/1000000000000 : ℝ)*(major_s5_1) + (5363472256923/1000000000000 : ℝ)*(major_s5_2) + (300481/250000000000 : ℝ)*(sp_s5_0) + (2400391/1000000000000 : ℝ)*(sp_s5_2) + (2741991/125000000000 : ℝ)*(sp_s5_7) + (39275293/500000000000 : ℝ)*(sp_s5_15) + (355054521163/50000000000 : ℝ)*(sp_s5_21) + (284041400421/40000000000 : ℝ)*(sp_s5_22) + (88763889509/12500000000 : ℝ)*(sp_s5_23) + (3625829653689/1000000000000 : ℝ)*(sp_s5_27) + (3625829653689/1000000000000 : ℝ)*(f.failure) + (7101113561111/1000000000000 : ℝ)*(f.sum) + (11796075499154629183/39701518000000000000000000000000 : ℝ)*base63 + (31308556769859/110620000000000000000000000 : ℝ)*base65 + (918326097406693/1794500000000000000000000000 : ℝ)*base66 + (176477375647951/553100000000000000000000000 : ℝ)*base69 + (1374182839070893609/2451671060000000000000000000000 : ℝ)*base71 + (35807125399549/886520000000000000000000000 : ℝ)*base72 + (4000115470982913/7178000000000000000000000000 : ℝ)*base75 + (4506015477233/22163000000000000000000000 : ℝ)*base77 + (1379777635310340939/2149811000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (2091/25000000000000000 : ℝ)*base86 + (2091/25000000000000000 : ℝ)*base88 + (2091/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((22163/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22163/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3589/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3589/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16593/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16593/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((528/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(528/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-9919/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9919/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1273/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1273/4000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301086_s5 p hpa hpb X hX hprev4

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:31:37.641982+00:00
-- url     : https://prove2.me/submissions/86d8b535-fd7e-499f-8680-59b424ff5852

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
theorem collision_support_c301054_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-292378367/10000000000 : ℝ)*x 0 + (178236643/400000000 : ℝ)*x 1 + (-57720039/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292378367/10000000000 : ℝ)^65 ≤ (461316936391/50000000000000 : ℝ)^49 := by
    have hnat : (292378367 : ℕ)^65*50000000000000^49 ≤ 461316936391^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292378367 10000000000 461316936391 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178236643/400000000 : ℝ)^65 ≤ (342219054457/1000000000000 : ℝ)^49 := by
    have hnat : (178236643 : ℕ)^65*1000000000000^49 ≤ 342219054457^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178236643 400000000 342219054457 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57720039/80000000 : ℝ)^65 ≤ (64855460672721/100000000000000 : ℝ)^49 := by
    have hnat : (57720039 : ℕ)^65*100000000000000^49 ≤ 64855460672721^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57720039 80000000 64855460672721 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-292378367/10000000000 : ℝ), (178236643/400000000 : ℝ), (-57720039/80000000 : ℝ)] ![(461316936391/50000000000000 : ℝ), (342219054457/1000000000000 : ℝ), (64855460672721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-292378367/10000000000 : ℝ)|^65 ≤ (461316936391/50000000000000 : ℝ)^49
        have hw : |(-292378367/10000000000 : ℝ)|=(292378367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(178236643/400000000 : ℝ)|^65 ≤ (342219054457/1000000000000 : ℝ)^49
        have hw : |(178236643/400000000 : ℝ)|=(178236643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57720039/80000000 : ℝ)|^65 ≤ (64855460672721/100000000000000 : ℝ)^49
        have hw : |(-57720039/80000000 : ℝ)|=(57720039/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2922930147/5000000000 : ℝ)*x 0 + (-1098791/6250000 : ℝ)*x 1 + (-1020777443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2922930147/5000000000 : ℝ)^65 ≤ (12264710932709/25000000000000 : ℝ)^49 := by
    have hnat : (2922930147 : ℕ)^65*25000000000000^49 ≤ 12264710932709^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2922930147 5000000000 12264710932709 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098791/6250000 : ℝ)^65 ≤ (4982943027963/50000000000000 : ℝ)^49 := by
    have hnat : (1098791 : ℕ)^65*50000000000000^49 ≤ 4982943027963^49*6250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098791 6250000 4982943027963 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020777443/2000000000 : ℝ)^65 ≤ (5121908774119/12500000000000 : ℝ)^49 := by
    have hnat : (1020777443 : ℕ)^65*12500000000000^49 ≤ 5121908774119^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020777443 2000000000 5121908774119 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2922930147/5000000000 : ℝ), (-1098791/6250000 : ℝ), (-1020777443/2000000000 : ℝ)] ![(12264710932709/25000000000000 : ℝ), (4982943027963/50000000000000 : ℝ), (5121908774119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2922930147/5000000000 : ℝ)|^65 ≤ (12264710932709/25000000000000 : ℝ)^49
        have hw : |(2922930147/5000000000 : ℝ)|=(2922930147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098791/6250000 : ℝ)|^65 ≤ (4982943027963/50000000000000 : ℝ)^49
        have hw : |(-1098791/6250000 : ℝ)|=(1098791/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020777443/2000000000 : ℝ)|^65 ≤ (5121908774119/12500000000000 : ℝ)^49
        have hw : |(-1020777443/2000000000 : ℝ)|=(1020777443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2822713177/5000000000 : ℝ)*x 0 + (2794848671/5000000000 : ℝ)*x 1 + (66859131/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2822713177/5000000000 : ℝ)^65 ≤ (46840134432729/100000000000000 : ℝ)^49 := by
    have hnat : (2822713177 : ℕ)^65*100000000000000^49 ≤ 46840134432729^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822713177 5000000000 46840134432729 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794848671/5000000000 : ℝ)^65 ≤ (5778469843357/12500000000000 : ℝ)^49 := by
    have hnat : (2794848671 : ℕ)^65*12500000000000^49 ≤ 5778469843357^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794848671 5000000000 5778469843357 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66859131/500000000 : ℝ)^65 ≤ (3466053400093/50000000000000 : ℝ)^49 := by
    have hnat : (66859131 : ℕ)^65*50000000000000^49 ≤ 3466053400093^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66859131 500000000 3466053400093 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2822713177/5000000000 : ℝ), (2794848671/5000000000 : ℝ), (66859131/500000000 : ℝ)] ![(46840134432729/100000000000000 : ℝ), (5778469843357/12500000000000 : ℝ), (3466053400093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2822713177/5000000000 : ℝ)|^65 ≤ (46840134432729/100000000000000 : ℝ)^49
        have hw : |(2822713177/5000000000 : ℝ)|=(2822713177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794848671/5000000000 : ℝ)|^65 ≤ (5778469843357/12500000000000 : ℝ)^49
        have hw : |(2794848671/5000000000 : ℝ)|=(2794848671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66859131/500000000 : ℝ)|^65 ≤ (3466053400093/50000000000000 : ℝ)^49
        have hw : |(66859131/500000000 : ℝ)|=(66859131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5520451417/10000000000 : ℝ)*x 0 + (2739789879/5000000000 : ℝ)*x 1 + (-424164317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520451417/10000000000 : ℝ)^65 ≤ (22734813826619/50000000000000 : ℝ)^49 := by
    have hnat : (5520451417 : ℕ)^65*50000000000000^49 ≤ 22734813826619^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520451417 10000000000 22734813826619 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739789879/5000000000 : ℝ)^65 ≤ (5627950204151/12500000000000 : ℝ)^49 := by
    have hnat : (2739789879 : ℕ)^65*12500000000000^49 ≤ 5627950204151^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739789879 5000000000 5627950204151 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424164317/2500000000 : ℝ)^65 ≤ (594173168427/6250000000000 : ℝ)^49 := by
    have hnat : (424164317 : ℕ)^65*6250000000000^49 ≤ 594173168427^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424164317 2500000000 594173168427 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520451417/10000000000 : ℝ), (2739789879/5000000000 : ℝ), (-424164317/2500000000 : ℝ)] ![(22734813826619/50000000000000 : ℝ), (5627950204151/12500000000000 : ℝ), (594173168427/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520451417/10000000000 : ℝ)|^65 ≤ (22734813826619/50000000000000 : ℝ)^49
        have hw : |(5520451417/10000000000 : ℝ)|=(5520451417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739789879/5000000000 : ℝ)|^65 ≤ (5627950204151/12500000000000 : ℝ)^49
        have hw : |(2739789879/5000000000 : ℝ)|=(2739789879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424164317/2500000000 : ℝ)|^65 ≤ (594173168427/6250000000000 : ℝ)^49
        have hw : |(-424164317/2500000000 : ℝ)|=(424164317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-11837/2500000 : ℝ)*x 0 + (1902400987/10000000000 : ℝ)*x 1 + (-914751303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11837/2500000 : ℝ)^65 ≤ (82454898197/100000000000000 : ℝ)^49 := by
    have hnat : (11837 : ℕ)^65*100000000000000^49 ≤ 82454898197^49*2500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11837 2500000 82454898197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902400987/10000000000 : ℝ)^65 ≤ (2213105510333/20000000000000 : ℝ)^49 := by
    have hnat : (1902400987 : ℕ)^65*20000000000000^49 ≤ 2213105510333^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902400987 10000000000 2213105510333 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914751303/1000000000 : ℝ)^65 ≤ (17770403508941/20000000000000 : ℝ)^49 := by
    have hnat : (914751303 : ℕ)^65*20000000000000^49 ≤ 17770403508941^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914751303 1000000000 17770403508941 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11837/2500000 : ℝ), (1902400987/10000000000 : ℝ), (-914751303/1000000000 : ℝ)] ![(82454898197/100000000000000 : ℝ), (2213105510333/20000000000000 : ℝ), (17770403508941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11837/2500000 : ℝ)|^65 ≤ (82454898197/100000000000000 : ℝ)^49
        have hw : |(-11837/2500000 : ℝ)|=(11837/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1902400987/10000000000 : ℝ)|^65 ≤ (2213105510333/20000000000000 : ℝ)^49
        have hw : |(1902400987/10000000000 : ℝ)|=(1902400987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-914751303/1000000000 : ℝ)|^65 ≤ (17770403508941/20000000000000 : ℝ)^49
        have hw : |(-914751303/1000000000 : ℝ)|=(914751303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3917638149/10000000000 : ℝ)*x 0 + (-1177119417/10000000000 : ℝ)*x 1 + (-7252025859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3917638149/10000000000 : ℝ)^65 ≤ (7212308762743/25000000000000 : ℝ)^49 := by
    have hnat : (3917638149 : ℕ)^65*25000000000000^49 ≤ 7212308762743^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3917638149 10000000000 7212308762743 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177119417/10000000000 : ℝ)^65 ≤ (1463372835401/25000000000000 : ℝ)^49 := by
    have hnat : (1177119417 : ℕ)^65*25000000000000^49 ≤ 1463372835401^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177119417 10000000000 1463372835401 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7252025859/10000000000 : ℝ)^65 ≤ (32648636793639/50000000000000 : ℝ)^49 := by
    have hnat : (7252025859 : ℕ)^65*50000000000000^49 ≤ 32648636793639^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7252025859 10000000000 32648636793639 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3917638149/10000000000 : ℝ), (-1177119417/10000000000 : ℝ), (-7252025859/10000000000 : ℝ)] ![(7212308762743/25000000000000 : ℝ), (1463372835401/25000000000000 : ℝ), (32648636793639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3917638149/10000000000 : ℝ)|^65 ≤ (7212308762743/25000000000000 : ℝ)^49
        have hw : |(3917638149/10000000000 : ℝ)|=(3917638149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1177119417/10000000000 : ℝ)|^65 ≤ (1463372835401/25000000000000 : ℝ)^49
        have hw : |(-1177119417/10000000000 : ℝ)|=(1177119417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7252025859/10000000000 : ℝ)|^65 ≤ (32648636793639/50000000000000 : ℝ)^49
        have hw : |(-7252025859/10000000000 : ℝ)|=(7252025859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3427594647/10000000000 : ℝ)*x 0 + (7952119369/10000000000 : ℝ)*x 1 + (26674629/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3427594647/10000000000 : ℝ)^65 ≤ (24162912334929/100000000000000 : ℝ)^49 := by
    have hnat : (3427594647 : ℕ)^65*100000000000000^49 ≤ 24162912334929^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3427594647 10000000000 24162912334929 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7952119369/10000000000 : ℝ)^65 ≤ (14757660107463/20000000000000 : ℝ)^49 := by
    have hnat : (7952119369 : ℕ)^65*20000000000000^49 ≤ 14757660107463^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7952119369 10000000000 14757660107463 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26674629/500000000 : ℝ)^65 ≤ (2048787120099/100000000000000 : ℝ)^49 := by
    have hnat : (26674629 : ℕ)^65*100000000000000^49 ≤ 2048787120099^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26674629 500000000 2048787120099 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3427594647/10000000000 : ℝ), (7952119369/10000000000 : ℝ), (26674629/500000000 : ℝ)] ![(24162912334929/100000000000000 : ℝ), (14757660107463/20000000000000 : ℝ), (2048787120099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3427594647/10000000000 : ℝ)|^65 ≤ (24162912334929/100000000000000 : ℝ)^49
        have hw : |(3427594647/10000000000 : ℝ)|=(3427594647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7952119369/10000000000 : ℝ)|^65 ≤ (14757660107463/20000000000000 : ℝ)^49
        have hw : |(7952119369/10000000000 : ℝ)|=(7952119369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26674629/500000000 : ℝ)|^65 ≤ (2048787120099/100000000000000 : ℝ)^49
        have hw : |(26674629/500000000 : ℝ)|=(26674629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (754802799/2000000000 : ℝ)*x 0 + (304778661/400000000 : ℝ)*x 1 + (-5435097/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (754802799/2000000000 : ℝ)^65 ≤ (13727356120143/50000000000000 : ℝ)^49 := by
    have hnat : (754802799 : ℕ)^65*50000000000000^49 ≤ 13727356120143^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754802799 2000000000 13727356120143 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (304778661/400000000 : ℝ)^65 ≤ (3486095865479/5000000000000 : ℝ)^49 := by
    have hnat : (304778661 : ℕ)^65*5000000000000^49 ≤ 3486095865479^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304778661 400000000 3486095865479 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435097/80000000 : ℝ)^65 ≤ (282337043911/10000000000000 : ℝ)^49 := by
    have hnat : (5435097 : ℕ)^65*10000000000000^49 ≤ 282337043911^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435097 80000000 282337043911 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(754802799/2000000000 : ℝ), (304778661/400000000 : ℝ), (-5435097/80000000 : ℝ)] ![(13727356120143/50000000000000 : ℝ), (3486095865479/5000000000000 : ℝ), (282337043911/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(754802799/2000000000 : ℝ)|^65 ≤ (13727356120143/50000000000000 : ℝ)^49
        have hw : |(754802799/2000000000 : ℝ)|=(754802799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(304778661/400000000 : ℝ)|^65 ≤ (3486095865479/5000000000000 : ℝ)^49
        have hw : |(304778661/400000000 : ℝ)|=(304778661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5435097/80000000 : ℝ)|^65 ≤ (282337043911/10000000000000 : ℝ)^49
        have hw : |(-5435097/80000000 : ℝ)|=(5435097/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5320061/10000000000 : ℝ)*x 0 + (1043314869/5000000000 : ℝ)*x 1 + (-9041328351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5320061/10000000000 : ℝ)^65 ≤ (453762037/10000000000000 : ℝ)^49 := by
    have hnat : (5320061 : ℕ)^65*10000000000000^49 ≤ 453762037^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5320061 10000000000 453762037 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043314869/5000000000 : ℝ)^65 ≤ (12509025558521/100000000000000 : ℝ)^49 := by
    have hnat : (1043314869 : ℕ)^65*100000000000000^49 ≤ 12509025558521^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043314869 5000000000 12509025558521 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9041328351/10000000000 : ℝ)^65 ≤ (87486436810129/100000000000000 : ℝ)^49 := by
    have hnat : (9041328351 : ℕ)^65*100000000000000^49 ≤ 87486436810129^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9041328351 10000000000 87486436810129 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5320061/10000000000 : ℝ), (1043314869/5000000000 : ℝ), (-9041328351/10000000000 : ℝ)] ![(453762037/10000000000000 : ℝ), (12509025558521/100000000000000 : ℝ), (87486436810129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5320061/10000000000 : ℝ)|^65 ≤ (453762037/10000000000000 : ℝ)^49
        have hw : |(5320061/10000000000 : ℝ)|=(5320061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043314869/5000000000 : ℝ)|^65 ≤ (12509025558521/100000000000000 : ℝ)^49
        have hw : |(1043314869/5000000000 : ℝ)|=(1043314869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9041328351/10000000000 : ℝ)|^65 ≤ (87486436810129/100000000000000 : ℝ)^49
        have hw : |(-9041328351/10000000000 : ℝ)|=(9041328351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1692652293/5000000000 : ℝ)*x 0 + (-436333567/2000000000 : ℝ)*x 1 + (-1763896001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1692652293/5000000000 : ℝ)^65 ≤ (23768239485901/100000000000000 : ℝ)^49 := by
    have hnat : (1692652293 : ℕ)^65*100000000000000^49 ≤ 23768239485901^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692652293 5000000000 23768239485901 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436333567/2000000000 : ℝ)^65 ≤ (829397825121/6250000000000 : ℝ)^49 := by
    have hnat : (436333567 : ℕ)^65*6250000000000^49 ≤ 829397825121^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436333567 2000000000 829397825121 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763896001/2500000000 : ℝ)^65 ≤ (31480697647947/50000000000000 : ℝ)^49 := by
    have hnat : (1763896001 : ℕ)^65*50000000000000^49 ≤ 31480697647947^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763896001 2500000000 31480697647947 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1692652293/5000000000 : ℝ), (-436333567/2000000000 : ℝ), (-1763896001/2500000000 : ℝ)] ![(23768239485901/100000000000000 : ℝ), (829397825121/6250000000000 : ℝ), (31480697647947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1692652293/5000000000 : ℝ)|^65 ≤ (23768239485901/100000000000000 : ℝ)^49
        have hw : |(1692652293/5000000000 : ℝ)|=(1692652293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436333567/2000000000 : ℝ)|^65 ≤ (829397825121/6250000000000 : ℝ)^49
        have hw : |(-436333567/2000000000 : ℝ)|=(436333567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1763896001/2500000000 : ℝ)|^65 ≤ (31480697647947/50000000000000 : ℝ)^49
        have hw : |(-1763896001/2500000000 : ℝ)|=(1763896001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7876961469/10000000000 : ℝ)*x 0 + (792410663/2500000000 : ℝ)*x 1 + (275164011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7876961469/10000000000 : ℝ)^65 ≤ (9108076797087/12500000000000 : ℝ)^49 := by
    have hnat : (7876961469 : ℕ)^65*12500000000000^49 ≤ 9108076797087^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7876961469 10000000000 9108076797087 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (792410663/2500000000 : ℝ)^65 ≤ (21780853341967/100000000000000 : ℝ)^49 := by
    have hnat : (792410663 : ℕ)^65*100000000000000^49 ≤ 21780853341967^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792410663 2500000000 21780853341967 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275164011/2500000000 : ℝ)^65 ≤ (5354532271647/100000000000000 : ℝ)^49 := by
    have hnat : (275164011 : ℕ)^65*100000000000000^49 ≤ 5354532271647^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275164011 2500000000 5354532271647 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7876961469/10000000000 : ℝ), (792410663/2500000000 : ℝ), (275164011/2500000000 : ℝ)] ![(9108076797087/12500000000000 : ℝ), (21780853341967/100000000000000 : ℝ), (5354532271647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7876961469/10000000000 : ℝ)|^65 ≤ (9108076797087/12500000000000 : ℝ)^49
        have hw : |(7876961469/10000000000 : ℝ)|=(7876961469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(792410663/2500000000 : ℝ)|^65 ≤ (21780853341967/100000000000000 : ℝ)^49
        have hw : |(792410663/2500000000 : ℝ)|=(792410663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275164011/2500000000 : ℝ)|^65 ≤ (5354532271647/100000000000000 : ℝ)^49
        have hw : |(275164011/2500000000 : ℝ)|=(275164011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (732089539/1000000000 : ℝ)*x 0 + (1913908677/5000000000 : ℝ)*x 1 + (-592364959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732089539/1000000000 : ℝ)^65 ≤ (13224225995671/20000000000000 : ℝ)^49 := by
    have hnat : (732089539 : ℕ)^65*20000000000000^49 ≤ 13224225995671^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732089539 1000000000 13224225995671 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913908677/5000000000 : ℝ)^65 ≤ (27975123299633/100000000000000 : ℝ)^49 := by
    have hnat : (1913908677 : ℕ)^65*100000000000000^49 ≤ 27975123299633^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913908677 5000000000 27975123299633 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592364959/5000000000 : ℝ)^65 ≤ (2951873357481/50000000000000 : ℝ)^49 := by
    have hnat : (592364959 : ℕ)^65*50000000000000^49 ≤ 2951873357481^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592364959 5000000000 2951873357481 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(732089539/1000000000 : ℝ), (1913908677/5000000000 : ℝ), (-592364959/5000000000 : ℝ)] ![(13224225995671/20000000000000 : ℝ), (27975123299633/100000000000000 : ℝ), (2951873357481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(732089539/1000000000 : ℝ)|^65 ≤ (13224225995671/20000000000000 : ℝ)^49
        have hw : |(732089539/1000000000 : ℝ)|=(732089539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1913908677/5000000000 : ℝ)|^65 ≤ (27975123299633/100000000000000 : ℝ)^49
        have hw : |(1913908677/5000000000 : ℝ)|=(1913908677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-592364959/5000000000 : ℝ)|^65 ≤ (2951873357481/50000000000000 : ℝ)^49
        have hw : |(-592364959/5000000000 : ℝ)|=(592364959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (36315263/10000000000 : ℝ)*x 0 + (390925423/625000000 : ℝ)*x 1 + (-5594406871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36315263/10000000000 : ℝ)^65 ≤ (11598814959/20000000000000 : ℝ)^49 := by
    have hnat : (36315263 : ℕ)^65*20000000000000^49 ≤ 11598814959^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36315263 10000000000 11598814959 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390925423/625000000 : ℝ)^65 ≤ (26831286765483/50000000000000 : ℝ)^49 := by
    have hnat : (390925423 : ℕ)^65*50000000000000^49 ≤ 26831286765483^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390925423 625000000 26831286765483 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5594406871/10000000000 : ℝ)^65 ≤ (11569858095719/25000000000000 : ℝ)^49 := by
    have hnat : (5594406871 : ℕ)^65*25000000000000^49 ≤ 11569858095719^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594406871 10000000000 11569858095719 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36315263/10000000000 : ℝ), (390925423/625000000 : ℝ), (-5594406871/10000000000 : ℝ)] ![(11598814959/20000000000000 : ℝ), (26831286765483/50000000000000 : ℝ), (11569858095719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36315263/10000000000 : ℝ)|^65 ≤ (11598814959/20000000000000 : ℝ)^49
        have hw : |(36315263/10000000000 : ℝ)|=(36315263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(390925423/625000000 : ℝ)|^65 ≤ (26831286765483/50000000000000 : ℝ)^49
        have hw : |(390925423/625000000 : ℝ)|=(390925423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5594406871/10000000000 : ℝ)|^65 ≤ (11569858095719/25000000000000 : ℝ)^49
        have hw : |(-5594406871/10000000000 : ℝ)|=(5594406871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7907401637/10000000000 : ℝ)*x 0 + (-1713404097/10000000000 : ℝ)*x 1 + (-1322343507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7907401637/10000000000 : ℝ)^65 ≤ (73238377076231/100000000000000 : ℝ)^49 := by
    have hnat : (7907401637 : ℕ)^65*100000000000000^49 ≤ 73238377076231^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7907401637 10000000000 73238377076231 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713404097/10000000000 : ℝ)^65 ≤ (1203930968289/12500000000000 : ℝ)^49 := by
    have hnat : (1713404097 : ℕ)^65*12500000000000^49 ≤ 1203930968289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713404097 10000000000 1203930968289 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322343507/5000000000 : ℝ)^65 ≤ (26765898681/156250000000 : ℝ)^49 := by
    have hnat : (1322343507 : ℕ)^65*156250000000^49 ≤ 26765898681^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322343507 5000000000 26765898681 156250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7907401637/10000000000 : ℝ), (-1713404097/10000000000 : ℝ), (-1322343507/5000000000 : ℝ)] ![(73238377076231/100000000000000 : ℝ), (1203930968289/12500000000000 : ℝ), (26765898681/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7907401637/10000000000 : ℝ)|^65 ≤ (73238377076231/100000000000000 : ℝ)^49
        have hw : |(7907401637/10000000000 : ℝ)|=(7907401637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713404097/10000000000 : ℝ)|^65 ≤ (1203930968289/12500000000000 : ℝ)^49
        have hw : |(-1713404097/10000000000 : ℝ)|=(1713404097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322343507/5000000000 : ℝ)|^65 ≤ (26765898681/156250000000 : ℝ)^49
        have hw : |(-1322343507/5000000000 : ℝ)|=(1322343507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3462442941/10000000000 : ℝ)*x 0 + (3435849947/5000000000 : ℝ)*x 1 + (2358612397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3462442941/10000000000 : ℝ)^65 ≤ (12244666362639/50000000000000 : ℝ)^49 := by
    have hnat : (3462442941 : ℕ)^65*50000000000000^49 ≤ 12244666362639^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462442941 10000000000 12244666362639 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3435849947/5000000000 : ℝ)^65 ≤ (474953052419/781250000000 : ℝ)^49 := by
    have hnat : (3435849947 : ℕ)^65*781250000000^49 ≤ 474953052419^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3435849947 5000000000 474953052419 781250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2358612397/10000000000 : ℝ)^65 ≤ (73583382749/500000000000 : ℝ)^49 := by
    have hnat : (2358612397 : ℕ)^65*500000000000^49 ≤ 73583382749^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358612397 10000000000 73583382749 500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3462442941/10000000000 : ℝ), (3435849947/5000000000 : ℝ), (2358612397/10000000000 : ℝ)] ![(12244666362639/50000000000000 : ℝ), (474953052419/781250000000 : ℝ), (73583382749/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3462442941/10000000000 : ℝ)|^65 ≤ (12244666362639/50000000000000 : ℝ)^49
        have hw : |(3462442941/10000000000 : ℝ)|=(3462442941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3435849947/5000000000 : ℝ)|^65 ≤ (474953052419/781250000000 : ℝ)^49
        have hw : |(3435849947/5000000000 : ℝ)|=(3435849947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2358612397/10000000000 : ℝ)|^65 ≤ (73583382749/500000000000 : ℝ)^49
        have hw : |(2358612397/10000000000 : ℝ)|=(2358612397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301054_s2_s2_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3618217859/5000000000 : ℝ)*x 0 + (3733255781/10000000000 : ℝ)*x 1 + (-732659257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3618217859/5000000000 : ℝ)^65 ≤ (65111128965003/100000000000000 : ℝ)^49 := by
    have hnat : (3618217859 : ℕ)^65*100000000000000^49 ≤ 65111128965003^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3618217859 5000000000 65111128965003 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733255781/10000000000 : ℝ)^65 ≤ (27062087635277/100000000000000 : ℝ)^49 := by
    have hnat : (3733255781 : ℕ)^65*100000000000000^49 ≤ 27062087635277^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733255781 10000000000 27062087635277 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732659257/5000000000 : ℝ)^65 ≤ (313071335263/4000000000000 : ℝ)^49 := by
    have hnat : (732659257 : ℕ)^65*4000000000000^49 ≤ 313071335263^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732659257 5000000000 313071335263 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3618217859/5000000000 : ℝ), (3733255781/10000000000 : ℝ), (-732659257/5000000000 : ℝ)] ![(65111128965003/100000000000000 : ℝ), (27062087635277/100000000000000 : ℝ), (313071335263/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3618217859/5000000000 : ℝ)|^65 ≤ (65111128965003/100000000000000 : ℝ)^49
        have hw : |(3618217859/5000000000 : ℝ)|=(3618217859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733255781/10000000000 : ℝ)|^65 ≤ (27062087635277/100000000000000 : ℝ)^49
        have hw : |(3733255781/10000000000 : ℝ)|=(3733255781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-732659257/5000000000 : ℝ)|^65 ≤ (313071335263/4000000000000 : ℝ)^49
        have hw : |(-732659257/5000000000 : ℝ)|=(732659257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301054_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((22139/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22139/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91247/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9253/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9253/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40981/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40981/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81/125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81/125 : ℝ)*X 1 2) := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s2_pow0 : (22139/25000 : ℝ) ^ (129/32 : ℝ) ≤ (12253284700271154673/20000000000000000000 : ℝ) := by
    have hpowers : (22139/25000 : ℝ)^129 ≤ (12253284700271154673/20000000000000000000 : ℝ)^32 := by
      have hnat : (22139 : ℕ)^129*20000000000000000000^32 ≤ 12253284700271154673^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22139 25000 12253284700271154673 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22139/25000 : ℝ)) (X := (12253284700271154673/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (32253284700271154673/20000000000000000000 : ℝ) ≤ (5629291989883721/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (32253284700271154673/20000000000000000000 : ℝ)^32 ≤ (5629291989883721/5000000000000000 : ℝ)^129 := by
      have hnat : (32253284700271154673 : ℕ)^32*5000000000000000^129 ≤ 5629291989883721^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32253284700271154673 20000000000000000000 5629291989883721 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5629291989883721/5000000000000000 : ℝ)) (X := (32253284700271154673/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (22253284700271154673/10000000000000000000 : ℝ) ≤ (243896339495921/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (22253284700271154673/10000000000000000000 : ℝ)^32 ≤ (243896339495921/200000000000000 : ℝ)^129 := by
      have hnat : (22253284700271154673 : ℕ)^32*200000000000000^129 ≤ 243896339495921^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22253284700271154673 10000000000000000000 243896339495921 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (243896339495921/200000000000000 : ℝ)) (X := (22253284700271154673/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(629291989883721/4427800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7314320273661/69184375000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (22139/25000 : ℝ)) (alpha := (629291989883721/4427800000000000 : ℝ)) (beta := (7314320273661/69184375000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22139/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(629291989883721/4427800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7314320273661/69184375000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (91247/100000 : ℝ) ^ (129/32 : ℝ) ≤ (138248747574133479/200000000000000000 : ℝ) := by
    have hpowers : (91247/100000 : ℝ)^129 ≤ (138248747574133479/200000000000000000 : ℝ)^32 := by
      have hnat : (91247 : ℕ)^129*200000000000000000^32 ≤ 138248747574133479^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91247 100000 138248747574133479 200000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91247/100000 : ℝ)) (X := (138248747574133479/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (338248747574133479/200000000000000000 : ℝ) ≤ (2848061079757039/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (338248747574133479/200000000000000000 : ℝ)^32 ≤ (2848061079757039/2500000000000000 : ℝ)^129 := by
      have hnat : (338248747574133479 : ℕ)^32*2500000000000000^129 ≤ 2848061079757039^129*200000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        338248747574133479 200000000000000000 2848061079757039 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2848061079757039/2500000000000000 : ℝ)) (X := (338248747574133479/200000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (238248747574133479/100000000000000000 : ℝ) ≤ (248060133296887/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (238248747574133479/100000000000000000 : ℝ)^32 ≤ (248060133296887/200000000000000 : ℝ)^129 := by
      have hnat : (238248747574133479 : ℕ)^32*200000000000000^129 ≤ 248060133296887^129*100000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        238248747574133479 100000000000000000 248060133296887 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (248060133296887/200000000000000 : ℝ)) (X := (238248747574133479/100000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(348061079757039/2281175000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(505381172908097/4562350000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (91247/100000 : ℝ)) (alpha := (348061079757039/2281175000000000 : ℝ)) (beta := (505381172908097/4562350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (91247/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(348061079757039/2281175000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(505381172908097/4562350000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (9253/12500 : ℝ) ^ (129/32 : ℝ) ≤ (2974459697360339557/10000000000000000000 : ℝ) := by
    have hpowers : (9253/12500 : ℝ)^129 ≤ (2974459697360339557/10000000000000000000 : ℝ)^32 := by
      have hnat : (9253 : ℕ)^129*10000000000000000000^32 ≤ 2974459697360339557^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9253 12500 2974459697360339557 10000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9253/12500 : ℝ)) (X := (2974459697360339557/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (12974459697360339557/10000000000000000000 : ℝ) ≤ (2133453348468171/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12974459697360339557/10000000000000000000 : ℝ)^32 ≤ (2133453348468171/2000000000000000 : ℝ)^129 := by
      have hnat : (12974459697360339557 : ℕ)^32*2000000000000000^129 ≤ 2133453348468171^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12974459697360339557 10000000000000000000 2133453348468171 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2133453348468171/2000000000000000 : ℝ)) (X := (12974459697360339557/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (7974459697360339557/5000000000000000000 : ℝ) ≤ (2245535479971697/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (7974459697360339557/5000000000000000000 : ℝ)^32 ≤ (2245535479971697/2000000000000000 : ℝ)^129 := by
      have hnat : (7974459697360339557 : ℕ)^32*2000000000000000^129 ≤ 2245535479971697^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7974459697360339557 5000000000000000000 2245535479971697 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2245535479971697/2000000000000000 : ℝ)) (X := (7974459697360339557/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(133453348468171/1480480000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(56041065751763/740240000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (9253/12500 : ℝ)) (alpha := (133453348468171/1480480000000000 : ℝ)) (beta := (56041065751763/740240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9253/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(133453348468171/1480480000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(56041065751763/740240000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-292378367/10000000000 : ℝ)*X 0 0+(178236643/400000000 : ℝ)*X 0 1+(-57720039/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2922930147/5000000000 : ℝ)*X 1 0+(-1098791/6250000 : ℝ)*X 1 1+(-1020777443/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2822713177/5000000000 : ℝ)*X 2 0+(2794848671/5000000000 : ℝ)*X 2 1+(66859131/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5520451417/10000000000 : ℝ)*X 0 0+(2739789879/5000000000 : ℝ)*X 0 1+(-424164317/2500000000 : ℝ)*X 0 2+(5520451417/10000000000 : ℝ)*X 1 0+(2739789879/5000000000 : ℝ)*X 1 1+(-424164317/2500000000 : ℝ)*X 1 2+(5520451417/10000000000 : ℝ)*X 2 0+(2739789879/5000000000 : ℝ)*X 2 1+(-424164317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-11837/2500000 : ℝ)*X 0 0+(1902400987/10000000000 : ℝ)*X 0 1+(-914751303/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3917638149/10000000000 : ℝ)*X 1 0+(-1177119417/10000000000 : ℝ)*X 1 1+(-7252025859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3427594647/10000000000 : ℝ)*X 2 0+(7952119369/10000000000 : ℝ)*X 2 1+(26674629/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((754802799/2000000000 : ℝ)*X 0 0+(304778661/400000000 : ℝ)*X 0 1+(-5435097/80000000 : ℝ)*X 0 2+(754802799/2000000000 : ℝ)*X 1 0+(304778661/400000000 : ℝ)*X 1 1+(-5435097/80000000 : ℝ)*X 1 2+(754802799/2000000000 : ℝ)*X 2 0+(304778661/400000000 : ℝ)*X 2 1+(-5435097/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((5320061/10000000000 : ℝ)*X 0 0+(1043314869/5000000000 : ℝ)*X 0 1+(-9041328351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1692652293/5000000000 : ℝ)*X 1 0+(-436333567/2000000000 : ℝ)*X 1 1+(-1763896001/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7876961469/10000000000 : ℝ)*X 2 0+(792410663/2500000000 : ℝ)*X 2 1+(275164011/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((732089539/1000000000 : ℝ)*X 0 0+(1913908677/5000000000 : ℝ)*X 0 1+(-592364959/5000000000 : ℝ)*X 0 2+(732089539/1000000000 : ℝ)*X 1 0+(1913908677/5000000000 : ℝ)*X 1 1+(-592364959/5000000000 : ℝ)*X 1 2+(732089539/1000000000 : ℝ)*X 2 0+(1913908677/5000000000 : ℝ)*X 2 1+(-592364959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((36315263/10000000000 : ℝ)*X 0 0+(390925423/625000000 : ℝ)*X 0 1+(-5594406871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7907401637/10000000000 : ℝ)*X 1 0+(-1713404097/10000000000 : ℝ)*X 1 1+(-1322343507/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3462442941/10000000000 : ℝ)*X 2 0+(3435849947/5000000000 : ℝ)*X 2 1+(2358612397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3618217859/5000000000 : ℝ)*X 0 0+(3733255781/10000000000 : ℝ)*X 0 1+(-732659257/5000000000 : ℝ)*X 0 2+(3618217859/5000000000 : ℝ)*X 1 0+(3733255781/10000000000 : ℝ)*X 1 1+(-732659257/5000000000 : ℝ)*X 1 2+(3618217859/5000000000 : ℝ)*X 2 0+(3733255781/10000000000 : ℝ)*X 2 1+(-732659257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((38977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2193077643583185248804304579/168861698200000000000000000000000 : ℝ) := by norm_num
    linear_combination (291601687631/500000000000 : ℝ)*(base7) + (345543/1000000000000 : ℝ)*(base50) + (16423001/500000000000 : ℝ)*(base53) + (116972933121/500000000000 : ℝ)*(base60) + (493932310591/250000000000 : ℝ)*(major_s2_0) + (493932310591/250000000000 : ℝ)*(major_s2_1) + (987848198181/500000000000 : ℝ)*(major_s2_2) + (63015729/1000000000000 : ℝ)*(sp_s2_1) + (305559/25000000000 : ℝ)*(sp_s2_6) + (1127866370317/500000000000 : ℝ)*(sp_s2_7) + (451300389583/200000000000 : ℝ)*(sp_s2_8) + (1128298904823/500000000000 : ℝ)*(sp_s2_9) + (1918829211881/1000000000000 : ℝ)*(sp_s2_13) + (83222301/100000000000 : ℝ)*(sp_s2_14) + (1335638058979/1000000000000 : ℝ)*(f.failure) + (1128298904823/500000000000 : ℝ)*(f.sum) + (160158671446242626107/337723396400000000000000000000000 : ℝ)*base62 + (89172617942413/370120000000000000000000000 : ℝ)*base64 + (1132528299640417/4562350000000000000000000000 : ℝ)*base67 + (559005471604073/740240000000000000000000000 : ℝ)*base68 + (15610128529821299917/40970433400000000000000000000000 : ℝ)*base71 + (437352773854539/1106950000000000000000000000 : ℝ)*base73 + (4139853596775703/4562350000000000000000000000 : ℝ)*base74 + (260602900458647/553475000000000000000000000 : ℝ)*base76 + (3547497563462385283/7769682050000000000000000000000 : ℝ)*base78 + (2399/25000000000000000 : ℝ)*base87 + (2399/25000000000000000 : ℝ)*base89 + (2399/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40981/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40981/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6101387182430396797077224670129/575142944069200000000000000000000000 : ℝ) := by norm_num
    linear_combination (158471034211/200000000000 : ℝ)*(base7) + (128053/500000000000 : ℝ)*(base39) + (53931857899/500000000000 : ℝ)*(base60) + (2088041415283/1000000000000 : ℝ)*(major_s2_0) + (2088041415283/1000000000000 : ℝ)*(major_s2_1) + (2088041415283/1000000000000 : ℝ)*(major_s2_2) + (4784467/1000000000000 : ℝ)*(sp_s2_0) + (135659/15625000000 : ℝ)*(sp_s2_1) + (40953797/1000000000000 : ℝ)*(sp_s2_8) + (2276467614759/1000000000000 : ℝ)*(sp_s2_14) + (2276422763253/1000000000000 : ℝ)*(sp_s2_15) + (1138236199613/500000000000 : ℝ)*(sp_s2_16) + (2203891793349/1000000000000 : ℝ)*(sp_s2_20) + (27028827/1000000000000 : ℝ)*(sp_s2_27) + (17644545639/12500000000 : ℝ)*(f.failure) + (1138236199613/500000000000 : ℝ)*(f.sum) + (135817830154669096773/675446792800000000000000000000000 : ℝ)*base62 + (91986204108471/740240000000000000000000000 : ℝ)*base64 + (378794340978639/4562350000000000000000000000 : ℝ)*base67 + (45781229053171/296096000000000000000000000 : ℝ)*base68 + (15177255514247075307/81940866800000000000000000000000 : ℝ)*base70 + (35893718281833/1106950000000000000000000000 : ℝ)*base73 + (284461961576269/1140587500000000000000000000 : ℝ)*base74 + (538611269194257/4427800000000000000000000000 : ℝ)*base76 + (83406266704986879/7769682050000000000000000000000 : ℝ)*base79 + (157/625000000000000 : ℝ)*base86 + (157/625000000000000 : ℝ)*base88 + (157/625000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81/125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81/125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (799185229081373723296125191151/115028588813840000000000000000000000 : ℝ) := by norm_num
    linear_combination (742310716529/1000000000000 : ℝ)*(base7) + (186841396389/1000000000000 : ℝ)*(base39) + (228031/500000000000 : ℝ)*(base43) + (1848457224409/1000000000000 : ℝ)*(major_s2_0) + (924228384173/500000000000 : ℝ)*(major_s2_1) + (1848457224409/1000000000000 : ℝ)*(major_s2_2) + (10475343/1000000000000 : ℝ)*(sp_s2_2) + (265149/200000000000 : ℝ)*(sp_s2_6) + (3675439/250000000000 : ℝ)*(sp_s2_9) + (51545989/500000000000 : ℝ)*(sp_s2_20) + (398018708787/200000000000 : ℝ)*(sp_s2_21) + (995046999999/500000000000 : ℝ)*(sp_s2_22) + (497517091709/250000000000 : ℝ)*(sp_s2_23) + (1991805568977/1000000000000 : ℝ)*(sp_s2_27) + (312399817543/250000000000 : ℝ)*(f.failure) + (995046999999/500000000000 : ℝ)*(f.sum) + (33267082393709605809/675446792800000000000000000000000 : ℝ)*base63 + (56067717639869/740240000000000000000000000 : ℝ)*base64 + (1801682794579217/4562350000000000000000000000 : ℝ)*base66 + (63775945823683/1480480000000000000000000000 : ℝ)*base69 + (19606745731379361359/81940866800000000000000000000000 : ℝ)*base71 + (41342698394157/553475000000000000000000000 : ℝ)*base73 + (2035445549720753/4562350000000000000000000000 : ℝ)*base75 + (372180149538251/4427800000000000000000000000 : ℝ)*base76 + (115079142264007503/388484102500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (1433/6250000000000000 : ℝ)*base87 + (7683/6250000000000000 : ℝ)*base89 + (1433/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((22139/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22139/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91247/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9253/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9253/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38977/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38977/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40981/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40981/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-81/125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-81/125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301054_s2 p hpa hpb X hX hprev1

#print axioms solution

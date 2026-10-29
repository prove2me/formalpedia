-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:55.647359+00:00
-- url     : https://prove2.me/submissions/44d894e5-c8af-4f14-98a0-fadb70007626

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
theorem collision_support_c316062_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1339997541/10000000000 : ℝ)*x 0 + (2503730697/5000000000 : ℝ)*x 1 + (-5804217251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339997541/10000000000 : ℝ)^77 ≤ (1977368823823/25000000000000 : ℝ)^61 := by
    have hnat : (1339997541 : ℕ)^77*25000000000000^61 ≤ 1977368823823^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339997541 10000000000 1977368823823 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503730697/5000000000 : ℝ)^77 ≤ (41766567585427/100000000000000 : ℝ)^61 := by
    have hnat : (2503730697 : ℕ)^77*100000000000000^61 ≤ 41766567585427^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503730697 5000000000 41766567585427 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5804217251/10000000000 : ℝ)^77 ≤ (50323957104369/100000000000000 : ℝ)^61 := by
    have hnat : (5804217251 : ℕ)^77*100000000000000^61 ≤ 50323957104369^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5804217251 10000000000 50323957104369 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1339997541/10000000000 : ℝ), (2503730697/5000000000 : ℝ), (-5804217251/10000000000 : ℝ)] ![(1977368823823/25000000000000 : ℝ), (41766567585427/100000000000000 : ℝ), (50323957104369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1339997541/10000000000 : ℝ)|^77 ≤ (1977368823823/25000000000000 : ℝ)^61
        have hw : |(-1339997541/10000000000 : ℝ)|=(1339997541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2503730697/5000000000 : ℝ)|^77 ≤ (41766567585427/100000000000000 : ℝ)^61
        have hw : |(2503730697/5000000000 : ℝ)|=(2503730697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5804217251/10000000000 : ℝ)|^77 ≤ (50323957104369/100000000000000 : ℝ)^61
        have hw : |(-5804217251/10000000000 : ℝ)|=(5804217251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (502766629/1000000000 : ℝ)*x 0 + (-673256719/5000000000 : ℝ)*x 1 + (-5780317947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502766629/1000000000 : ℝ)^77 ≤ (10494852504673/25000000000000 : ℝ)^61 := by
    have hnat : (502766629 : ℕ)^77*25000000000000^61 ≤ 10494852504673^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502766629 1000000000 10494852504673 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673256719/5000000000 : ℝ)^77 ≤ (7958055049507/100000000000000 : ℝ)^61 := by
    have hnat : (673256719 : ℕ)^77*100000000000000^61 ≤ 7958055049507^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673256719 5000000000 7958055049507 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5780317947/10000000000 : ℝ)^77 ≤ (10012506983559/20000000000000 : ℝ)^61 := by
    have hnat : (5780317947 : ℕ)^77*20000000000000^61 ≤ 10012506983559^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5780317947 10000000000 10012506983559 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502766629/1000000000 : ℝ), (-673256719/5000000000 : ℝ), (-5780317947/10000000000 : ℝ)] ![(10494852504673/25000000000000 : ℝ), (7958055049507/100000000000000 : ℝ), (10012506983559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502766629/1000000000 : ℝ)|^77 ≤ (10494852504673/25000000000000 : ℝ)^61
        have hw : |(502766629/1000000000 : ℝ)|=(502766629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-673256719/5000000000 : ℝ)|^77 ≤ (7958055049507/100000000000000 : ℝ)^61
        have hw : |(-673256719/5000000000 : ℝ)|=(673256719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5780317947/10000000000 : ℝ)|^77 ≤ (10012506983559/20000000000000 : ℝ)^61
        have hw : |(-5780317947/10000000000 : ℝ)|=(5780317947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (522656981/1000000000 : ℝ)*x 0 + (210032387/400000000 : ℝ)*x 1 + (181102091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522656981/1000000000 : ℝ)^77 ≤ (10763324859/24414062500 : ℝ)^61 := by
    have hnat : (522656981 : ℕ)^77*24414062500^61 ≤ 10763324859^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522656981 1000000000 10763324859 24414062500 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210032387/400000000 : ℝ)^77 ≤ (44344831102849/100000000000000 : ℝ)^61 := by
    have hnat : (210032387 : ℕ)^77*100000000000000^61 ≤ 44344831102849^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210032387 400000000 44344831102849 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181102091/1000000000 : ℝ)^77 ≤ (11568590251369/100000000000000 : ℝ)^61 := by
    have hnat : (181102091 : ℕ)^77*100000000000000^61 ≤ 11568590251369^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181102091 1000000000 11568590251369 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522656981/1000000000 : ℝ), (210032387/400000000 : ℝ), (181102091/1000000000 : ℝ)] ![(10763324859/24414062500 : ℝ), (44344831102849/100000000000000 : ℝ), (11568590251369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522656981/1000000000 : ℝ)|^77 ≤ (10763324859/24414062500 : ℝ)^61
        have hw : |(522656981/1000000000 : ℝ)|=(522656981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210032387/400000000 : ℝ)|^77 ≤ (44344831102849/100000000000000 : ℝ)^61
        have hw : |(210032387/400000000 : ℝ)|=(210032387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181102091/1000000000 : ℝ)|^77 ≤ (11568590251369/100000000000000 : ℝ)^61
        have hw : |(181102091/1000000000 : ℝ)|=(181102091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-280535801/2500000000 : ℝ)*x 0 + (4223671727/10000000000 : ℝ)*x 1 + (-133414937/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280535801/2500000000 : ℝ)^77 ≤ (3161190183319/50000000000000 : ℝ)^61 := by
    have hnat : (280535801 : ℕ)^77*50000000000000^61 ≤ 3161190183319^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280535801 2500000000 3161190183319 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223671727/10000000000 : ℝ)^77 ≤ (8422684520983/25000000000000 : ℝ)^61 := by
    have hnat : (4223671727 : ℕ)^77*25000000000000^61 ≤ 8422684520983^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223671727 10000000000 8422684520983 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133414937/200000000 : ℝ)^77 ≤ (5998688152699/10000000000000 : ℝ)^61 := by
    have hnat : (133414937 : ℕ)^77*10000000000000^61 ≤ 5998688152699^61*200000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133414937 200000000 5998688152699 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280535801/2500000000 : ℝ), (4223671727/10000000000 : ℝ), (-133414937/200000000 : ℝ)] ![(3161190183319/50000000000000 : ℝ), (8422684520983/25000000000000 : ℝ), (5998688152699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280535801/2500000000 : ℝ)|^77 ≤ (3161190183319/50000000000000 : ℝ)^61
        have hw : |(-280535801/2500000000 : ℝ)|=(280535801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223671727/10000000000 : ℝ)|^77 ≤ (8422684520983/25000000000000 : ℝ)^61
        have hw : |(4223671727/10000000000 : ℝ)|=(4223671727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133414937/200000000 : ℝ)|^77 ≤ (5998688152699/10000000000000 : ℝ)^61
        have hw : |(-133414937/200000000 : ℝ)|=(133414937/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4568390903/10000000000 : ℝ)*x 0 + (-152130749/2500000000 : ℝ)*x 1 + (-3330743323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4568390903/10000000000 : ℝ)^77 ≤ (37198106537907/100000000000000 : ℝ)^61 := by
    have hnat : (4568390903 : ℕ)^77*100000000000000^61 ≤ 37198106537907^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568390903 10000000000 37198106537907 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152130749/2500000000 : ℝ)^77 ≤ (45626678613/1562500000000 : ℝ)^61 := by
    have hnat : (152130749 : ℕ)^77*1562500000000^61 ≤ 45626678613^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152130749 2500000000 45626678613 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3330743323/5000000000 : ℝ)^77 ≤ (2994089300759/5000000000000 : ℝ)^61 := by
    have hnat : (3330743323 : ℕ)^77*5000000000000^61 ≤ 2994089300759^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3330743323 5000000000 2994089300759 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4568390903/10000000000 : ℝ), (-152130749/2500000000 : ℝ), (-3330743323/5000000000 : ℝ)] ![(37198106537907/100000000000000 : ℝ), (45626678613/1562500000000 : ℝ), (2994089300759/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4568390903/10000000000 : ℝ)|^77 ≤ (37198106537907/100000000000000 : ℝ)^61
        have hw : |(4568390903/10000000000 : ℝ)|=(4568390903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152130749/2500000000 : ℝ)|^77 ≤ (45626678613/1562500000000 : ℝ)^61
        have hw : |(-152130749/2500000000 : ℝ)|=(152130749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3330743323/5000000000 : ℝ)|^77 ≤ (2994089300759/5000000000000 : ℝ)^61
        have hw : |(-3330743323/5000000000 : ℝ)|=(3330743323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4543467967/10000000000 : ℝ)*x 0 + (6495386749/10000000000 : ℝ)*x 1 + (117479767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4543467967/10000000000 : ℝ)^77 ≤ (18471063158083/50000000000000 : ℝ)^61 := by
    have hnat : (4543467967 : ℕ)^77*50000000000000^61 ≤ 18471063158083^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543467967 10000000000 18471063158083 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6495386749/10000000000 : ℝ)^77 ≤ (29001618568171/50000000000000 : ℝ)^61 := by
    have hnat : (6495386749 : ℕ)^77*50000000000000^61 ≤ 29001618568171^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6495386749 10000000000 29001618568171 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117479767/1250000000 : ℝ)^77 ≤ (631829567579/12500000000000 : ℝ)^61 := by
    have hnat : (117479767 : ℕ)^77*12500000000000^61 ≤ 631829567579^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117479767 1250000000 631829567579 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4543467967/10000000000 : ℝ), (6495386749/10000000000 : ℝ), (117479767/1250000000 : ℝ)] ![(18471063158083/50000000000000 : ℝ), (29001618568171/50000000000000 : ℝ), (631829567579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4543467967/10000000000 : ℝ)|^77 ≤ (18471063158083/50000000000000 : ℝ)^61
        have hw : |(4543467967/10000000000 : ℝ)|=(4543467967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6495386749/10000000000 : ℝ)|^77 ≤ (29001618568171/50000000000000 : ℝ)^61
        have hw : |(6495386749/10000000000 : ℝ)|=(6495386749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117479767/1250000000 : ℝ)|^77 ≤ (631829567579/12500000000000 : ℝ)^61
        have hw : |(117479767/1250000000 : ℝ)|=(117479767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (304284131/625000000 : ℝ)*x 0 + (6613264981/10000000000 : ℝ)*x 1 + (-114759067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304284131/625000000 : ℝ)^77 ≤ (8061867427383/20000000000000 : ℝ)^61 := by
    have hnat : (304284131 : ℕ)^77*20000000000000^61 ≤ 8061867427383^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304284131 625000000 8061867427383 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6613264981/10000000000 : ℝ)^77 ≤ (29667565434837/50000000000000 : ℝ)^61 := by
    have hnat : (6613264981 : ℕ)^77*50000000000000^61 ≤ 29667565434837^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6613264981 10000000000 29667565434837 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114759067/10000000000 : ℝ)^77 ≤ (8888299739/2500000000000 : ℝ)^61 := by
    have hnat : (114759067 : ℕ)^77*2500000000000^61 ≤ 8888299739^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114759067 10000000000 8888299739 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(304284131/625000000 : ℝ), (6613264981/10000000000 : ℝ), (-114759067/10000000000 : ℝ)] ![(8061867427383/20000000000000 : ℝ), (29667565434837/50000000000000 : ℝ), (8888299739/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(304284131/625000000 : ℝ)|^77 ≤ (8061867427383/20000000000000 : ℝ)^61
        have hw : |(304284131/625000000 : ℝ)|=(304284131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6613264981/10000000000 : ℝ)|^77 ≤ (29667565434837/50000000000000 : ℝ)^61
        have hw : |(6613264981/10000000000 : ℝ)|=(6613264981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114759067/10000000000 : ℝ)|^77 ≤ (8888299739/2500000000000 : ℝ)^61
        have hw : |(-114759067/10000000000 : ℝ)|=(114759067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-303094001/5000000000 : ℝ)*x 0 + (4540528519/10000000000 : ℝ)*x 1 + (-6687936363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303094001/5000000000 : ℝ)^77 ≤ (2905970677877/100000000000000 : ℝ)^61 := by
    have hnat : (303094001 : ℕ)^77*100000000000000^61 ≤ 2905970677877^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303094001 5000000000 2905970677877 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540528519/10000000000 : ℝ)^77 ≤ (36911959864153/100000000000000 : ℝ)^61 := by
    have hnat : (4540528519 : ℕ)^77*100000000000000^61 ≤ 36911959864153^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540528519 10000000000 36911959864153 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6687936363/10000000000 : ℝ)^77 ≤ (60182069448543/100000000000000 : ℝ)^61 := by
    have hnat : (6687936363 : ℕ)^77*100000000000000^61 ≤ 60182069448543^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6687936363 10000000000 60182069448543 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-303094001/5000000000 : ℝ), (4540528519/10000000000 : ℝ), (-6687936363/10000000000 : ℝ)] ![(2905970677877/100000000000000 : ℝ), (36911959864153/100000000000000 : ℝ), (60182069448543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-303094001/5000000000 : ℝ)|^77 ≤ (2905970677877/100000000000000 : ℝ)^61
        have hw : |(-303094001/5000000000 : ℝ)|=(303094001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540528519/10000000000 : ℝ)|^77 ≤ (36911959864153/100000000000000 : ℝ)^61
        have hw : |(4540528519/10000000000 : ℝ)|=(4540528519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6687936363/10000000000 : ℝ)|^77 ≤ (60182069448543/100000000000000 : ℝ)^61
        have hw : |(-6687936363/10000000000 : ℝ)|=(6687936363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2106284133/5000000000 : ℝ)*x 0 + (-28131277/250000000 : ℝ)*x 1 + (-6678643413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106284133/5000000000 : ℝ)^77 ≤ (1678948860663/5000000000000 : ℝ)^61 := by
    have hnat : (2106284133 : ℕ)^77*5000000000000^61 ≤ 1678948860663^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106284133 5000000000 1678948860663 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28131277/250000000 : ℝ)^77 ≤ (317224583951/5000000000000 : ℝ)^61 := by
    have hnat : (28131277 : ℕ)^77*5000000000000^61 ≤ 317224583951^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28131277 250000000 317224583951 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6678643413/10000000000 : ℝ)^77 ≤ (60076531098559/100000000000000 : ℝ)^61 := by
    have hnat : (6678643413 : ℕ)^77*100000000000000^61 ≤ 60076531098559^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6678643413 10000000000 60076531098559 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106284133/5000000000 : ℝ), (-28131277/250000000 : ℝ), (-6678643413/10000000000 : ℝ)] ![(1678948860663/5000000000000 : ℝ), (317224583951/5000000000000 : ℝ), (60076531098559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106284133/5000000000 : ℝ)|^77 ≤ (1678948860663/5000000000000 : ℝ)^61
        have hw : |(2106284133/5000000000 : ℝ)|=(2106284133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28131277/250000000 : ℝ)|^77 ≤ (317224583951/5000000000000 : ℝ)^61
        have hw : |(-28131277/250000000 : ℝ)|=(28131277/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6678643413/10000000000 : ℝ)|^77 ≤ (60076531098559/100000000000000 : ℝ)^61
        have hw : |(-6678643413/10000000000 : ℝ)|=(6678643413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1564447219/2500000000 : ℝ)*x 0 + (14984059/31250000 : ℝ)*x 1 + (59348893/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1564447219/2500000000 : ℝ)^77 ≤ (55337955783987/100000000000000 : ℝ)^61 := by
    have hnat : (1564447219 : ℕ)^77*100000000000000^61 ≤ 55337955783987^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564447219 2500000000 55337955783987 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14984059/31250000 : ℝ)^77 ≤ (19770583062303/50000000000000 : ℝ)^61 := by
    have hnat : (14984059 : ℕ)^77*50000000000000^61 ≤ 19770583062303^61*31250000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14984059 31250000 19770583062303 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59348893/625000000 : ℝ)^77 ≤ (2560439041233/50000000000000 : ℝ)^61 := by
    have hnat : (59348893 : ℕ)^77*50000000000000^61 ≤ 2560439041233^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59348893 625000000 2560439041233 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1564447219/2500000000 : ℝ), (14984059/31250000 : ℝ), (59348893/625000000 : ℝ)] ![(55337955783987/100000000000000 : ℝ), (19770583062303/50000000000000 : ℝ), (2560439041233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1564447219/2500000000 : ℝ)|^77 ≤ (55337955783987/100000000000000 : ℝ)^61
        have hw : |(1564447219/2500000000 : ℝ)|=(1564447219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14984059/31250000 : ℝ)|^77 ≤ (19770583062303/50000000000000 : ℝ)^61
        have hw : |(14984059/31250000 : ℝ)|=(14984059/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59348893/625000000 : ℝ)|^77 ≤ (2560439041233/50000000000000 : ℝ)^61
        have hw : |(59348893/625000000 : ℝ)|=(59348893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1431431823/2000000000 : ℝ)*x 0 + (2128921041/5000000000 : ℝ)*x 1 + (-6358043/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1431431823/2000000000 : ℝ)^77 ≤ (2048754341129/3125000000000 : ℝ)^61 := by
    have hnat : (1431431823 : ℕ)^77*3125000000000^61 ≤ 2048754341129^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431431823 2000000000 2048754341129 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128921041/5000000000 : ℝ)^77 ≤ (34035159687053/100000000000000 : ℝ)^61 := by
    have hnat : (2128921041 : ℕ)^77*100000000000000^61 ≤ 34035159687053^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128921041 5000000000 34035159687053 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6358043/500000000 : ℝ)^77 ≤ (404701385211/100000000000000 : ℝ)^61 := by
    have hnat : (6358043 : ℕ)^77*100000000000000^61 ≤ 404701385211^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6358043 500000000 404701385211 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1431431823/2000000000 : ℝ), (2128921041/5000000000 : ℝ), (-6358043/500000000 : ℝ)] ![(2048754341129/3125000000000 : ℝ), (34035159687053/100000000000000 : ℝ), (404701385211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1431431823/2000000000 : ℝ)|^77 ≤ (2048754341129/3125000000000 : ℝ)^61
        have hw : |(1431431823/2000000000 : ℝ)|=(1431431823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2128921041/5000000000 : ℝ)|^77 ≤ (34035159687053/100000000000000 : ℝ)^61
        have hw : |(2128921041/5000000000 : ℝ)|=(2128921041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6358043/500000000 : ℝ)|^77 ≤ (404701385211/100000000000000 : ℝ)^61
        have hw : |(-6358043/500000000 : ℝ)|=(6358043/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3526339/156250000 : ℝ)*x 0 + (1439365683/2500000000 : ℝ)*x 1 + (-5715256373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3526339/156250000 : ℝ)^77 ≤ (834903419909/100000000000000 : ℝ)^61 := by
    have hnat : (3526339 : ℕ)^77*100000000000000^61 ≤ 834903419909^61*156250000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3526339 156250000 834903419909 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439365683/2500000000 : ℝ)^77 ≤ (49812798529167/100000000000000 : ℝ)^61 := by
    have hnat : (1439365683 : ℕ)^77*100000000000000^61 ≤ 49812798529167^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439365683 2500000000 49812798529167 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5715256373/10000000000 : ℝ)^77 ≤ (49352298041117/100000000000000 : ℝ)^61 := by
    have hnat : (5715256373 : ℕ)^77*100000000000000^61 ≤ 49352298041117^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715256373 10000000000 49352298041117 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3526339/156250000 : ℝ), (1439365683/2500000000 : ℝ), (-5715256373/10000000000 : ℝ)] ![(834903419909/100000000000000 : ℝ), (49812798529167/100000000000000 : ℝ), (49352298041117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3526339/156250000 : ℝ)|^77 ≤ (834903419909/100000000000000 : ℝ)^61
        have hw : |(-3526339/156250000 : ℝ)|=(3526339/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1439365683/2500000000 : ℝ)|^77 ≤ (49812798529167/100000000000000 : ℝ)^61
        have hw : |(1439365683/2500000000 : ℝ)|=(1439365683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5715256373/10000000000 : ℝ)|^77 ≤ (49352298041117/100000000000000 : ℝ)^61
        have hw : |(-5715256373/10000000000 : ℝ)|=(5715256373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1556000197/2500000000 : ℝ)*x 0 + (-339179331/5000000000 : ℝ)*x 1 + (-5000151167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1556000197/2500000000 : ℝ)^77 ≤ (54961062270069/100000000000000 : ℝ)^61 := by
    have hnat : (1556000197 : ℕ)^77*100000000000000^61 ≤ 54961062270069^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556000197 2500000000 54961062270069 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339179331/5000000000 : ℝ)^77 ≤ (3349322105943/100000000000000 : ℝ)^61 := by
    have hnat : (339179331 : ℕ)^77*100000000000000^61 ≤ 3349322105943^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339179331 5000000000 3349322105943 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5000151167/10000000000 : ℝ)^77 ≤ (20844807807701/50000000000000 : ℝ)^61 := by
    have hnat : (5000151167 : ℕ)^77*50000000000000^61 ≤ 20844807807701^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5000151167 10000000000 20844807807701 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1556000197/2500000000 : ℝ), (-339179331/5000000000 : ℝ), (-5000151167/10000000000 : ℝ)] ![(54961062270069/100000000000000 : ℝ), (3349322105943/100000000000000 : ℝ), (20844807807701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1556000197/2500000000 : ℝ)|^77 ≤ (54961062270069/100000000000000 : ℝ)^61
        have hw : |(1556000197/2500000000 : ℝ)|=(1556000197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339179331/5000000000 : ℝ)|^77 ≤ (3349322105943/100000000000000 : ℝ)^61
        have hw : |(-339179331/5000000000 : ℝ)|=(339179331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5000151167/10000000000 : ℝ)|^77 ≤ (20844807807701/50000000000000 : ℝ)^61
        have hw : |(-5000151167/10000000000 : ℝ)|=(5000151167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (567236401/1250000000 : ℝ)*x 0 + (1500986409/2500000000 : ℝ)*x 1 + (67569721/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567236401/1250000000 : ℝ)^77 ≤ (36884898490063/100000000000000 : ℝ)^61 := by
    have hnat : (567236401 : ℕ)^77*100000000000000^61 ≤ 36884898490063^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567236401 1250000000 36884898490063 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500986409/2500000000 : ℝ)^77 ≤ (6564955909169/12500000000000 : ℝ)^61 := by
    have hnat : (1500986409 : ℕ)^77*12500000000000^61 ≤ 6564955909169^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500986409 2500000000 6564955909169 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67569721/400000000 : ℝ)^77 ≤ (10595454222223/100000000000000 : ℝ)^61 := by
    have hnat : (67569721 : ℕ)^77*100000000000000^61 ≤ 10595454222223^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67569721 400000000 10595454222223 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(567236401/1250000000 : ℝ), (1500986409/2500000000 : ℝ), (67569721/400000000 : ℝ)] ![(36884898490063/100000000000000 : ℝ), (6564955909169/12500000000000 : ℝ), (10595454222223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(567236401/1250000000 : ℝ)|^77 ≤ (36884898490063/100000000000000 : ℝ)^61
        have hw : |(567236401/1250000000 : ℝ)|=(567236401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500986409/2500000000 : ℝ)|^77 ≤ (6564955909169/12500000000000 : ℝ)^61
        have hw : |(1500986409/2500000000 : ℝ)|=(1500986409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67569721/400000000 : ℝ)|^77 ≤ (10595454222223/100000000000000 : ℝ)^61
        have hw : |(67569721/400000000 : ℝ)|=(67569721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316062_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7486476517/10000000000 : ℝ)*x 0 + (3790451691/10000000000 : ℝ)*x 1 + (-152435003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7486476517/10000000000 : ℝ)^77 ≤ (6939066738683/10000000000000 : ℝ)^61 := by
    have hnat : (7486476517 : ℕ)^77*10000000000000^61 ≤ 6939066738683^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7486476517 10000000000 6939066738683 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3790451691/10000000000 : ℝ)^77 ≤ (14694461748277/50000000000000 : ℝ)^61 := by
    have hnat : (3790451691 : ℕ)^77*50000000000000^61 ≤ 14694461748277^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3790451691 10000000000 14694461748277 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152435003/5000000000 : ℝ)^77 ≤ (610204553943/50000000000000 : ℝ)^61 := by
    have hnat : (152435003 : ℕ)^77*50000000000000^61 ≤ 610204553943^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152435003 5000000000 610204553943 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7486476517/10000000000 : ℝ), (3790451691/10000000000 : ℝ), (-152435003/5000000000 : ℝ)] ![(6939066738683/10000000000000 : ℝ), (14694461748277/50000000000000 : ℝ), (610204553943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7486476517/10000000000 : ℝ)|^77 ≤ (6939066738683/10000000000000 : ℝ)^61
        have hw : |(7486476517/10000000000 : ℝ)|=(7486476517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3790451691/10000000000 : ℝ)|^77 ≤ (14694461748277/50000000000000 : ℝ)^61
        have hw : |(3790451691/10000000000 : ℝ)|=(3790451691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152435003/5000000000 : ℝ)|^77 ≤ (610204553943/50000000000000 : ℝ)^61
        have hw : |(-152435003/5000000000 : ℝ)|=(152435003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316062_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((15697/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15697/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19463/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19463/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67277/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-67277/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52743/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52743/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53121/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53121/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4651/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4651/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
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
  have s1_pow0 : (15697/20000 : ℝ) ^ (19/4 : ℝ) ≤ (31640012572133181997/100000000000000000000 : ℝ) := by
    have hpowers : (15697/20000 : ℝ)^19 ≤ (31640012572133181997/100000000000000000000 : ℝ)^4 := by
      have hnat : (15697 : ℕ)^19*100000000000000000000^4 ≤ 31640012572133181997^4*20000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15697 20000 31640012572133181997 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15697/20000 : ℝ)) (X := (31640012572133181997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (131640012572133181997/100000000000000000000 : ℝ) ≤ (10595813313767773/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (131640012572133181997/100000000000000000000 : ℝ)^4 ≤ (10595813313767773/10000000000000000 : ℝ)^19 := by
      have hnat : (131640012572133181997 : ℕ)^4*10000000000000000^19 ≤ 10595813313767773^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131640012572133181997 100000000000000000000 10595813313767773 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10595813313767773/10000000000000000 : ℝ)) (X := (131640012572133181997/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (81640012572133181997/50000000000000000000 : ℝ) ≤ (1108735650991241/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (81640012572133181997/50000000000000000000 : ℝ)^4 ≤ (1108735650991241/1000000000000000 : ℝ)^19 := by
      have hnat : (81640012572133181997 : ℕ)^4*1000000000000000^19 ≤ 1108735650991241^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81640012572133181997 50000000000000000000 1108735650991241 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1108735650991241/1000000000000000 : ℝ)) (X := (81640012572133181997/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(595813313767773/7848500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(491543196144637/7848500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (15697/20000 : ℝ)) (alpha := (595813313767773/7848500000000000 : ℝ)) (beta := (491543196144637/7848500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15697/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(595813313767773/7848500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(491543196144637/7848500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (19463/25000 : ℝ) ^ (19/4 : ℝ) ≤ (30446082956760205433/100000000000000000000 : ℝ) := by
    have hpowers : (19463/25000 : ℝ)^19 ≤ (30446082956760205433/100000000000000000000 : ℝ)^4 := by
      have hnat : (19463 : ℕ)^19*100000000000000000000^4 ≤ 30446082956760205433^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19463 25000 30446082956760205433 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19463/25000 : ℝ)) (X := (30446082956760205433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (130446082956760205433/100000000000000000000 : ℝ) ≤ (42302035313689/40000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (130446082956760205433/100000000000000000000 : ℝ)^4 ≤ (42302035313689/40000000000000 : ℝ)^19 := by
      have hnat : (130446082956760205433 : ℕ)^4*40000000000000^19 ≤ 42302035313689^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130446082956760205433 100000000000000000000 42302035313689 40000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (42302035313689/40000000000000 : ℝ)) (X := (130446082956760205433/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (80446082956760205433/50000000000000000000 : ℝ) ≤ (2210604383424387/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (80446082956760205433/50000000000000000000 : ℝ)^4 ≤ (2210604383424387/2000000000000000 : ℝ)^19 := by
      have hnat : (80446082956760205433 : ℕ)^4*2000000000000000^19 ≤ 2210604383424387^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80446082956760205433 50000000000000000000 2210604383424387 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2210604383424387/2000000000000000 : ℝ)) (X := (80446082956760205433/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2302035313689/31140800000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(95502617739937/1557040000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (19463/25000 : ℝ)) (alpha := (2302035313689/31140800000000 : ℝ)) (beta := (95502617739937/1557040000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (19463/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2302035313689/31140800000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(95502617739937/1557040000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (67277/100000 : ℝ) ^ (19/4 : ℝ) ≤ (1902288774049201553/12500000000000000000 : ℝ) := by
    have hpowers : (67277/100000 : ℝ)^19 ≤ (1902288774049201553/12500000000000000000 : ℝ)^4 := by
      have hnat : (67277 : ℕ)^19*12500000000000000000^4 ≤ 1902288774049201553^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67277 100000 1902288774049201553 12500000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67277/100000 : ℝ)) (X := (1902288774049201553/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (14402288774049201553/12500000000000000000 : ℝ) ≤ (2575679988234753/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (14402288774049201553/12500000000000000000 : ℝ)^4 ≤ (2575679988234753/2500000000000000 : ℝ)^19 := by
      have hnat : (14402288774049201553 : ℕ)^4*2500000000000000^19 ≤ 2575679988234753^19*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14402288774049201553 12500000000000000000 2575679988234753 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2575679988234753/2500000000000000 : ℝ)) (X := (14402288774049201553/12500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (8152288774049201553/6250000000000000000 : ℝ) ≤ (5287673659427823/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (8152288774049201553/6250000000000000000 : ℝ)^4 ≤ (5287673659427823/5000000000000000 : ℝ)^19 := by
      have hnat : (8152288774049201553 : ℕ)^4*5000000000000000^19 ≤ 5287673659427823^19*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8152288774049201553 6250000000000000000 5287673659427823 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5287673659427823/5000000000000000 : ℝ)) (X := (8152288774049201553/6250000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(10811426890679/240275000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(136313682958317/3363850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (67277/100000 : ℝ)) (alpha := (10811426890679/240275000000000 : ℝ)) (beta := (136313682958317/3363850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (67277/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(10811426890679/240275000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(136313682958317/3363850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1339997541/10000000000 : ℝ)*X 0 0+(2503730697/5000000000 : ℝ)*X 0 1+(-5804217251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((502766629/1000000000 : ℝ)*X 1 0+(-673256719/5000000000 : ℝ)*X 1 1+(-5780317947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((522656981/1000000000 : ℝ)*X 2 0+(210032387/400000000 : ℝ)*X 2 1+(181102091/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-280535801/2500000000 : ℝ)*X 0 0+(4223671727/10000000000 : ℝ)*X 0 1+(-133414937/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4568390903/10000000000 : ℝ)*X 1 0+(-152130749/2500000000 : ℝ)*X 1 1+(-3330743323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4543467967/10000000000 : ℝ)*X 2 0+(6495386749/10000000000 : ℝ)*X 2 1+(117479767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((304284131/625000000 : ℝ)*X 0 0+(6613264981/10000000000 : ℝ)*X 0 1+(-114759067/10000000000 : ℝ)*X 0 2+(304284131/625000000 : ℝ)*X 1 0+(6613264981/10000000000 : ℝ)*X 1 1+(-114759067/10000000000 : ℝ)*X 1 2+(304284131/625000000 : ℝ)*X 2 0+(6613264981/10000000000 : ℝ)*X 2 1+(-114759067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-303094001/5000000000 : ℝ)*X 0 0+(4540528519/10000000000 : ℝ)*X 0 1+(-6687936363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2106284133/5000000000 : ℝ)*X 1 0+(-28131277/250000000 : ℝ)*X 1 1+(-6678643413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1564447219/2500000000 : ℝ)*X 2 0+(14984059/31250000 : ℝ)*X 2 1+(59348893/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1431431823/2000000000 : ℝ)*X 0 0+(2128921041/5000000000 : ℝ)*X 0 1+(-6358043/500000000 : ℝ)*X 0 2+(1431431823/2000000000 : ℝ)*X 1 0+(2128921041/5000000000 : ℝ)*X 1 1+(-6358043/500000000 : ℝ)*X 1 2+(1431431823/2000000000 : ℝ)*X 2 0+(2128921041/5000000000 : ℝ)*X 2 1+(-6358043/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-3526339/156250000 : ℝ)*X 0 0+(1439365683/2500000000 : ℝ)*X 0 1+(-5715256373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1556000197/2500000000 : ℝ)*X 1 0+(-339179331/5000000000 : ℝ)*X 1 1+(-5000151167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((567236401/1250000000 : ℝ)*X 2 0+(1500986409/2500000000 : ℝ)*X 2 1+(67569721/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7486476517/10000000000 : ℝ)*X 0 0+(3790451691/10000000000 : ℝ)*X 0 1+(-152435003/5000000000 : ℝ)*X 0 2+(7486476517/10000000000 : ℝ)*X 1 0+(3790451691/10000000000 : ℝ)*X 1 1+(-152435003/5000000000 : ℝ)*X 1 2+(7486476517/10000000000 : ℝ)*X 2 0+(3790451691/10000000000 : ℝ)*X 2 1+(-152435003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((52743/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52743/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (517050665174681408835146247/130941225100000000000000000000000 : ℝ) := by norm_num
    linear_combination (274637030581/1000000000000 : ℝ)*(base7) + (120597/500000000000 : ℝ)*(base39) + (4060851093/31250000000 : ℝ)*(base60) + (4009795903119/1000000000000 : ℝ)*(major_s1_0) + (4009795903119/1000000000000 : ℝ)*(major_s1_1) + (4009795903119/1000000000000 : ℝ)*(major_s1_2) + (321081/40000000000 : ℝ)*(sp_s1_0) + (2799311214463/500000000000 : ℝ)*(sp_s1_7) + (5598678870651/1000000000000 : ℝ)*(sp_s1_8) + (2799338013203/500000000000 : ℝ)*(sp_s1_9) + (2536773873199/1000000000000 : ℝ)*(sp_s1_13) + (52777673/1000000000000 : ℝ)*(sp_s1_14) + (4362973/1000000000000 : ℝ)*(sp_s1_22) + (7207219/1000000000000 : ℝ)*(sp_s1_23) + (1131068421309/500000000000 : ℝ)*(f.failure) + (44789465869/8000000000 : ℝ)*(f.sum) + (6616187876110021411/37411778600000000000000000000000 : ℝ)*base62 + (1919891254107893/3363850000000000000000000000 : ℝ)*base65 + (839637868306569/1557040000000000000000000000 : ℝ)*base66 + (158147633025147/480550000000000000000000000 : ℝ)*base69 + (54008496957829978059/528023534500000000000000000000000 : ℝ)*base71 + (1990350547832697/7848500000000000000000000000 : ℝ)*base72 + (1163988182041/778520000000000000000000000 : ℝ)*base74 + (735311178571463/7848500000000000000000000000 : ℝ)*base76 + (162627523592096616331/611021422000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (19413/50000000000000000 : ℝ)*base87 + (19413/50000000000000000 : ℝ)*base89 + (19413/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53121/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53121/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25898581616395363088354546531769/1284615256496687500000000000000000000 : ℝ) := by norm_num
    linear_combination (60248761529/200000000000 : ℝ)*(base7) + (488992183783/125000000000 : ℝ)*(major_s1_0) + (488992183783/125000000000 : ℝ)*(major_s1_1) + (488992183783/125000000000 : ℝ)*(major_s1_2) + (801183/62500000000 : ℝ)*(sp_s1_0) + (1274249/125000000000 : ℝ)*(sp_s1_1) + (352641/31250000000 : ℝ)*(sp_s1_2) + (40349861/250000000000 : ℝ)*(sp_s1_8) + (2721385952113/500000000000 : ℝ)*(sp_s1_14) + (5442614817391/1000000000000 : ℝ)*(sp_s1_15) + (1088555025263/200000000000 : ℝ)*(sp_s1_16) + (627028285311/250000000000 : ℝ)*(sp_s1_20) + (1687673/1000000000000 : ℝ)*(sp_s1_21) + (60418267/1000000000000 : ℝ)*(sp_s1_27) + (441385950373/200000000000 : ℝ)*(f.failure) + (5442786410827/1000000000000 : ℝ)*(f.sum) + (6403024417574899509/9352944650000000000000000000000 : ℝ)*base62 + (254524543267107/3363850000000000000000000000 : ℝ)*base64 + (27601845552499/97315000000000000000000000 : ℝ)*base66 + (186621582096923/480550000000000000000000000 : ℝ)*base68 + (87716274320346374473/264011767250000000000000000000000 : ℝ)*base70 + (1235881169623391/3924250000000000000000000000 : ℝ)*base72 + (69911249925067/194630000000000000000000000 : ℝ)*base74 + (178530768938589/3924250000000000000000000000 : ℝ)*base76 + (5450847874709863617/76377677750000000000000000000000 : ℝ)*base79 + (13139/20000000000000000 : ℝ)*base86 + (13139/20000000000000000 : ℝ)*base88 + (13139/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4651/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4651/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4497743043879147356370283712271/367032930427625000000000000000000000 : ℝ) := by norm_num
    linear_combination (416147/1000000000000 : ℝ)*(base7) + (5686823/500000000000 : ℝ)*(base11) + (374072314717/1000000000000 : ℝ)*(base39) + (461210023127/125000000000 : ℝ)*(major_s1_0) + (461210023127/125000000000 : ℝ)*(major_s1_1) + (461210023127/125000000000 : ℝ)*(major_s1_2) + (8167331/250000000000 : ℝ)*(sp_s1_0) + (4830093/1000000000000 : ℝ)*(sp_s1_1) + (2304073/100000000000 : ℝ)*(sp_s1_2) + (4260487/50000000000 : ℝ)*(sp_s1_9) + (331110579901/62500000000 : ℝ)*(sp_s1_21) + (5297808491293/1000000000000 : ℝ)*(sp_s1_22) + (1324426267729/250000000000 : ℝ)*(sp_s1_23) + (1040771569717/500000000000 : ℝ)*(sp_s1_27) + (2081542723287/1000000000000 : ℝ)*(f.failure) + (2648906660693/500000000000 : ℝ)*(f.sum) + (41475382979779327/334033737500000000000000000000 : ℝ)*base62 + (82197589413057/240275000000000000000000000 : ℝ)*base64 + (61412516801447/194630000000000000000000000 : ℝ)*base67 + (1614381745911/4290625000000000000000000 : ℝ)*base68 + (1414858341846505233/18857983375000000000000000000000 : ℝ)*base70 + (161829644794573/1962125000000000000000000000 : ℝ)*base73 + (10534554381721/24328750000000000000000000 : ℝ)*base74 + (382259611623579/981062500000000000000000000 : ℝ)*base76 + (19701574466409210377/76377677750000000000000000000000 : ℝ)*base78 + (83759/100000000000000000 : ℝ)*base87 + (83759/100000000000000000 : ℝ)*base89 + (83759/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((15697/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15697/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19463/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19463/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67277/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-67277/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52743/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52743/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53121/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53121/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4651/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4651/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316062_s1 p hpa hpb X hX hprev0

#print axioms solution

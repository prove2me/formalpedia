-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1539_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:54.966197+00:00
-- url     : https://prove2.me/submissions/ac5c0ef0-9048-467c-9d73-2564fbca6708

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1539_s6_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350049247/10000000000 : ℝ)*x 0 + (5218889857/10000000000 : ℝ)*x 1 + (-121049041/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350049247/10000000000 : ℝ)^4575 ≤ (11167718654831/25000000000000 : ℝ)^3551 := by
    have hnat : (5350049247 : ℕ)^4575*25000000000000^3551 ≤ 11167718654831^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350049247 10000000000 11167718654831 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218889857/10000000000 : ℝ)^4575 ≤ (4326495793059/10000000000000 : ℝ)^3551 := by
    have hnat : (5218889857 : ℕ)^4575*10000000000000^3551 ≤ 4326495793059^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218889857 10000000000 4326495793059 10000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121049041/625000000 : ℝ)^4575 ≤ (12064167435283/100000000000000 : ℝ)^3551 := by
    have hnat : (121049041 : ℕ)^4575*100000000000000^3551 ≤ 12064167435283^3551*625000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121049041 625000000 12064167435283 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350049247/10000000000 : ℝ), (5218889857/10000000000 : ℝ), (-121049041/625000000 : ℝ)] ![(11167718654831/25000000000000 : ℝ), (4326495793059/10000000000000 : ℝ), (12064167435283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350049247/10000000000 : ℝ)|^4575 ≤ (11167718654831/25000000000000 : ℝ)^3551
        have hw : |(5350049247/10000000000 : ℝ)|=(5350049247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218889857/10000000000 : ℝ)|^4575 ≤ (4326495793059/10000000000000 : ℝ)^3551
        have hw : |(5218889857/10000000000 : ℝ)|=(5218889857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121049041/625000000 : ℝ)|^4575 ≤ (12064167435283/100000000000000 : ℝ)^3551
        have hw : |(-121049041/625000000 : ℝ)|=(121049041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s6_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828882539/10000000000 : ℝ)*x 0 + (1304995303/2500000000 : ℝ)*x 1 + (169645041/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828882539/10000000000 : ℝ)^4575 ≤ (2801320076853/25000000000000 : ℝ)^3551 := by
    have hnat : (1828882539 : ℕ)^4575*25000000000000^3551 ≤ 2801320076853^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828882539 10000000000 2801320076853 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304995303/2500000000 : ℝ)^4575 ≤ (21638307343441/50000000000000 : ℝ)^3551 := by
    have hnat : (1304995303 : ℕ)^4575*50000000000000^3551 ≤ 21638307343441^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304995303 2500000000 21638307343441 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169645041/312500000 : ℝ)^4575 ≤ (22759052495939/50000000000000 : ℝ)^3551 := by
    have hnat : (169645041 : ℕ)^4575*50000000000000^3551 ≤ 22759052495939^3551*312500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169645041 312500000 22759052495939 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828882539/10000000000 : ℝ), (1304995303/2500000000 : ℝ), (169645041/312500000 : ℝ)] ![(2801320076853/25000000000000 : ℝ), (21638307343441/50000000000000 : ℝ), (22759052495939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828882539/10000000000 : ℝ)|^4575 ≤ (2801320076853/25000000000000 : ℝ)^3551
        have hw : |(-1828882539/10000000000 : ℝ)|=(1828882539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304995303/2500000000 : ℝ)|^4575 ≤ (21638307343441/50000000000000 : ℝ)^3551
        have hw : |(1304995303/2500000000 : ℝ)|=(1304995303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169645041/312500000 : ℝ)|^4575 ≤ (22759052495939/50000000000000 : ℝ)^3551
        have hw : |(169645041/312500000 : ℝ)|=(169645041/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s6_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529448381/1000000000 : ℝ)*x 0 + (-863516659/5000000000 : ℝ)*x 1 + (2714320673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529448381/1000000000 : ℝ)^4575 ≤ (44074032612521/100000000000000 : ℝ)^3551 := by
    have hnat : (529448381 : ℕ)^4575*100000000000000^3551 ≤ 44074032612521^3551*1000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529448381 1000000000 44074032612521 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (863516659/5000000000 : ℝ)^4575 ≤ (1040786200063/10000000000000 : ℝ)^3551 := by
    have hnat : (863516659 : ℕ)^4575*10000000000000^3551 ≤ 1040786200063^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863516659 5000000000 1040786200063 10000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714320673/5000000000 : ℝ)^4575 ≤ (45518105359171/100000000000000 : ℝ)^3551 := by
    have hnat : (2714320673 : ℕ)^4575*100000000000000^3551 ≤ 45518105359171^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714320673 5000000000 45518105359171 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529448381/1000000000 : ℝ), (-863516659/5000000000 : ℝ), (2714320673/5000000000 : ℝ)] ![(44074032612521/100000000000000 : ℝ), (1040786200063/10000000000000 : ℝ), (45518105359171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529448381/1000000000 : ℝ)|^4575 ≤ (44074032612521/100000000000000 : ℝ)^3551
        have hw : |(529448381/1000000000 : ℝ)|=(529448381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-863516659/5000000000 : ℝ)|^4575 ≤ (1040786200063/10000000000000 : ℝ)^3551
        have hw : |(-863516659/5000000000 : ℝ)|=(863516659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714320673/5000000000 : ℝ)|^4575 ≤ (45518105359171/100000000000000 : ℝ)^3551
        have hw : |(2714320673/5000000000 : ℝ)|=(2714320673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s6_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294483833/10000000000 : ℝ)*x 0 + (5428641329/10000000000 : ℝ)*x 1 + (-1727033311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294483833/10000000000 : ℝ)^4575 ≤ (22037016429599/50000000000000 : ℝ)^3551 := by
    have hnat : (5294483833 : ℕ)^4575*50000000000000^3551 ≤ 22037016429599^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294483833 10000000000 22037016429599 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428641329/10000000000 : ℝ)^4575 ≤ (11379526293881/25000000000000 : ℝ)^3551 := by
    have hnat : (5428641329 : ℕ)^4575*25000000000000^3551 ≤ 11379526293881^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428641329 10000000000 11379526293881 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727033311/10000000000 : ℝ)^4575 ≤ (260196548657/2500000000000 : ℝ)^3551 := by
    have hnat : (1727033311 : ℕ)^4575*2500000000000^3551 ≤ 260196548657^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727033311 10000000000 260196548657 2500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294483833/10000000000 : ℝ), (5428641329/10000000000 : ℝ), (-1727033311/10000000000 : ℝ)] ![(22037016429599/50000000000000 : ℝ), (11379526293881/25000000000000 : ℝ), (260196548657/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294483833/10000000000 : ℝ)|^4575 ≤ (22037016429599/50000000000000 : ℝ)^3551
        have hw : |(5294483833/10000000000 : ℝ)|=(5294483833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428641329/10000000000 : ℝ)|^4575 ≤ (11379526293881/25000000000000 : ℝ)^3551
        have hw : |(5428641329/10000000000 : ℝ)|=(5428641329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727033311/10000000000 : ℝ)|^4575 ≤ (260196548657/2500000000000 : ℝ)^3551
        have hw : |(-1727033311/10000000000 : ℝ)|=(1727033311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s6_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34059413/80000000 : ℝ)*x 0 + (4504244531/10000000000 : ℝ)*x 1 + (502759263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34059413/80000000 : ℝ)^4575 ≤ (1040050815153/3125000000000 : ℝ)^3551 := by
    have hnat : (34059413 : ℕ)^4575*3125000000000^3551 ≤ 1040050815153^3551*80000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34059413 80000000 1040050815153 3125000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504244531/10000000000 : ℝ)^4575 ≤ (35787973483423/100000000000000 : ℝ)^3551 := by
    have hnat : (4504244531 : ℕ)^4575*100000000000000^3551 ≤ 35787973483423^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504244531 10000000000 35787973483423 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502759263/1250000000 : ℝ)^4575 ≤ (15465200208487/50000000000000 : ℝ)^3551 := by
    have hnat : (502759263 : ℕ)^4575*50000000000000^3551 ≤ 15465200208487^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502759263 1250000000 15465200208487 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34059413/80000000 : ℝ), (4504244531/10000000000 : ℝ), (502759263/1250000000 : ℝ)] ![(1040050815153/3125000000000 : ℝ), (35787973483423/100000000000000 : ℝ), (15465200208487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34059413/80000000 : ℝ)|^4575 ≤ (1040050815153/3125000000000 : ℝ)^3551
        have hw : |(34059413/80000000 : ℝ)|=(34059413/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504244531/10000000000 : ℝ)|^4575 ≤ (35787973483423/100000000000000 : ℝ)^3551
        have hw : |(4504244531/10000000000 : ℝ)|=(4504244531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502759263/1250000000 : ℝ)|^4575 ≤ (15465200208487/50000000000000 : ℝ)^3551
        have hw : |(502759263/1250000000 : ℝ)|=(502759263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1377/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1377/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1377/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1377/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1377/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1377/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1377/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1377/12500 : ℝ) ^ (4573/1024 : ℝ) ≤ (5270490021380373/100000000000000000000 : ℝ) := by
    have hpowers : (1377/12500 : ℝ)^4573 ≤ (5270490021380373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1377 : ℕ)^4573*100000000000000000000^1024 ≤ 5270490021380373^1024*12500^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1377 12500 5270490021380373 100000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1377/12500 : ℝ)) (X := (5270490021380373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4573/1024 : ℝ) ≤ (12057548837611087/50000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4573 ≤ (12057548837611087/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4573*50000000000000000000^1024 ≤ 12057548837611087^1024*20000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 12057548837611087 50000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (12057548837611087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005270490021380373/50000000000000000000 : ℝ) ≤ (5000118013580639/5000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50005270490021380373/50000000000000000000 : ℝ)^1024 ≤ (5000118013580639/5000000000000000 : ℝ)^4573 := by
      have hnat : (50005270490021380373 : ℕ)^1024*5000000000000000^4573 ≤ 5000118013580639^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005270490021380373 50000000000000000000 5000118013580639 5000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000118013580639/5000000000000000 : ℝ)) (X := (50005270490021380373/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029385587696602547/100000000000000000000 : ℝ) ≤ (10000657935954909/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (100029385587696602547/100000000000000000000 : ℝ)^1024 ≤ (10000657935954909/10000000000000000 : ℝ)^4573 := by
      have hnat : (100029385587696602547 : ℕ)^1024*10000000000000000^4573 ≤ 10000657935954909^4573*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029385587696602547 100000000000000000000 10000657935954909 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000657935954909/10000000000000000 : ℝ)) (X := (100029385587696602547/100000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012057548837611087/25000000000000000000 : ℝ) ≤ (500053992237427/500000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (25012057548837611087/25000000000000000000 : ℝ)^1024 ≤ (500053992237427/500000000000000 : ℝ)^4573 := by
      have hnat : (25012057548837611087 : ℕ)^1024*500000000000000^4573 ≤ 500053992237427^4573*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012057548837611087 25000000000000000000 500053992237427 500000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500053992237427/500000000000000 : ℝ)) (X := (25012057548837611087/25000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5270490021380373/100000000000000000000 : ℝ) ≤ ((4468175931084247319/4469000000000000000 : ℝ)+2*(421908793631/446900000000000 : ℝ)*(1377/12500 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (4468175931084247319/4469000000000000000 : ℝ)+2*(421908793631/446900000000000 : ℝ)*(1377/12500 : ℝ)=(5000118013580639/5000000000000000 : ℝ) by norm_num, show 1+2*(5270490021380373/100000000000000000000 : ℝ)=(50005270490021380373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12057548837611087/50000000000000000000 : ℝ)+(5270490021380373/100000000000000000000 : ℝ) ≤ ((4468175931084247319/4469000000000000000 : ℝ)+(421908793631/446900000000000 : ℝ)*((3097/20000 : ℝ)+(1377/12500 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (4468175931084247319/4469000000000000000 : ℝ)+(421908793631/446900000000000 : ℝ)*((3097/20000 : ℝ)+(1377/12500 : ℝ))=(10000657935954909/10000000000000000 : ℝ) by norm_num, show 1+(12057548837611087/50000000000000000000 : ℝ)+(5270490021380373/100000000000000000000 : ℝ)=(100029385587696602547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12057548837611087/50000000000000000000 : ℝ) ≤ ((4468175931084247319/4469000000000000000 : ℝ)+2*(421908793631/446900000000000 : ℝ)*(3097/20000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (4468175931084247319/4469000000000000000 : ℝ)+2*(421908793631/446900000000000 : ℝ)*(3097/20000 : ℝ)=(500053992237427/500000000000000 : ℝ) by norm_num, show 1+2*(12057548837611087/50000000000000000000 : ℝ)=(25012057548837611087/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4468175931084247319/4469000000000000000 : ℝ)*(X 1 0+X 2 0)+(421908793631/446900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1377/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4468175931084247319/4469000000000000000 : ℝ)) (alpha := (421908793631/446900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4468175931084247319/4469000000000000000 : ℝ)*(X 0 1+X 2 1)+(421908793631/446900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1377/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4468175931084247319/4469000000000000000 : ℝ)) (alpha := (421908793631/446900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4468175931084247319/4469000000000000000 : ℝ)*(X 0 2+X 1 2)+(421908793631/446900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1377/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4468175931084247319/4469000000000000000 : ℝ)) (alpha := (421908793631/446900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5350049247/10000000000 : ℝ)*X 2 0+(5218889857/10000000000 : ℝ)*X 2 1+(-121049041/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1828882539/10000000000 : ℝ)*X 0 0+(1304995303/2500000000 : ℝ)*X 0 1+(169645041/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529448381/1000000000 : ℝ)*X 1 0+(-863516659/5000000000 : ℝ)*X 1 1+(2714320673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5294483833/10000000000 : ℝ)*X 2 0+(5428641329/10000000000 : ℝ)*X 2 1+(-1727033311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((34059413/80000000 : ℝ)*X 0 0+(4504244531/10000000000 : ℝ)*X 0 1+(502759263/1250000000 : ℝ)*X 0 2+(34059413/80000000 : ℝ)*X 1 0+(4504244531/10000000000 : ℝ)*X 1 1+(502759263/1250000000 : ℝ)*X 1 2+(34059413/80000000 : ℝ)*X 2 0+(4504244531/10000000000 : ℝ)*X 2 1+(502759263/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67301121660128230176001269/22345000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258000383/50000000000000 : ℝ)*(base19) + (590308781/100000000000000 : ℝ)*(base23) + (45249541/25000000000000 : ℝ)*(lower1) + (7117871/10000000000000 : ℝ)*(upper3) + (23153849/100000000000000 : ℝ)*(lower4) + (71722141/100000000000000 : ℝ)*(upper5) + (343321294140983/10000000000000 : ℝ)*(major0) + (343321294140983/10000000000000 : ℝ)*(major1) + (343321294140983/10000000000000 : ℝ)*(major2) + (23241629/2500000000000 : ℝ)*(sp0) + (2396237067448013/50000000000000 : ℝ)*(sp1) + (239623680944763/5000000000000 : ℝ)*(sp2) + (958494522984417/20000000000000 : ℝ)*(sp3) + (259243955940829/12500000000000 : ℝ)*(sp4) + (259243955940829/12500000000000 : ℝ)*(f.failure) + (2396237067448013/50000000000000 : ℝ)*(f.sum) + (162977693467/69828125000000000000000000 : ℝ)*base66 + (620071343400744577/44690000000000000000000000000000 : ℝ)*base67 + (85331290991095423/44690000000000000000000000000000 : ℝ)*base70 + (1005736904474504577/44690000000000000000000000000000 : ℝ)*base71 + (261272369409/2234500000000000000000000000 : ℝ)*base73 + (2251455455941784577/44690000000000000000000000000000 : ℝ)*base75 + (274700673975745423/44690000000000000000000000000000 : ℝ)*base78 + (737039840183374577/44690000000000000000000000000000 : ℝ)*base79 + (22167688519369/4469000000000000000000000000 : ℝ)*base81 + (12535549/1250000000000000000000 : ℝ)*base89 + (12535549/1250000000000000000000 : ℝ)*base91 + (12535549/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1539_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1539_box_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-809968559/5000000000 : ℝ)*x 0 + (5399918779/10000000000 : ℝ)*x 1 + (269995917/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809968559/5000000000 : ℝ)^4575 ≤ (4791942086109/50000000000000 : ℝ)^3551 := by
    have hnat : (809968559 : ℕ)^4575*50000000000000^3551 ≤ 4791942086109^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809968559 5000000000 4791942086109 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399918779/10000000000 : ℝ)^4575 ≤ (9041612055053/20000000000000 : ℝ)^3551 := by
    have hnat : (5399918779 : ℕ)^4575*20000000000000^3551 ≤ 9041612055053^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399918779 10000000000 9041612055053 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269995917/500000000 : ℝ)^4575 ≤ (45208055540117/100000000000000 : ℝ)^3551 := by
    have hnat : (269995917 : ℕ)^4575*100000000000000^3551 ≤ 45208055540117^3551*500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269995917 500000000 45208055540117 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-809968559/5000000000 : ℝ), (5399918779/10000000000 : ℝ), (269995917/500000000 : ℝ)] ![(4791942086109/50000000000000 : ℝ), (9041612055053/20000000000000 : ℝ), (45208055540117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-809968559/5000000000 : ℝ)|^4575 ≤ (4791942086109/50000000000000 : ℝ)^3551
        have hw : |(-809968559/5000000000 : ℝ)|=(809968559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399918779/10000000000 : ℝ)|^4575 ≤ (9041612055053/20000000000000 : ℝ)^3551
        have hw : |(5399918779/10000000000 : ℝ)|=(5399918779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269995917/500000000 : ℝ)|^4575 ≤ (45208055540117/100000000000000 : ℝ)^3551
        have hw : |(269995917/500000000 : ℝ)|=(269995917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271039971/10000000000 : ℝ)*x 0 + (-1798901479/10000000000 : ℝ)*x 1 + (5399918847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271039971/10000000000 : ℝ)^4575 ≤ (43822756811487/100000000000000 : ℝ)^3551 := by
    have hnat : (5271039971 : ℕ)^4575*100000000000000^3551 ≤ 43822756811487^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271039971 10000000000 43822756811487 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798901479/10000000000 : ℝ)^4575 ≤ (10969182168911/100000000000000 : ℝ)^3551 := by
    have hnat : (1798901479 : ℕ)^4575*100000000000000^3551 ≤ 10969182168911^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798901479 10000000000 10969182168911 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399918847/10000000000 : ℝ)^4575 ≤ (5651007626091/12500000000000 : ℝ)^3551 := by
    have hnat : (5399918847 : ℕ)^4575*12500000000000^3551 ≤ 5651007626091^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399918847 10000000000 5651007626091 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271039971/10000000000 : ℝ), (-1798901479/10000000000 : ℝ), (5399918847/10000000000 : ℝ)] ![(43822756811487/100000000000000 : ℝ), (10969182168911/100000000000000 : ℝ), (5651007626091/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271039971/10000000000 : ℝ)|^4575 ≤ (43822756811487/100000000000000 : ℝ)^3551
        have hw : |(5271039971/10000000000 : ℝ)|=(5271039971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1798901479/10000000000 : ℝ)|^4575 ≤ (10969182168911/100000000000000 : ℝ)^3551
        have hw : |(-1798901479/10000000000 : ℝ)|=(1798901479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399918847/10000000000 : ℝ)|^4575 ≤ (5651007626091/12500000000000 : ℝ)^3551
        have hw : |(5399918847/10000000000 : ℝ)|=(5399918847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635520211/5000000000 : ℝ)*x 0 + (5399918441/10000000000 : ℝ)*x 1 + (-89945071/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635520211/5000000000 : ℝ)^4575 ≤ (43822761642301/100000000000000 : ℝ)^3551 := by
    have hnat : (2635520211 : ℕ)^4575*100000000000000^3551 ≤ 43822761642301^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635520211 5000000000 43822761642301 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399918441/10000000000 : ℝ)^4575 ≤ (1808322265181/4000000000000 : ℝ)^3551 := by
    have hnat : (5399918441 : ℕ)^4575*4000000000000^3551 ≤ 1808322265181^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399918441 10000000000 1808322265181 4000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89945071/500000000 : ℝ)^4575 ≤ (10969181705401/100000000000000 : ℝ)^3551 := by
    have hnat : (89945071 : ℕ)^4575*100000000000000^3551 ≤ 10969181705401^3551*500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89945071 500000000 10969181705401 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635520211/5000000000 : ℝ), (5399918441/10000000000 : ℝ), (-89945071/500000000 : ℝ)] ![(43822761642301/100000000000000 : ℝ), (1808322265181/4000000000000 : ℝ), (10969181705401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635520211/5000000000 : ℝ)|^4575 ≤ (43822761642301/100000000000000 : ℝ)^3551
        have hw : |(2635520211/5000000000 : ℝ)|=(2635520211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399918441/10000000000 : ℝ)|^4575 ≤ (1808322265181/4000000000000 : ℝ)^3551
        have hw : |(5399918441/10000000000 : ℝ)|=(5399918441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89945071/500000000 : ℝ)|^4575 ≤ (10969181705401/100000000000000 : ℝ)^3551
        have hw : |(-89945071/500000000 : ℝ)|=(89945071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2229627749/5000000000 : ℝ)*x 0 + (4163228779/10000000000 : ℝ)*x 1 + (2081614487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2229627749/5000000000 : ℝ)^4575 ≤ (35328103729453/100000000000000 : ℝ)^3551 := by
    have hnat : (2229627749 : ℕ)^4575*100000000000000^3551 ≤ 35328103729453^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229627749 5000000000 35328103729453 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4163228779/10000000000 : ℝ)^4575 ≤ (32335947154637/100000000000000 : ℝ)^3551 := by
    have hnat : (4163228779 : ℕ)^4575*100000000000000^3551 ≤ 32335947154637^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163228779 10000000000 32335947154637 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081614487/5000000000 : ℝ)^4575 ≤ (6467189821193/20000000000000 : ℝ)^3551 := by
    have hnat : (2081614487 : ℕ)^4575*20000000000000^3551 ≤ 6467189821193^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081614487 5000000000 6467189821193 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2229627749/5000000000 : ℝ), (4163228779/10000000000 : ℝ), (2081614487/5000000000 : ℝ)] ![(35328103729453/100000000000000 : ℝ), (32335947154637/100000000000000 : ℝ), (6467189821193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2229627749/5000000000 : ℝ)|^4575 ≤ (35328103729453/100000000000000 : ℝ)^3551
        have hw : |(2229627749/5000000000 : ℝ)|=(2229627749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4163228779/10000000000 : ℝ)|^4575 ≤ (32335947154637/100000000000000 : ℝ)^3551
        have hw : |(4163228779/10000000000 : ℝ)|=(4163228779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081614487/5000000000 : ℝ)|^4575 ≤ (6467189821193/20000000000000 : ℝ)^3551
        have hw : |(2081614487/5000000000 : ℝ)|=(2081614487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021596129/5000000000 : ℝ)*x 0 + (163887481/312500000 : ℝ)*x 1 + (1311099691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021596129/5000000000 : ℝ)^4575 ≤ (6462394641847/50000000000000 : ℝ)^3551 := by
    have hnat : (1021596129 : ℕ)^4575*50000000000000^3551 ≤ 6462394641847^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021596129 5000000000 6462394641847 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163887481/312500000 : ℝ)^4575 ≤ (8707521741071/20000000000000 : ℝ)^3551 := by
    have hnat : (163887481 : ℕ)^4575*20000000000000^3551 ≤ 8707521741071^3551*312500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163887481 312500000 8707521741071 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311099691/2500000000 : ℝ)^4575 ≤ (8707520397691/20000000000000 : ℝ)^3551 := by
    have hnat : (1311099691 : ℕ)^4575*20000000000000^3551 ≤ 8707520397691^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311099691 2500000000 8707520397691 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021596129/5000000000 : ℝ), (163887481/312500000 : ℝ), (1311099691/2500000000 : ℝ)] ![(6462394641847/50000000000000 : ℝ), (8707521741071/20000000000000 : ℝ), (8707520397691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021596129/5000000000 : ℝ)|^4575 ≤ (6462394641847/50000000000000 : ℝ)^3551
        have hw : |(-1021596129/5000000000 : ℝ)|=(1021596129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163887481/312500000 : ℝ)|^4575 ≤ (8707521741071/20000000000000 : ℝ)^3551
        have hw : |(163887481/312500000 : ℝ)|=(163887481/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311099691/2500000000 : ℝ)|^4575 ≤ (8707520397691/20000000000000 : ℝ)^3551
        have hw : |(1311099691/2500000000 : ℝ)|=(1311099691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379092851/10000000000 : ℝ)*x 0 + (-232930591/1250000000 : ℝ)*x 1 + (1048879823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379092851/10000000000 : ℝ)^4575 ≤ (22491776183431/50000000000000 : ℝ)^3551 := by
    have hnat : (5379092851 : ℕ)^4575*50000000000000^3551 ≤ 22491776183431^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379092851 10000000000 22491776183431 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232930591/1250000000 : ℝ)^4575 ≤ (11478841877049/100000000000000 : ℝ)^3551 := by
    have hnat : (232930591 : ℕ)^4575*100000000000000^3551 ≤ 11478841877049^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232930591 1250000000 11478841877049 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048879823/2000000000 : ℝ)^4575 ≤ (21768802871323/50000000000000 : ℝ)^3551 := by
    have hnat : (1048879823 : ℕ)^4575*50000000000000^3551 ≤ 21768802871323^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048879823 2000000000 21768802871323 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379092851/10000000000 : ℝ), (-232930591/1250000000 : ℝ), (1048879823/2000000000 : ℝ)] ![(22491776183431/50000000000000 : ℝ), (11478841877049/100000000000000 : ℝ), (21768802871323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379092851/10000000000 : ℝ)|^4575 ≤ (22491776183431/50000000000000 : ℝ)^3551
        have hw : |(5379092851/10000000000 : ℝ)|=(5379092851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232930591/1250000000 : ℝ)|^4575 ≤ (11478841877049/100000000000000 : ℝ)^3551
        have hw : |(-232930591/1250000000 : ℝ)|=(232930591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048879823/2000000000 : ℝ)|^4575 ≤ (21768802871323/50000000000000 : ℝ)^3551
        have hw : |(1048879823/2000000000 : ℝ)|=(1048879823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379093583/10000000000 : ℝ)*x 0 + (2622199417/5000000000 : ℝ)*x 1 + (-931722057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379093583/10000000000 : ℝ)^4575 ≤ (44983560253579/100000000000000 : ℝ)^3551 := by
    have hnat : (5379093583 : ℕ)^4575*100000000000000^3551 ≤ 44983560253579^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379093583 10000000000 44983560253579 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622199417/5000000000 : ℝ)^4575 ≤ (21768801368577/50000000000000 : ℝ)^3551 := by
    have hnat : (2622199417 : ℕ)^4575*50000000000000^3551 ≤ 21768801368577^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622199417 5000000000 21768801368577 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931722057/5000000000 : ℝ)^4575 ≤ (11478837004117/100000000000000 : ℝ)^3551 := by
    have hnat : (931722057 : ℕ)^4575*100000000000000^3551 ≤ 11478837004117^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931722057 5000000000 11478837004117 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379093583/10000000000 : ℝ), (2622199417/5000000000 : ℝ), (-931722057/5000000000 : ℝ)] ![(44983560253579/100000000000000 : ℝ), (21768801368577/50000000000000 : ℝ), (11478837004117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379093583/10000000000 : ℝ)|^4575 ≤ (44983560253579/100000000000000 : ℝ)^3551
        have hw : |(5379093583/10000000000 : ℝ)|=(5379093583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622199417/5000000000 : ℝ)|^4575 ≤ (21768801368577/50000000000000 : ℝ)^3551
        have hw : |(2622199417/5000000000 : ℝ)|=(2622199417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931722057/5000000000 : ℝ)|^4575 ≤ (11478837004117/100000000000000 : ℝ)^3551
        have hw : |(-931722057/5000000000 : ℝ)|=(931722057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4052920567/10000000000 : ℝ)*x 0 + (873253009/2000000000 : ℝ)*x 1 + (4366265761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4052920567/10000000000 : ℝ)^4575 ≤ (6247271481287/20000000000000 : ℝ)^3551 := by
    have hnat : (4052920567 : ℕ)^4575*20000000000000^3551 ≤ 6247271481287^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052920567 10000000000 6247271481287 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873253009/2000000000 : ℝ)^4575 ≤ (34381817660269/100000000000000 : ℝ)^3551 := by
    have hnat : (873253009 : ℕ)^4575*100000000000000^3551 ≤ 34381817660269^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873253009 2000000000 34381817660269 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4366265761/10000000000 : ℝ)^4575 ≤ (2148864057763/6250000000000 : ℝ)^3551 := by
    have hnat : (4366265761 : ℕ)^4575*6250000000000^3551 ≤ 2148864057763^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366265761 10000000000 2148864057763 6250000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4052920567/10000000000 : ℝ), (873253009/2000000000 : ℝ), (4366265761/10000000000 : ℝ)] ![(6247271481287/20000000000000 : ℝ), (34381817660269/100000000000000 : ℝ), (2148864057763/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4052920567/10000000000 : ℝ)|^4575 ≤ (6247271481287/20000000000000 : ℝ)^3551
        have hw : |(4052920567/10000000000 : ℝ)|=(4052920567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873253009/2000000000 : ℝ)|^4575 ≤ (34381817660269/100000000000000 : ℝ)^3551
        have hw : |(873253009/2000000000 : ℝ)|=(873253009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4366265761/10000000000 : ℝ)|^4575 ≤ (2148864057763/6250000000000 : ℝ)^3551
        have hw : |(4366265761/10000000000 : ℝ)|=(4366265761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_8 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953614213/10000000000 : ℝ)*x 0 + (2567578191/5000000000 : ℝ)*x 1 + (2710144533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953614213/10000000000 : ℝ)^4575 ≤ (3049849261231/25000000000000 : ℝ)^3551 := by
    have hnat : (1953614213 : ℕ)^4575*25000000000000^3551 ≤ 3049849261231^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953614213 10000000000 3049849261231 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567578191/5000000000 : ℝ)^4575 ≤ (1324147030159/3125000000000 : ℝ)^3551 := by
    have hnat : (2567578191 : ℕ)^4575*3125000000000^3551 ≤ 1324147030159^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567578191 5000000000 1324147030159 3125000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710144533/5000000000 : ℝ)^4575 ≤ (45427897970801/100000000000000 : ℝ)^3551 := by
    have hnat : (2710144533 : ℕ)^4575*100000000000000^3551 ≤ 45427897970801^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710144533 5000000000 45427897970801 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953614213/10000000000 : ℝ), (2567578191/5000000000 : ℝ), (2710144533/5000000000 : ℝ)] ![(3049849261231/25000000000000 : ℝ), (1324147030159/3125000000000 : ℝ), (45427897970801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953614213/10000000000 : ℝ)|^4575 ≤ (3049849261231/25000000000000 : ℝ)^3551
        have hw : |(-1953614213/10000000000 : ℝ)|=(1953614213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567578191/5000000000 : ℝ)|^4575 ≤ (1324147030159/3125000000000 : ℝ)^3551
        have hw : |(2567578191/5000000000 : ℝ)|=(2567578191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710144533/5000000000 : ℝ)|^4575 ≤ (45427897970801/100000000000000 : ℝ)^3551
        have hw : |(2710144533/5000000000 : ℝ)|=(2710144533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_9 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051376773/2000000000 : ℝ)*x 0 + (-447552111/2500000000 : ℝ)*x 1 + (2710143649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051376773/2000000000 : ℝ)^4575 ≤ (43671184697979/100000000000000 : ℝ)^3551 := by
    have hnat : (1051376773 : ℕ)^4575*100000000000000^3551 ≤ 43671184697979^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051376773 2000000000 43671184697979 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447552111/2500000000 : ℝ)^4575 ≤ (5450468204651/50000000000000 : ℝ)^3551 := by
    have hnat : (447552111 : ℕ)^4575*50000000000000^3551 ≤ 5450468204651^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447552111 2500000000 5450468204651 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710143649/5000000000 : ℝ)^4575 ≤ (45427878880057/100000000000000 : ℝ)^3551 := by
    have hnat : (2710143649 : ℕ)^4575*100000000000000^3551 ≤ 45427878880057^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710143649 5000000000 45427878880057 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051376773/2000000000 : ℝ), (-447552111/2500000000 : ℝ), (2710143649/5000000000 : ℝ)] ![(43671184697979/100000000000000 : ℝ), (5450468204651/50000000000000 : ℝ), (45427878880057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051376773/2000000000 : ℝ)|^4575 ≤ (43671184697979/100000000000000 : ℝ)^3551
        have hw : |(1051376773/2000000000 : ℝ)|=(1051376773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447552111/2500000000 : ℝ)|^4575 ≤ (5450468204651/50000000000000 : ℝ)^3551
        have hw : |(-447552111/2500000000 : ℝ)|=(447552111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710143649/5000000000 : ℝ)|^4575 ≤ (45427878880057/100000000000000 : ℝ)^3551
        have hw : |(2710143649/5000000000 : ℝ)|=(2710143649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_10 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256882383/10000000000 : ℝ)*x 0 + (5420289083/10000000000 : ℝ)*x 1 + (-1790208009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256882383/10000000000 : ℝ)^4575 ≤ (43671168836079/100000000000000 : ℝ)^3551 := by
    have hnat : (5256882383 : ℕ)^4575*100000000000000^3551 ≤ 43671168836079^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256882383 10000000000 43671168836079 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420289083/10000000000 : ℝ)^4575 ≤ (22713949077183/50000000000000 : ℝ)^3551 := by
    have hnat : (5420289083 : ℕ)^4575*50000000000000^3551 ≤ 22713949077183^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420289083 10000000000 22713949077183 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790208009/10000000000 : ℝ)^4575 ≤ (5450466498333/50000000000000 : ℝ)^3551 := by
    have hnat : (1790208009 : ℕ)^4575*50000000000000^3551 ≤ 5450466498333^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790208009 10000000000 5450466498333 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256882383/10000000000 : ℝ), (5420289083/10000000000 : ℝ), (-1790208009/10000000000 : ℝ)] ![(43671168836079/100000000000000 : ℝ), (22713949077183/50000000000000 : ℝ), (5450466498333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256882383/10000000000 : ℝ)|^4575 ≤ (43671168836079/100000000000000 : ℝ)^3551
        have hw : |(5256882383/10000000000 : ℝ)|=(5256882383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420289083/10000000000 : ℝ)|^4575 ≤ (22713949077183/50000000000000 : ℝ)^3551
        have hw : |(5420289083/10000000000 : ℝ)|=(5420289083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790208009/10000000000 : ℝ)|^4575 ≤ (5450466498333/50000000000000 : ℝ)^3551
        have hw : |(-1790208009/10000000000 : ℝ)|=(1790208009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_11 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (140979053/312500000 : ℝ)*x 0 + (4136601671/10000000000 : ℝ)*x 1 + (1034150431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140979053/312500000 : ℝ)^4575 ≤ (8965129475017/25000000000000 : ℝ)^3551 := by
    have hnat : (140979053 : ℕ)^4575*25000000000000^3551 ≤ 8965129475017^3551*312500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140979053 312500000 8965129475017 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4136601671/10000000000 : ℝ)^4575 ≤ (16034870391689/50000000000000 : ℝ)^3551 := by
    have hnat : (4136601671 : ℕ)^4575*50000000000000^3551 ≤ 16034870391689^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136601671 10000000000 16034870391689 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034150431/2500000000 : ℝ)^4575 ≤ (16034870656379/50000000000000 : ℝ)^3551 := by
    have hnat : (1034150431 : ℕ)^4575*50000000000000^3551 ≤ 16034870656379^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034150431 2500000000 16034870656379 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140979053/312500000 : ℝ), (4136601671/10000000000 : ℝ), (1034150431/2500000000 : ℝ)] ![(8965129475017/25000000000000 : ℝ), (16034870391689/50000000000000 : ℝ), (16034870656379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140979053/312500000 : ℝ)|^4575 ≤ (8965129475017/25000000000000 : ℝ)^3551
        have hw : |(140979053/312500000 : ℝ)|=(140979053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4136601671/10000000000 : ℝ)|^4575 ≤ (16034870391689/50000000000000 : ℝ)^3551
        have hw : |(4136601671/10000000000 : ℝ)|=(4136601671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034150431/2500000000 : ℝ)|^4575 ≤ (16034870656379/50000000000000 : ℝ)^3551
        have hw : |(1034150431/2500000000 : ℝ)|=(1034150431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_12 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1709324243/10000000000 : ℝ)*x 0 + (2752868733/5000000000 : ℝ)*x 1 + (2614678153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1709324243/10000000000 : ℝ)^4575 ≤ (5135283776823/50000000000000 : ℝ)^3551 := by
    have hnat : (1709324243 : ℕ)^4575*50000000000000^3551 ≤ 5135283776823^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709324243 10000000000 5135283776823 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752868733/5000000000 : ℝ)^4575 ≤ (46352653486529/100000000000000 : ℝ)^3551 := by
    have hnat : (2752868733 : ℕ)^4575*100000000000000^3551 ≤ 46352653486529^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752868733 5000000000 46352653486529 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614678153/5000000000 : ℝ)^4575 ≤ (5422097368699/12500000000000 : ℝ)^3551 := by
    have hnat : (2614678153 : ℕ)^4575*12500000000000^3551 ≤ 5422097368699^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614678153 5000000000 5422097368699 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1709324243/10000000000 : ℝ), (2752868733/5000000000 : ℝ), (2614678153/5000000000 : ℝ)] ![(5135283776823/50000000000000 : ℝ), (46352653486529/100000000000000 : ℝ), (5422097368699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1709324243/10000000000 : ℝ)|^4575 ≤ (5135283776823/50000000000000 : ℝ)^3551
        have hw : |(-1709324243/10000000000 : ℝ)|=(1709324243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752868733/5000000000 : ℝ)|^4575 ≤ (46352653486529/100000000000000 : ℝ)^3551
        have hw : |(2752868733/5000000000 : ℝ)|=(2752868733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614678153/5000000000 : ℝ)|^4575 ≤ (5422097368699/12500000000000 : ℝ)^3551
        have hw : |(2614678153/5000000000 : ℝ)|=(2614678153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_13 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389544913/10000000000 : ℝ)*x 0 + (-1869512891/10000000000 : ℝ)*x 1 + (163417387/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389544913/10000000000 : ℝ)^4575 ≤ (45096196534921/100000000000000 : ℝ)^3551 := by
    have hnat : (5389544913 : ℕ)^4575*100000000000000^3551 ≤ 45096196534921^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389544913 10000000000 45096196534921 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1869512891/10000000000 : ℝ)^4575 ≤ (11527023666967/100000000000000 : ℝ)^3551 := by
    have hnat : (1869512891 : ℕ)^4575*100000000000000^3551 ≤ 11527023666967^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869512891 10000000000 11527023666967 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163417387/312500000 : ℝ)^4575 ≤ (21688389891583/50000000000000 : ℝ)^3551 := by
    have hnat : (163417387 : ℕ)^4575*50000000000000^3551 ≤ 21688389891583^3551*312500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163417387 312500000 21688389891583 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389544913/10000000000 : ℝ), (-1869512891/10000000000 : ℝ), (163417387/312500000 : ℝ)] ![(45096196534921/100000000000000 : ℝ), (11527023666967/100000000000000 : ℝ), (21688389891583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389544913/10000000000 : ℝ)|^4575 ≤ (45096196534921/100000000000000 : ℝ)^3551
        have hw : |(5389544913/10000000000 : ℝ)|=(5389544913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1869512891/10000000000 : ℝ)|^4575 ≤ (11527023666967/100000000000000 : ℝ)^3551
        have hw : |(-1869512891/10000000000 : ℝ)|=(1869512891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163417387/312500000 : ℝ)|^4575 ≤ (21688389891583/50000000000000 : ℝ)^3551
        have hw : |(163417387/312500000 : ℝ)|=(163417387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_14 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694772497/5000000000 : ℝ)*x 0 + (32683477/62500000 : ℝ)*x 1 + (-1869512867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694772497/5000000000 : ℝ)^4575 ≤ (1127404935203/2500000000000 : ℝ)^3551 := by
    have hnat : (2694772497 : ℕ)^4575*2500000000000^3551 ≤ 1127404935203^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694772497 5000000000 1127404935203 2500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32683477/62500000 : ℝ)^4575 ≤ (5422097387401/12500000000000 : ℝ)^3551 := by
    have hnat : (32683477 : ℕ)^4575*12500000000000^3551 ≤ 5422097387401^3551*62500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32683477 62500000 5422097387401 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869512867/10000000000 : ℝ)^4575 ≤ (2305404695263/20000000000000 : ℝ)^3551 := by
    have hnat : (1869512867 : ℕ)^4575*20000000000000^3551 ≤ 2305404695263^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869512867 10000000000 2305404695263 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694772497/5000000000 : ℝ), (32683477/62500000 : ℝ), (-1869512867/10000000000 : ℝ)] ![(1127404935203/2500000000000 : ℝ), (5422097387401/12500000000000 : ℝ), (2305404695263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694772497/5000000000 : ℝ)|^4575 ≤ (1127404935203/2500000000000 : ℝ)^3551
        have hw : |(2694772497/5000000000 : ℝ)|=(2694772497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32683477/62500000 : ℝ)|^4575 ≤ (5422097387401/12500000000000 : ℝ)^3551
        have hw : |(32683477/62500000 : ℝ)|=(32683477/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1869512867/10000000000 : ℝ)|^4575 ≤ (2305404695263/20000000000000 : ℝ)^3551
        have hw : |(-1869512867/10000000000 : ℝ)|=(1869512867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_box_15 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1003188861/2500000000 : ℝ)*x 0 + (4385880457/10000000000 : ℝ)*x 1 + (4385880433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003188861/2500000000 : ℝ)^4575 ≤ (6167620827997/20000000000000 : ℝ)^3551 := by
    have hnat : (1003188861 : ℕ)^4575*20000000000000^3551 ≤ 6167620827997^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003188861 2500000000 6167620827997 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4385880457/10000000000 : ℝ)^4575 ≤ (864523700999/2500000000000 : ℝ)^3551 := by
    have hnat : (4385880457 : ℕ)^4575*2500000000000^3551 ≤ 864523700999^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385880457 10000000000 864523700999 2500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4385880433/10000000000 : ℝ)^4575 ≤ (34580947796161/100000000000000 : ℝ)^3551 := by
    have hnat : (4385880433 : ℕ)^4575*100000000000000^3551 ≤ 34580947796161^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385880433 10000000000 34580947796161 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1003188861/2500000000 : ℝ), (4385880457/10000000000 : ℝ), (4385880433/10000000000 : ℝ)] ![(6167620827997/20000000000000 : ℝ), (864523700999/2500000000000 : ℝ), (34580947796161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1003188861/2500000000 : ℝ)|^4575 ≤ (6167620827997/20000000000000 : ℝ)^3551
        have hw : |(1003188861/2500000000 : ℝ)|=(1003188861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4385880457/10000000000 : ℝ)|^4575 ≤ (864523700999/2500000000000 : ℝ)^3551
        have hw : |(4385880457/10000000000 : ℝ)|=(4385880457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4385880433/10000000000 : ℝ)|^4575 ≤ (34580947796161/100000000000000 : ℝ)^3551
        have hw : |(4385880433/10000000000 : ℝ)|=(4385880433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(31889/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11751/20000 : ℝ) ∧ (16121/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43087/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1377/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1377/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1377/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1377/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1377/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1377/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1377/12500 : ℝ) ^ (4573/1024 : ℝ) ≤ (5270490021380373/100000000000000000000 : ℝ) := by
    have hpowers : (1377/12500 : ℝ)^4573 ≤ (5270490021380373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1377 : ℕ)^4573*100000000000000000000^1024 ≤ 5270490021380373^1024*12500^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1377 12500 5270490021380373 100000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1377/12500 : ℝ)) (X := (5270490021380373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4573/1024 : ℝ) ≤ (6027035935728581/25000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4573 ≤ (6027035935728581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4573*25000000000000000000^1024 ≤ 6027035935728581^1024*25000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 6027035935728581 25000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (6027035935728581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005270490021380373/50000000000000000000 : ℝ) ≤ (5000118013580639/5000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50005270490021380373/50000000000000000000 : ℝ)^1024 ≤ (5000118013580639/5000000000000000 : ℝ)^4573 := by
      have hnat : (50005270490021380373 : ℕ)^1024*5000000000000000^4573 ≤ 5000118013580639^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005270490021380373 50000000000000000000 5000118013580639 5000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000118013580639/5000000000000000 : ℝ)) (X := (50005270490021380373/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029378633764294697/100000000000000000000 : ℝ) ≤ (200013155605517/200000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (100029378633764294697/100000000000000000000 : ℝ)^1024 ≤ (200013155605517/200000000000000 : ℝ)^4573 := by
      have hnat : (100029378633764294697 : ℕ)^1024*200000000000000^4573 ≤ 200013155605517^4573*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029378633764294697 100000000000000000000 200013155605517 200000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013155605517/200000000000000 : ℝ)) (X := (100029378633764294697/100000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506027035935728581/12500000000000000000 : ℝ) ≤ (5000539766695211/5000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (12506027035935728581/12500000000000000000 : ℝ)^1024 ≤ (5000539766695211/5000000000000000 : ℝ)^4573 := by
      have hnat : (12506027035935728581 : ℕ)^1024*5000000000000000^4573 ≤ 5000539766695211^4573*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506027035935728581 12500000000000000000 5000539766695211 5000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000539766695211/5000000000000000 : ℝ)) (X := (12506027035935728581/12500000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5270490021380373/100000000000000000000 : ℝ) ≤ ((223358812523681699/223400000000000000 : ℝ)+2*(105438278643/111700000000000 : ℝ)*(1377/12500 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (223358812523681699/223400000000000000 : ℝ)+2*(105438278643/111700000000000 : ℝ)*(1377/12500 : ℝ)=(5000118013580639/5000000000000000 : ℝ) by norm_num, show 1+2*(5270490021380373/100000000000000000000 : ℝ)=(50005270490021380373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6027035935728581/25000000000000000000 : ℝ)+(5270490021380373/100000000000000000000 : ℝ) ≤ ((223358812523681699/223400000000000000 : ℝ)+(105438278643/111700000000000 : ℝ)*((3871/25000 : ℝ)+(1377/12500 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (223358812523681699/223400000000000000 : ℝ)+(105438278643/111700000000000 : ℝ)*((3871/25000 : ℝ)+(1377/12500 : ℝ))=(200013155605517/200000000000000 : ℝ) by norm_num, show 1+(6027035935728581/25000000000000000000 : ℝ)+(5270490021380373/100000000000000000000 : ℝ)=(100029378633764294697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6027035935728581/25000000000000000000 : ℝ) ≤ ((223358812523681699/223400000000000000 : ℝ)+2*(105438278643/111700000000000 : ℝ)*(3871/25000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (223358812523681699/223400000000000000 : ℝ)+2*(105438278643/111700000000000 : ℝ)*(3871/25000 : ℝ)=(5000539766695211/5000000000000000 : ℝ) by norm_num, show 1+2*(6027035935728581/25000000000000000000 : ℝ)=(12506027035935728581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (223358812523681699/223400000000000000 : ℝ)*(X 1 0+X 2 0)+(105438278643/111700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1377/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (223358812523681699/223400000000000000 : ℝ)) (alpha := (105438278643/111700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (223358812523681699/223400000000000000 : ℝ)*(X 0 1+X 2 1)+(105438278643/111700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1377/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (223358812523681699/223400000000000000 : ℝ)) (alpha := (105438278643/111700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (223358812523681699/223400000000000000 : ℝ)*(X 0 2+X 1 2)+(105438278643/111700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (1377/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (223358812523681699/223400000000000000 : ℝ)) (alpha := (105438278643/111700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-809968559/5000000000 : ℝ)*X 0 0+(5399918779/10000000000 : ℝ)*X 0 1+(269995917/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271039971/10000000000 : ℝ)*X 1 0+(-1798901479/10000000000 : ℝ)*X 1 1+(5399918847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635520211/5000000000 : ℝ)*X 2 0+(5399918441/10000000000 : ℝ)*X 2 1+(-89945071/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2229627749/5000000000 : ℝ)*X 0 0+(4163228779/10000000000 : ℝ)*X 0 1+(2081614487/5000000000 : ℝ)*X 0 2+(2229627749/5000000000 : ℝ)*X 1 0+(4163228779/10000000000 : ℝ)*X 1 1+(2081614487/5000000000 : ℝ)*X 1 2+(2229627749/5000000000 : ℝ)*X 2 0+(4163228779/10000000000 : ℝ)*X 2 1+(2081614487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1021596129/5000000000 : ℝ)*X 0 0+(163887481/312500000 : ℝ)*X 0 1+(1311099691/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379092851/10000000000 : ℝ)*X 1 0+(-232930591/1250000000 : ℝ)*X 1 1+(1048879823/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5379093583/10000000000 : ℝ)*X 2 0+(2622199417/5000000000 : ℝ)*X 2 1+(-931722057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4052920567/10000000000 : ℝ)*X 0 0+(873253009/2000000000 : ℝ)*X 0 1+(4366265761/10000000000 : ℝ)*X 0 2+(4052920567/10000000000 : ℝ)*X 1 0+(873253009/2000000000 : ℝ)*X 1 1+(4366265761/10000000000 : ℝ)*X 1 2+(4052920567/10000000000 : ℝ)*X 2 0+(873253009/2000000000 : ℝ)*X 2 1+(4366265761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1953614213/10000000000 : ℝ)*X 0 0+(2567578191/5000000000 : ℝ)*X 0 1+(2710144533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051376773/2000000000 : ℝ)*X 1 0+(-447552111/2500000000 : ℝ)*X 1 1+(2710143649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256882383/10000000000 : ℝ)*X 2 0+(5420289083/10000000000 : ℝ)*X 2 1+(-1790208009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((140979053/312500000 : ℝ)*X 0 0+(4136601671/10000000000 : ℝ)*X 0 1+(1034150431/2500000000 : ℝ)*X 0 2+(140979053/312500000 : ℝ)*X 1 0+(4136601671/10000000000 : ℝ)*X 1 1+(1034150431/2500000000 : ℝ)*X 1 2+(140979053/312500000 : ℝ)*X 2 0+(4136601671/10000000000 : ℝ)*X 2 1+(1034150431/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1709324243/10000000000 : ℝ)*X 0 0+(2752868733/5000000000 : ℝ)*X 0 1+(2614678153/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389544913/10000000000 : ℝ)*X 1 0+(-1869512891/10000000000 : ℝ)*X 1 1+(163417387/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2694772497/5000000000 : ℝ)*X 2 0+(32683477/62500000 : ℝ)*X 2 1+(-1869512867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1003188861/2500000000 : ℝ)*X 0 0+(4385880457/10000000000 : ℝ)*X 0 1+(4385880433/10000000000 : ℝ)*X 0 2+(1003188861/2500000000 : ℝ)*X 1 0+(4385880457/10000000000 : ℝ)*X 1 1+(4385880433/10000000000 : ℝ)*X 1 2+(1003188861/2500000000 : ℝ)*X 2 0+(4385880457/10000000000 : ℝ)*X 2 1+(4385880433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31889/50000 : ℝ) ≤ (-3561838691887857087691939307757/5585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121227113/100000000000000 : ℝ)*(upper0) + (61697003/100000000000000 : ℝ)*(lower1) + (128407839/50000000000000 : ℝ)*(lower2) + (1925487/2000000000000 : ℝ)*(lower3) + (1131507703653781/50000000000000 : ℝ)*(major0) + (1131507703653781/50000000000000 : ℝ)*(major1) + (1131507703653781/50000000000000 : ℝ)*(major2) + (238146323/12500000000000 : ℝ)*(sp3) + (198764232817901/6250000000000 : ℝ)*(sp4) + (397529504661473/12500000000000 : ℝ)*(sp5) + (1590106526226351/50000000000000 : ℝ)*(sp6) + (1367051234981089/100000000000000 : ℝ)*(sp7) + (1039025671/12500000000000 : ℝ)*(sp8) + (22984839083/100000000000000 : ℝ)*(sp14) + (1367053140151673/100000000000000 : ℝ)*(f.failure) + (397529504661473/12500000000000 : ℝ)*(f.sum) + (2998562217311/5585000000000000000000000000 : ℝ)*base65 + (33292133998910081/11170000000000000000000000000000 : ℝ)*base68 + (10352383901529919/11170000000000000000000000000000 : ℝ)*base69 + (57712359309789919/11170000000000000000000000000000 : ℝ)*base71 + (19110781182801/5585000000000000000000000000 : ℝ)*base73 + (63658640384630081/11170000000000000000000000000000 : ℝ)*base76 + (5191292036509919/11170000000000000000000000000000 : ℝ)*base77 + (1555067136489919/11170000000000000000000000000000 : ℝ)*base79 + (17389334025947/2792500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (40036313/10000000000000000000000 : ℝ)*base89 + (40036313/10000000000000000000000 : ℝ)*base91 + (40036313/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11751/20000 : ℝ) ≤ (1640807468792952113597596269/2792500000000000000000000000 : ℝ) := by norm_num
    linear_combination (48435597/50000000000000 : ℝ)*(lower1) + (56429159/50000000000000 : ℝ)*(upper4) + (15015247/50000000000000 : ℝ)*(lower5) + (585279245514843/25000000000000 : ℝ)*(major0) + (585279245514843/25000000000000 : ℝ)*(major1) + (585279245514843/25000000000000 : ℝ)*(major2) + (1624205744975353/50000000000000 : ℝ)*(sp0) + (1624205531112267/50000000000000 : ℝ)*(sp1) + (1624207087999031/50000000000000 : ℝ)*(sp2) + (176778766169047/12500000000000 : ℝ)*(sp3) + (390554187/10000000000000 : ℝ)*(sp5) + (395884171/50000000000000 : ℝ)*(sp6) + (745640491/25000000000000 : ℝ)*(sp7) + (1738907849/50000000000000 : ℝ)*(sp8) + (70711655595717/5000000000000 : ℝ)*(f.failure) + (812103741941601/25000000000000 : ℝ)*(f.sum) + (4921109676197/2792500000000000000000000000 : ℝ)*base66 + (12072966050066257/5585000000000000000000000000000 : ℝ)*base67 + (8463040089503743/5585000000000000000000000000000 : ℝ)*base70 + (43950877273143743/5585000000000000000000000000000 : ℝ)*base72 + (4417550114267/2792500000000000000000000000 : ℝ)*base74 + (30308413935096257/5585000000000000000000000000000 : ℝ)*base75 + (19272949727753743/5585000000000000000000000000000 : ℝ)*base78 + (11856368803466257/5585000000000000000000000000000 : ℝ)*base79 + (6985475814799/1396250000000000000000000000 : ℝ)*base81 + (2853723/500000000000000000000 : ℝ)*base90 + (2853723/500000000000000000000 : ℝ)*base92 + (2853723/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16121/20000 : ℝ) ≤ (4501899963317509257627127768347/5585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109035243/100000000000000 : ℝ)*(upper2) + (135511231/100000000000000 : ℝ)*(lower3) + (227039731/100000000000000 : ℝ)*(lower5) + (1265853832488583/50000000000000 : ℝ)*(major0) + (1265853832488583/50000000000000 : ℝ)*(major1) + (1265853832488583/50000000000000 : ℝ)*(major2) + (58020588437/20000000000000 : ℝ)*(sp2) + (135758046917/100000000000000 : ℝ)*(sp3) + (134992713/2500000000000 : ℝ)*(sp4) + (876788622832197/25000000000000 : ℝ)*(sp8) + (219198768450979/6250000000000 : ℝ)*(sp9) + (3506890192273479/100000000000000 : ℝ)*(sp10) + (764615141290313/50000000000000 : ℝ)*(sp11) + (5101044589/25000000000000 : ℝ)*(sp12) + (1529366040627543/100000000000000 : ℝ)*(f.failure) + (219198768450979/6250000000000 : ℝ)*(f.sum) + (636675968561/698125000000000000000000000 : ℝ)*base65 + (89091052664310517/11170000000000000000000000000000 : ℝ)*base67 + (68863238620260517/11170000000000000000000000000000 : ℝ)*base69 + (96451528844540517/11170000000000000000000000000000 : ℝ)*base71 + (3113521210533/5585000000000000000000000000 : ℝ)*base73 + (75600740812100517/11170000000000000000000000000000 : ℝ)*base75 + (74554294609150517/11170000000000000000000000000000 : ℝ)*base77 + (20806244634010517/11170000000000000000000000000000 : ℝ)*base79 + (17124650933703/5585000000000000000000000000 : ℝ)*base81 + (91966217/10000000000000000000000 : ℝ)*base90 + (91966217/10000000000000000000000 : ℝ)*base92 + (91966217/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-43087/50000 : ℝ) ≤ (-96253047770488130192614457229/111700000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35573/781250000000 : ℝ)*(lower1) + (21143627/100000000000000 : ℝ)*(lower2) + (1028611/20000000000000 : ℝ)*(upper5) + (25714093130881/1000000000000 : ℝ)*(major0) + (25714093130881/1000000000000 : ℝ)*(major1) + (25714093130881/1000000000000 : ℝ)*(major2) + (750681723/100000000000000 : ℝ)*(sp0) + (7811134369/100000000000000 : ℝ)*(sp6) + (2629282179/50000000000000 : ℝ)*(sp7) + (11380741/2000000000000 : ℝ)*(sp8) + (3618191783724937/100000000000000 : ℝ)*(sp12) + (361819310344371/10000000000000 : ℝ)*(sp13) + (3618185292309341/100000000000000 : ℝ)*(sp14) + (1553343943001459/100000000000000 : ℝ)*(sp15) + (1553349201565817/100000000000000 : ℝ)*(f.failure) + (361819310344371/10000000000000 : ℝ)*(f.sum) + (4682715077801/1117000000000000000000000000 : ℝ)*base65 + (379742446855981/223400000000000000000000000000 : ℝ)*base68 + (209628752018981/223400000000000000000000000000 : ℝ)*base70 + (1086383271667981/223400000000000000000000000000 : ℝ)*base72 + (1182291283111/1117000000000000000000000000 : ℝ)*base74 + (1551893426692181/223400000000000000000000000000 : ℝ)*base76 + (128510164781381/223400000000000000000000000000 : ℝ)*base78 + (400561518879781/223400000000000000000000000000 : ℝ)*base80 + (328514884641/279250000000000000000000000 : ℝ)*base82 + (46684377/10000000000000000000000 : ℝ)*base89 + (46684377/10000000000000000000000 : ℝ)*base91 + (46684377/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1539_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31889/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11751/20000 : ℝ) else (16121/20000 : ℝ) ≤ X j i ∧ X j i ≤ (43087/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1539_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1539_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31889/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11751/20000 : ℝ) else (16121/20000 : ℝ) ≤ X j i ∧ X j i ≤ (43087/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1539_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1539_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31889/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11751/20000 : ℝ) else (16121/20000 : ℝ) ≤ X j i ∧ X j i ≤ (43087/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1539_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

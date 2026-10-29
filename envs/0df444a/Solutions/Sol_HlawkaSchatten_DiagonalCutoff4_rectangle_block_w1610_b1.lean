-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:06.982246+00:00
-- url     : https://prove2.me/submissions/bef0ed49-15a9-4b37-8270-9915a3bce640

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
theorem support_rectangle_w1610_s3_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-852082971/5000000000 : ℝ)*x 0 + (5460019933/10000000000 : ℝ)*x 1 + (5180310707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852082971/5000000000 : ℝ)^4759 ≤ (5245545181351/50000000000000 : ℝ)^3735 := by
    have hnat : (852082971 : ℕ)^4759*50000000000000^3735 ≤ 5245545181351^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852082971 5000000000 5245545181351 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460019933/10000000000 : ℝ)^4759 ≤ (185013115577/400000000000 : ℝ)^3735 := by
    have hnat : (5460019933 : ℕ)^4759*400000000000^3735 ≤ 185013115577^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460019933 10000000000 185013115577 400000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180310707/10000000000 : ℝ)^4759 ≤ (43255630731793/100000000000000 : ℝ)^3735 := by
    have hnat : (5180310707 : ℕ)^4759*100000000000000^3735 ≤ 43255630731793^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180310707 10000000000 43255630731793 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-852082971/5000000000 : ℝ), (5460019933/10000000000 : ℝ), (5180310707/10000000000 : ℝ)] ![(5245545181351/50000000000000 : ℝ), (185013115577/400000000000 : ℝ), (43255630731793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-852082971/5000000000 : ℝ)|^4759 ≤ (5245545181351/50000000000000 : ℝ)^3735
        have hw : |(-852082971/5000000000 : ℝ)|=(852082971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460019933/10000000000 : ℝ)|^4759 ≤ (185013115577/400000000000 : ℝ)^3735
        have hw : |(5460019933/10000000000 : ℝ)|=(5460019933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180310707/10000000000 : ℝ)|^4759 ≤ (43255630731793/100000000000000 : ℝ)^3735
        have hw : |(5180310707/10000000000 : ℝ)|=(5180310707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66921457/125000000 : ℝ)*x 0 + (-1848414351/10000000000 : ℝ)*x 1 + (323769383/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66921457/125000000 : ℝ)^4759 ≤ (5638617624267/12500000000000 : ℝ)^3735 := by
    have hnat : (66921457 : ℕ)^4759*12500000000000^3735 ≤ 5638617624267^3735*125000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66921457 125000000 5638617624267 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848414351/10000000000 : ℝ)^4759 ≤ (11635434408503/100000000000000 : ℝ)^3735 := by
    have hnat : (1848414351 : ℕ)^4759*100000000000000^3735 ≤ 11635434408503^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848414351 10000000000 11635434408503 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323769383/625000000 : ℝ)^4759 ≤ (21627812285827/50000000000000 : ℝ)^3735 := by
    have hnat : (323769383 : ℕ)^4759*50000000000000^3735 ≤ 21627812285827^3735*625000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323769383 625000000 21627812285827 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66921457/125000000 : ℝ), (-1848414351/10000000000 : ℝ), (323769383/625000000 : ℝ)] ![(5638617624267/12500000000000 : ℝ), (11635434408503/100000000000000 : ℝ), (21627812285827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66921457/125000000 : ℝ)|^4759 ≤ (5638617624267/12500000000000 : ℝ)^3735
        have hw : |(66921457/125000000 : ℝ)|=(66921457/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1848414351/10000000000 : ℝ)|^4759 ≤ (11635434408503/100000000000000 : ℝ)^3735
        have hw : |(-1848414351/10000000000 : ℝ)|=(1848414351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323769383/625000000 : ℝ)|^4759 ≤ (21627812285827/50000000000000 : ℝ)^3735
        have hw : |(323769383/625000000 : ℝ)|=(323769383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353716583/10000000000 : ℝ)*x 0 + (1295077481/2500000000 : ℝ)*x 1 + (-1848414593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353716583/10000000000 : ℝ)^4759 ≤ (45108941241059/100000000000000 : ℝ)^3735 := by
    have hnat : (5353716583 : ℕ)^4759*100000000000000^3735 ≤ 45108941241059^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353716583 10000000000 45108941241059 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295077481/2500000000 : ℝ)^4759 ≤ (21627811200621/50000000000000 : ℝ)^3735 := by
    have hnat : (1295077481 : ℕ)^4759*50000000000000^3735 ≤ 21627811200621^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295077481 2500000000 21627811200621 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848414593/10000000000 : ℝ)^4759 ≤ (2327087269899/20000000000000 : ℝ)^3735 := by
    have hnat : (1848414593 : ℕ)^4759*20000000000000^3735 ≤ 2327087269899^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848414593 10000000000 2327087269899 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353716583/10000000000 : ℝ), (1295077481/2500000000 : ℝ), (-1848414593/10000000000 : ℝ)] ![(45108941241059/100000000000000 : ℝ), (21627811200621/50000000000000 : ℝ), (2327087269899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353716583/10000000000 : ℝ)|^4759 ≤ (45108941241059/100000000000000 : ℝ)^3735
        have hw : |(5353716583/10000000000 : ℝ)|=(5353716583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295077481/2500000000 : ℝ)|^4759 ≤ (21627811200621/50000000000000 : ℝ)^3735
        have hw : |(1295077481/2500000000 : ℝ)|=(1295077481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1848414593/10000000000 : ℝ)|^4759 ≤ (2327087269899/20000000000000 : ℝ)^3735
        have hw : |(-1848414593/10000000000 : ℝ)|=(1848414593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053117721/2500000000 : ℝ)*x 0 + (3879594869/10000000000 : ℝ)*x 1 + (4566937283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053117721/2500000000 : ℝ)^4759 ≤ (33235231286903/100000000000000 : ℝ)^3735 := by
    have hnat : (1053117721 : ℕ)^4759*100000000000000^3735 ≤ 33235231286903^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053117721 2500000000 33235231286903 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3879594869/10000000000 : ℝ)^4759 ≤ (7481465759963/25000000000000 : ℝ)^3735 := by
    have hnat : (3879594869 : ℕ)^4759*25000000000000^3735 ≤ 7481465759963^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3879594869 10000000000 7481465759963 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4566937283/10000000000 : ℝ)^4759 ≤ (7367781132679/20000000000000 : ℝ)^3735 := by
    have hnat : (4566937283 : ℕ)^4759*20000000000000^3735 ≤ 7367781132679^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566937283 10000000000 7367781132679 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053117721/2500000000 : ℝ), (3879594869/10000000000 : ℝ), (4566937283/10000000000 : ℝ)] ![(33235231286903/100000000000000 : ℝ), (7481465759963/25000000000000 : ℝ), (7367781132679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053117721/2500000000 : ℝ)|^4759 ≤ (33235231286903/100000000000000 : ℝ)^3735
        have hw : |(1053117721/2500000000 : ℝ)|=(1053117721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3879594869/10000000000 : ℝ)|^4759 ≤ (7481465759963/25000000000000 : ℝ)^3735
        have hw : |(3879594869/10000000000 : ℝ)|=(3879594869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4566937283/10000000000 : ℝ)|^4759 ≤ (7367781132679/20000000000000 : ℝ)^3735
        have hw : |(4566937283/10000000000 : ℝ)|=(4566937283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53257401/312500000 : ℝ)*x 0 + (518239663/1000000000 : ℝ)*x 1 + (2728956063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53257401/312500000 : ℝ)^4759 ≤ (2622911605561/25000000000000 : ℝ)^3735 := by
    have hnat : (53257401 : ℕ)^4759*25000000000000^3735 ≤ 2622911605561^3735*312500000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53257401 312500000 2622911605561 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518239663/1000000000 : ℝ)^4759 ≤ (216389123301/500000000000 : ℝ)^3735 := by
    have hnat : (518239663 : ℕ)^4759*500000000000^3735 ≤ 216389123301^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518239663 1000000000 216389123301 500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728956063/5000000000 : ℝ)^4759 ≤ (46230528902013/100000000000000 : ℝ)^3735 := by
    have hnat : (2728956063 : ℕ)^4759*100000000000000^3735 ≤ 46230528902013^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728956063 5000000000 46230528902013 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53257401/312500000 : ℝ), (518239663/1000000000 : ℝ), (2728956063/5000000000 : ℝ)] ![(2622911605561/25000000000000 : ℝ), (216389123301/500000000000 : ℝ), (46230528902013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53257401/312500000 : ℝ)|^4759 ≤ (2622911605561/25000000000000 : ℝ)^3735
        have hw : |(-53257401/312500000 : ℝ)|=(53257401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518239663/1000000000 : ℝ)|^4759 ≤ (216389123301/500000000000 : ℝ)^3735
        have hw : |(518239663/1000000000 : ℝ)|=(518239663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728956063/5000000000 : ℝ)|^4759 ≤ (46230528902013/100000000000000 : ℝ)^3735
        have hw : |(2728956063/5000000000 : ℝ)|=(2728956063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055886339/2000000000 : ℝ)*x 0 + (-1570812559/10000000000 : ℝ)*x 1 + (682238969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055886339/2000000000 : ℝ)^4759 ≤ (22156479670521/50000000000000 : ℝ)^3735 := by
    have hnat : (1055886339 : ℕ)^4759*50000000000000^3735 ≤ 22156479670521^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055886339 2000000000 22156479670521 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1570812559/10000000000 : ℝ)^4759 ≤ (945651578767/10000000000000 : ℝ)^3735 := by
    have hnat : (1570812559 : ℕ)^4759*10000000000000^3735 ≤ 945651578767^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570812559 10000000000 945651578767 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682238969/1250000000 : ℝ)^4759 ≤ (1444703902049/3125000000000 : ℝ)^3735 := by
    have hnat : (682238969 : ℕ)^4759*3125000000000^3735 ≤ 1444703902049^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682238969 1250000000 1444703902049 3125000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055886339/2000000000 : ℝ), (-1570812559/10000000000 : ℝ), (682238969/1250000000 : ℝ)] ![(22156479670521/50000000000000 : ℝ), (945651578767/10000000000000 : ℝ), (1444703902049/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055886339/2000000000 : ℝ)|^4759 ≤ (22156479670521/50000000000000 : ℝ)^3735
        have hw : |(1055886339/2000000000 : ℝ)|=(1055886339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1570812559/10000000000 : ℝ)|^4759 ≤ (945651578767/10000000000000 : ℝ)^3735
        have hw : |(-1570812559/10000000000 : ℝ)|=(1570812559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682238969/1250000000 : ℝ)|^4759 ≤ (1444703902049/3125000000000 : ℝ)^3735
        have hw : |(682238969/1250000000 : ℝ)|=(682238969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319857923/2500000000 : ℝ)*x 0 + (2728955983/5000000000 : ℝ)*x 1 + (-78540613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319857923/2500000000 : ℝ)^4759 ≤ (22156479654479/50000000000000 : ℝ)^3735 := by
    have hnat : (1319857923 : ℕ)^4759*50000000000000^3735 ≤ 22156479654479^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319857923 2500000000 22156479654479 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728955983/5000000000 : ℝ)^4759 ≤ (46230527175191/100000000000000 : ℝ)^3735 := by
    have hnat : (2728955983 : ℕ)^4759*100000000000000^3735 ≤ 46230527175191^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728955983 5000000000 46230527175191 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78540613/500000000 : ℝ)^4759 ≤ (9456513494147/100000000000000 : ℝ)^3735 := by
    have hnat : (78540613 : ℕ)^4759*100000000000000^3735 ≤ 9456513494147^3735*500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78540613 500000000 9456513494147 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319857923/2500000000 : ℝ), (2728955983/5000000000 : ℝ), (-78540613/500000000 : ℝ)] ![(22156479654479/50000000000000 : ℝ), (46230527175191/100000000000000 : ℝ), (9456513494147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319857923/2500000000 : ℝ)|^4759 ≤ (22156479654479/50000000000000 : ℝ)^3735
        have hw : |(1319857923/2500000000 : ℝ)|=(1319857923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728955983/5000000000 : ℝ)|^4759 ≤ (46230527175191/100000000000000 : ℝ)^3735
        have hw : |(2728955983/5000000000 : ℝ)|=(2728955983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78540613/500000000 : ℝ)|^4759 ≤ (9456513494147/100000000000000 : ℝ)^3735
        have hw : |(-78540613/500000000 : ℝ)|=(78540613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s3_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26329031/62500000 : ℝ)*x 0 + (35639143/78125000 : ℝ)*x 1 + (1942388251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26329031/62500000 : ℝ)^4759 ≤ (16618490623711/50000000000000 : ℝ)^3735 := by
    have hnat : (26329031 : ℕ)^4759*50000000000000^3735 ≤ 16618490623711^3735*62500000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26329031 62500000 16618490623711 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35639143/78125000 : ℝ)^4759 ≤ (9196554727053/25000000000000 : ℝ)^3735 := by
    have hnat : (35639143 : ℕ)^4759*25000000000000^3735 ≤ 9196554727053^3735*78125000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35639143 78125000 9196554727053 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1942388251/5000000000 : ℝ)^4759 ≤ (29976799825727/100000000000000 : ℝ)^3735 := by
    have hnat : (1942388251 : ℕ)^4759*100000000000000^3735 ≤ 29976799825727^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942388251 5000000000 29976799825727 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26329031/62500000 : ℝ), (35639143/78125000 : ℝ), (1942388251/5000000000 : ℝ)] ![(16618490623711/50000000000000 : ℝ), (9196554727053/25000000000000 : ℝ), (29976799825727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26329031/62500000 : ℝ)|^4759 ≤ (16618490623711/50000000000000 : ℝ)^3735
        have hw : |(26329031/62500000 : ℝ)|=(26329031/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35639143/78125000 : ℝ)|^4759 ≤ (9196554727053/25000000000000 : ℝ)^3735
        have hw : |(35639143/78125000 : ℝ)|=(35639143/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1942388251/5000000000 : ℝ)|^4759 ≤ (29976799825727/100000000000000 : ℝ)^3735
        have hw : |(1942388251/5000000000 : ℝ)|=(1942388251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1303/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8177/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8247/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5149/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8247/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5149/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8247/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5149/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8247/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5149/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8247/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5149/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8247/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5149/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5149/50000 : ℝ) ^ (4755/1024 : ℝ) ≤ (1302069144199301/50000000000000000000 : ℝ) := by
    have hpowers : (5149/50000 : ℝ)^4755 ≤ (1302069144199301/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5149 : ℕ)^4755*50000000000000000000^1024 ≤ 1302069144199301^1024*50000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5149 50000 1302069144199301 50000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5149/50000 : ℝ)) (X := (1302069144199301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8247/50000 : ℝ) ^ (4755/1024 : ℝ) ≤ (11603271052120151/50000000000000000000 : ℝ) := by
    have hpowers : (8247/50000 : ℝ)^4755 ≤ (11603271052120151/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8247 : ℕ)^4755*50000000000000000000^1024 ≤ 11603271052120151^1024*50000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8247 50000 11603271052120151 50000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8247/50000 : ℝ)) (X := (11603271052120151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001302069144199301/25000000000000000000 : ℝ) ≤ (10000112159121799/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (25001302069144199301/25000000000000000000 : ℝ)^1024 ≤ (10000112159121799/10000000000000000 : ℝ)^4755 := by
      have hnat : (25001302069144199301 : ℕ)^1024*10000000000000000^4755 ≤ 10000112159121799^4755*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001302069144199301 25000000000000000000 10000112159121799 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000112159121799/10000000000000000 : ℝ)) (X := (25001302069144199301/25000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503226335049079863/12500000000000000000 : ℝ) ≤ (10000555782561067/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (12503226335049079863/12500000000000000000 : ℝ)^1024 ≤ (10000555782561067/10000000000000000 : ℝ)^4755 := by
      have hnat : (12503226335049079863 : ℕ)^1024*10000000000000000^4755 ≤ 10000555782561067^4755*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503226335049079863 12500000000000000000 10000555782561067 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000555782561067/10000000000000000 : ℝ)) (X := (12503226335049079863/12500000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011603271052120151/25000000000000000000 : ℝ) ≤ (2000199881200067/2000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (25011603271052120151/25000000000000000000 : ℝ)^1024 ≤ (2000199881200067/2000000000000000 : ℝ)^4755 := by
      have hnat : (25011603271052120151 : ℕ)^1024*2000000000000000^4755 ≤ 2000199881200067^4755*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011603271052120151 25000000000000000000 2000199881200067 2000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000199881200067/2000000000000000 : ℝ)) (X := (25011603271052120151/25000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1302069144199301/50000000000000000000 : ℝ) ≤ ((15487889517390875719/15490000000000000000 : ℝ)+2*(110905859817/154900000000000 : ℝ)*(5149/50000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (15487889517390875719/15490000000000000000 : ℝ)+2*(110905859817/154900000000000 : ℝ)*(5149/50000 : ℝ)=(10000112159121799/10000000000000000 : ℝ) by norm_num, show 1+2*(1302069144199301/50000000000000000000 : ℝ)=(25001302069144199301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11603271052120151/50000000000000000000 : ℝ)+(1302069144199301/50000000000000000000 : ℝ) ≤ ((15487889517390875719/15490000000000000000 : ℝ)+(110905859817/154900000000000 : ℝ)*((8247/50000 : ℝ)+(5149/50000 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (15487889517390875719/15490000000000000000 : ℝ)+(110905859817/154900000000000 : ℝ)*((8247/50000 : ℝ)+(5149/50000 : ℝ))=(10000555782561067/10000000000000000 : ℝ) by norm_num, show 1+(11603271052120151/50000000000000000000 : ℝ)+(1302069144199301/50000000000000000000 : ℝ)=(12503226335049079863/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11603271052120151/50000000000000000000 : ℝ) ≤ ((15487889517390875719/15490000000000000000 : ℝ)+2*(110905859817/154900000000000 : ℝ)*(8247/50000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (15487889517390875719/15490000000000000000 : ℝ)+2*(110905859817/154900000000000 : ℝ)*(8247/50000 : ℝ)=(2000199881200067/2000000000000000 : ℝ) by norm_num, show 1+2*(11603271052120151/50000000000000000000 : ℝ)=(25011603271052120151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15487889517390875719/15490000000000000000 : ℝ)*(X 1 0+X 2 0)+(110905859817/154900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (5149/50000 : ℝ)) (hi := (8247/50000 : ℝ)) (c := (15487889517390875719/15490000000000000000 : ℝ)) (alpha := (110905859817/154900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15487889517390875719/15490000000000000000 : ℝ)*(X 0 1+X 2 1)+(110905859817/154900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (5149/50000 : ℝ)) (hi := (8247/50000 : ℝ)) (c := (15487889517390875719/15490000000000000000 : ℝ)) (alpha := (110905859817/154900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15487889517390875719/15490000000000000000 : ℝ)*(X 0 2+X 1 2)+(110905859817/154900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (5149/50000 : ℝ)) (hi := (8247/50000 : ℝ)) (c := (15487889517390875719/15490000000000000000 : ℝ)) (alpha := (110905859817/154900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-852082971/5000000000 : ℝ)*X 0 0+(5460019933/10000000000 : ℝ)*X 0 1+(5180310707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66921457/125000000 : ℝ)*X 1 0+(-1848414351/10000000000 : ℝ)*X 1 1+(323769383/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353716583/10000000000 : ℝ)*X 2 0+(1295077481/2500000000 : ℝ)*X 2 1+(-1848414593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1053117721/2500000000 : ℝ)*X 0 0+(3879594869/10000000000 : ℝ)*X 0 1+(4566937283/10000000000 : ℝ)*X 0 2+(1053117721/2500000000 : ℝ)*X 1 0+(3879594869/10000000000 : ℝ)*X 1 1+(4566937283/10000000000 : ℝ)*X 1 2+(1053117721/2500000000 : ℝ)*X 2 0+(3879594869/10000000000 : ℝ)*X 2 1+(4566937283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53257401/312500000 : ℝ)*X 0 0+(518239663/1000000000 : ℝ)*X 0 1+(2728956063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055886339/2000000000 : ℝ)*X 1 0+(-1570812559/10000000000 : ℝ)*X 1 1+(682238969/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319857923/2500000000 : ℝ)*X 2 0+(2728955983/5000000000 : ℝ)*X 2 1+(-78540613/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26329031/62500000 : ℝ)*X 0 0+(35639143/78125000 : ℝ)*X 0 1+(1942388251/5000000000 : ℝ)*X 0 2+(26329031/62500000 : ℝ)*X 1 0+(35639143/78125000 : ℝ)*X 1 1+(1942388251/5000000000 : ℝ)*X 1 2+(26329031/62500000 : ℝ)*X 2 0+(35639143/78125000 : ℝ)*X 2 1+(1942388251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1589346523285835012272703163/387250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132210497/20000000000000 : ℝ)*(base19) + (635399433/100000000000000 : ℝ)*(base23) + (13950769/12500000000000 : ℝ)*(upper3) + (5614461/100000000000000 : ℝ)*(lower4) + (9140773/6250000000000 : ℝ)*(upper5) + (1257505649621253/50000000000000 : ℝ)*(major0) + (1257505649621253/50000000000000 : ℝ)*(major1) + (1257505649621253/50000000000000 : ℝ)*(major2) + (1787570337245599/50000000000000 : ℝ)*(sp0) + (1787570006719357/50000000000000 : ℝ)*(sp1) + (893784081885739/25000000000000 : ℝ)*(sp2) + (1454880518504333/100000000000000 : ℝ)*(sp3) + (3711548809/100000000000000 : ℝ)*(sp6) + (126868323/10000000000000 : ℝ)*(sp7) + (727440893593781/50000000000000 : ℝ)*(f.failure) + (1787570337245599/50000000000000 : ℝ)*(f.sum) + (1367119055341/3872500000000000000000000000 : ℝ)*base65 + (8278993330095344093/774500000000000000000000000000000 : ℝ)*base68 + (9443954913618344093/774500000000000000000000000000000 : ℝ)*base70 + (5786610492379844093/774500000000000000000000000000000 : ℝ)*base72 + (46016680088433/7745000000000000000000000000 : ℝ)*base74 + (10578472259065344093/774500000000000000000000000000000 : ℝ)*base76 + (2792850707611844093/774500000000000000000000000000000 : ℝ)*base78 + (1172331663643344093/774500000000000000000000000000000 : ℝ)*base80 + (50039191196593/7745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2443009/1000000000000000000000 : ℝ)*base90 + (2443009/1000000000000000000000 : ℝ)*base92 + (2443009/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58592749575817344153474051/7745000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1177969369/100000000000000 : ℝ)*(base19) + (297899209/25000000000000 : ℝ)*(base23) + (4290223/25000000000000 : ℝ)*(upper3) + (3267697/50000000000000 : ℝ)*(lower4) + (46731663/20000000000000 : ℝ)*(upper5) + (51065946854057/2000000000000 : ℝ)*(major0) + (51065946854057/2000000000000 : ℝ)*(major1) + (51065946854057/2000000000000 : ℝ)*(major2) + (3441419541/25000000000000 : ℝ)*(sp1) + (14000984011/100000000000000 : ℝ)*(sp2) + (1814782482647667/50000000000000 : ℝ)*(sp4) + (18147750108239/500000000000 : ℝ)*(sp5) + (1814774886357243/50000000000000 : ℝ)*(sp6) + (369257366983959/25000000000000 : ℝ)*(sp7) + (369257366983959/25000000000000 : ℝ)*(f.failure) + (1814782482647667/50000000000000 : ℝ)*(f.sum) + (2400806860619/774500000000000000000000000 : ℝ)*base66 + (96488645162121983/30980000000000000000000000000000 : ℝ)*base67 + (101465049553961983/30980000000000000000000000000000 : ℝ)*base69 + (25133408257158017/30980000000000000000000000000000 : ℝ)*base72 + (78623041093/154900000000000000000000000 : ℝ)*base74 + (374932619216121983/30980000000000000000000000000000 : ℝ)*base75 + (142771131865541983/30980000000000000000000000000000 : ℝ)*base77 + (235488463146521983/30980000000000000000000000000000 : ℝ)*base79 + (483868407529/1549000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5085851/500000000000000000000 : ℝ)*base90 + (5085851/500000000000000000000 : ℝ)*base92 + (5085851/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1610_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1303/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1610_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1610_s4_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1704281899/10000000000 : ℝ)*x 0 + (1364859163/2500000000 : ℝ)*x 1 + (5180816951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1704281899/10000000000 : ℝ)^4759 ≤ (10491999930061/100000000000000 : ℝ)^3735 := by
    have hnat : (1704281899 : ℕ)^4759*100000000000000^3735 ≤ 10491999930061^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704281899 10000000000 10491999930061 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364859163/2500000000 : ℝ)^4759 ≤ (23123491591033/50000000000000 : ℝ)^3735 := by
    have hnat : (1364859163 : ℕ)^4759*50000000000000^3735 ≤ 23123491591033^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364859163 2500000000 23123491591033 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180816951/10000000000 : ℝ)^4759 ≤ (43261016871891/100000000000000 : ℝ)^3735 := by
    have hnat : (5180816951 : ℕ)^4759*100000000000000^3735 ≤ 43261016871891^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180816951 10000000000 43261016871891 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1704281899/10000000000 : ℝ), (1364859163/2500000000 : ℝ), (5180816951/10000000000 : ℝ)] ![(10491999930061/100000000000000 : ℝ), (23123491591033/50000000000000 : ℝ), (43261016871891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1704281899/10000000000 : ℝ)|^4759 ≤ (10491999930061/100000000000000 : ℝ)^3735
        have hw : |(-1704281899/10000000000 : ℝ)|=(1704281899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364859163/2500000000 : ℝ)|^4759 ≤ (23123491591033/50000000000000 : ℝ)^3735
        have hw : |(1364859163/2500000000 : ℝ)|=(1364859163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180816951/10000000000 : ℝ)|^4759 ≤ (43261016871891/100000000000000 : ℝ)^3735
        have hw : |(5180816951/10000000000 : ℝ)|=(5180816951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16729877/31250000 : ℝ)*x 0 + (-461987857/2500000000 : ℝ)*x 1 + (5180816427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16729877/31250000 : ℝ)^4759 ≤ (45107267082811/100000000000000 : ℝ)^3735 := by
    have hnat : (16729877 : ℕ)^4759*100000000000000^3735 ≤ 45107267082811^3735*31250000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16729877 31250000 45107267082811 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461987857/2500000000 : ℝ)^4759 ≤ (2326344320569/20000000000000 : ℝ)^3735 := by
    have hnat : (461987857 : ℕ)^4759*20000000000000^3735 ≤ 2326344320569^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461987857 2500000000 2326344320569 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180816427/10000000000 : ℝ)^4759 ≤ (43261011296763/100000000000000 : ℝ)^3735 := by
    have hnat : (5180816427 : ℕ)^4759*100000000000000^3735 ≤ 43261011296763^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180816427 10000000000 43261011296763 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16729877/31250000 : ℝ), (-461987857/2500000000 : ℝ), (5180816427/10000000000 : ℝ)] ![(45107267082811/100000000000000 : ℝ), (2326344320569/20000000000000 : ℝ), (43261011296763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16729877/31250000 : ℝ)|^4759 ≤ (45107267082811/100000000000000 : ℝ)^3735
        have hw : |(16729877/31250000 : ℝ)|=(16729877/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-461987857/2500000000 : ℝ)|^4759 ≤ (2326344320569/20000000000000 : ℝ)^3735
        have hw : |(-461987857/2500000000 : ℝ)|=(461987857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180816427/10000000000 : ℝ)|^4759 ≤ (43261011296763/100000000000000 : ℝ)^3735
        have hw : |(5180816427/10000000000 : ℝ)|=(5180816427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353560663/10000000000 : ℝ)*x 0 + (5180816617/10000000000 : ℝ)*x 1 + (-923975573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353560663/10000000000 : ℝ)^4759 ≤ (11276816832433/25000000000000 : ℝ)^3735 := by
    have hnat : (5353560663 : ℕ)^4759*25000000000000^3735 ≤ 11276816832433^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353560663 10000000000 11276816832433 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180816617/10000000000 : ℝ)^4759 ≤ (43261013318279/100000000000000 : ℝ)^3735 := by
    have hnat : (5180816617 : ℕ)^4759*100000000000000^3735 ≤ 43261013318279^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180816617 10000000000 43261013318279 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923975573/5000000000 : ℝ)^4759 ≤ (90872807353/781250000000 : ℝ)^3735 := by
    have hnat : (923975573 : ℕ)^4759*781250000000^3735 ≤ 90872807353^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923975573 5000000000 90872807353 781250000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353560663/10000000000 : ℝ), (5180816617/10000000000 : ℝ), (-923975573/5000000000 : ℝ)] ![(11276816832433/25000000000000 : ℝ), (43261013318279/100000000000000 : ℝ), (90872807353/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353560663/10000000000 : ℝ)|^4759 ≤ (11276816832433/25000000000000 : ℝ)^3735
        have hw : |(5353560663/10000000000 : ℝ)|=(5353560663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180816617/10000000000 : ℝ)|^4759 ≤ (43261013318279/100000000000000 : ℝ)^3735
        have hw : |(5180816617/10000000000 : ℝ)|=(5180816617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-923975573/5000000000 : ℝ)|^4759 ≤ (90872807353/781250000000 : ℝ)^3735
        have hw : |(-923975573/5000000000 : ℝ)|=(923975573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105313667/250000000 : ℝ)*x 0 + (3880926597/10000000000 : ℝ)*x 1 + (2282794773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105313667/250000000 : ℝ)^4759 ≤ (33235993250547/100000000000000 : ℝ)^3735 := by
    have hnat : (105313667 : ℕ)^4759*100000000000000^3735 ≤ 33235993250547^3735*250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105313667 250000000 33235993250547 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3880926597/10000000000 : ℝ)^4759 ≤ (467796132641/1562500000000 : ℝ)^3735 := by
    have hnat : (3880926597 : ℕ)^4759*1562500000000^3735 ≤ 467796132641^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880926597 10000000000 467796132641 1562500000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282794773/5000000000 : ℝ)^4759 ≤ (4603131780207/12500000000000 : ℝ)^3735 := by
    have hnat : (2282794773 : ℕ)^4759*12500000000000^3735 ≤ 4603131780207^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282794773 5000000000 4603131780207 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105313667/250000000 : ℝ), (3880926597/10000000000 : ℝ), (2282794773/5000000000 : ℝ)] ![(33235993250547/100000000000000 : ℝ), (467796132641/1562500000000 : ℝ), (4603131780207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105313667/250000000 : ℝ)|^4759 ≤ (33235993250547/100000000000000 : ℝ)^3735
        have hw : |(105313667/250000000 : ℝ)|=(105313667/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3880926597/10000000000 : ℝ)|^4759 ≤ (467796132641/1562500000000 : ℝ)^3735
        have hw : |(3880926597/10000000000 : ℝ)|=(3880926597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2282794773/5000000000 : ℝ)|^4759 ≤ (4603131780207/12500000000000 : ℝ)^3735
        have hw : |(2282794773/5000000000 : ℝ)|=(2282794773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-852176223/5000000000 : ℝ)*x 0 + (5182887213/10000000000 : ℝ)*x 1 + (2728672209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852176223/5000000000 : ℝ)^4759 ≤ (5246276654713/50000000000000 : ℝ)^3735 := by
    have hnat : (852176223 : ℕ)^4759*50000000000000^3735 ≤ 5246276654713^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852176223 5000000000 5246276654713 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182887213/10000000000 : ℝ)^4759 ≤ (8656608950071/20000000000000 : ℝ)^3735 := by
    have hnat : (5182887213 : ℕ)^4759*20000000000000^3735 ≤ 8656608950071^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182887213 10000000000 8656608950071 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728672209/5000000000 : ℝ)^4759 ≤ (4622440192511/10000000000000 : ℝ)^3735 := by
    have hnat : (2728672209 : ℕ)^4759*10000000000000^3735 ≤ 4622440192511^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728672209 5000000000 4622440192511 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-852176223/5000000000 : ℝ), (5182887213/10000000000 : ℝ), (2728672209/5000000000 : ℝ)] ![(5246276654713/50000000000000 : ℝ), (8656608950071/20000000000000 : ℝ), (4622440192511/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-852176223/5000000000 : ℝ)|^4759 ≤ (5246276654713/50000000000000 : ℝ)^3735
        have hw : |(-852176223/5000000000 : ℝ)|=(852176223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182887213/10000000000 : ℝ)|^4759 ≤ (8656608950071/20000000000000 : ℝ)^3735
        have hw : |(5182887213/10000000000 : ℝ)|=(5182887213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728672209/5000000000 : ℝ)|^4759 ≤ (4622440192511/10000000000000 : ℝ)^3735
        have hw : |(2728672209/5000000000 : ℝ)|=(2728672209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279566003/10000000000 : ℝ)*x 0 + (-1571423497/10000000000 : ℝ)*x 1 + (2728672209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279566003/10000000000 : ℝ)^4759 ≤ (22157197865027/50000000000000 : ℝ)^3735 := by
    have hnat : (5279566003 : ℕ)^4759*50000000000000^3735 ≤ 22157197865027^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279566003 10000000000 22157197865027 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1571423497/10000000000 : ℝ)^4759 ≤ (591325145377/6250000000000 : ℝ)^3735 := by
    have hnat : (1571423497 : ℕ)^4759*6250000000000^3735 ≤ 591325145377^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571423497 10000000000 591325145377 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728672209/5000000000 : ℝ)^4759 ≤ (4622440192511/10000000000000 : ℝ)^3735 := by
    have hnat : (2728672209 : ℕ)^4759*10000000000000^3735 ≤ 4622440192511^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728672209 5000000000 4622440192511 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279566003/10000000000 : ℝ), (-1571423497/10000000000 : ℝ), (2728672209/5000000000 : ℝ)] ![(22157197865027/50000000000000 : ℝ), (591325145377/6250000000000 : ℝ), (4622440192511/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279566003/10000000000 : ℝ)|^4759 ≤ (22157197865027/50000000000000 : ℝ)^3735
        have hw : |(5279566003/10000000000 : ℝ)|=(5279566003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1571423497/10000000000 : ℝ)|^4759 ≤ (591325145377/6250000000000 : ℝ)^3735
        have hw : |(-1571423497/10000000000 : ℝ)|=(1571423497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728672209/5000000000 : ℝ)|^4759 ≤ (4622440192511/10000000000000 : ℝ)^3735
        have hw : |(2728672209/5000000000 : ℝ)|=(2728672209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279566003/10000000000 : ℝ)*x 0 + (2728672209/5000000000 : ℝ)*x 1 + (-1571423497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279566003/10000000000 : ℝ)^4759 ≤ (22157197865027/50000000000000 : ℝ)^3735 := by
    have hnat : (5279566003 : ℕ)^4759*50000000000000^3735 ≤ 22157197865027^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279566003 10000000000 22157197865027 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728672209/5000000000 : ℝ)^4759 ≤ (4622440192511/10000000000000 : ℝ)^3735 := by
    have hnat : (2728672209 : ℕ)^4759*10000000000000^3735 ≤ 4622440192511^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728672209 5000000000 4622440192511 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1571423497/10000000000 : ℝ)^4759 ≤ (591325145377/6250000000000 : ℝ)^3735 := by
    have hnat : (1571423497 : ℕ)^4759*6250000000000^3735 ≤ 591325145377^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571423497 10000000000 591325145377 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279566003/10000000000 : ℝ), (2728672209/5000000000 : ℝ), (-1571423497/10000000000 : ℝ)] ![(22157197865027/50000000000000 : ℝ), (4622440192511/10000000000000 : ℝ), (591325145377/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279566003/10000000000 : ℝ)|^4759 ≤ (22157197865027/50000000000000 : ℝ)^3735
        have hw : |(5279566003/10000000000 : ℝ)|=(5279566003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728672209/5000000000 : ℝ)|^4759 ≤ (4622440192511/10000000000000 : ℝ)^3735
        have hw : |(2728672209/5000000000 : ℝ)|=(2728672209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1571423497/10000000000 : ℝ)|^4759 ≤ (591325145377/6250000000000 : ℝ)^3735
        have hw : |(-1571423497/10000000000 : ℝ)|=(1571423497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s4_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4212719151/10000000000 : ℝ)*x 0 + (285031397/625000000 : ℝ)*x 1 + (3886067381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212719151/10000000000 : ℝ)^4759 ≤ (33237727084699/100000000000000 : ℝ)^3735 := by
    have hnat : (4212719151 : ℕ)^4759*100000000000000^3735 ≤ 33237727084699^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212719151 10000000000 33237727084699 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285031397/625000000 : ℝ)^4759 ≤ (36772780502049/100000000000000 : ℝ)^3735 := by
    have hnat : (285031397 : ℕ)^4759*100000000000000^3735 ≤ 36772780502049^3735*625000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285031397 625000000 36772780502049 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3886067381/10000000000 : ℝ)^4759 ≤ (2998949239799/10000000000000 : ℝ)^3735 := by
    have hnat : (3886067381 : ℕ)^4759*10000000000000^3735 ≤ 2998949239799^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886067381 10000000000 2998949239799 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212719151/10000000000 : ℝ), (285031397/625000000 : ℝ), (3886067381/10000000000 : ℝ)] ![(33237727084699/100000000000000 : ℝ), (36772780502049/100000000000000 : ℝ), (2998949239799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212719151/10000000000 : ℝ)|^4759 ≤ (33237727084699/100000000000000 : ℝ)^3735
        have hw : |(4212719151/10000000000 : ℝ)|=(4212719151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285031397/625000000 : ℝ)|^4759 ≤ (36772780502049/100000000000000 : ℝ)^3735
        have hw : |(285031397/625000000 : ℝ)|=(285031397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3886067381/10000000000 : ℝ)|^4759 ≤ (2998949239799/10000000000000 : ℝ)^3735
        have hw : |(3886067381/10000000000 : ℝ)|=(3886067381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1303/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2087/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8171/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8177/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1303/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8177/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1303/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8177/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1303/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8177/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1303/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8177/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1303/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8177/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1303/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1303/12500 : ℝ) ^ (4755/1024 : ℝ) ≤ (344428484475509/12500000000000000000 : ℝ) := by
    have hpowers : (1303/12500 : ℝ)^4755 ≤ (344428484475509/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1303 : ℕ)^4755*12500000000000000000^1024 ≤ 344428484475509^1024*12500^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1303 12500 344428484475509 12500000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1303/12500 : ℝ)) (X := (344428484475509/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8177/50000 : ℝ) ^ (4755/1024 : ℝ) ≤ (1394119576963327/6250000000000000000 : ℝ) := by
    have hpowers : (8177/50000 : ℝ)^4755 ≤ (1394119576963327/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8177 : ℕ)^4755*6250000000000000000^1024 ≤ 1394119576963327^1024*50000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8177 50000 1394119576963327 6250000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8177/50000 : ℝ)) (X := (1394119576963327/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250344428484475509/6250000000000000000 : ℝ) ≤ (5000059337479361/5000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (6250344428484475509/6250000000000000000 : ℝ)^1024 ≤ (5000059337479361/5000000000000000 : ℝ)^4755 := by
      have hnat : (6250344428484475509 : ℕ)^1024*5000000000000000^4755 ≤ 5000059337479361^4755*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250344428484475509 6250000000000000000 5000059337479361 5000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000059337479361/5000000000000000 : ℝ)) (X := (6250344428484475509/6250000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503132667638402163/12500000000000000000 : ℝ) ≤ (80004317188721/80000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (12503132667638402163/12500000000000000000 : ℝ)^1024 ≤ (80004317188721/80000000000000 : ℝ)^4755 := by
      have hnat : (12503132667638402163 : ℕ)^1024*80000000000000^4755 ≤ 80004317188721^4755*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503132667638402163 12500000000000000000 80004317188721 80000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80004317188721/80000000000000 : ℝ)) (X := (12503132667638402163/12500000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126394119576963327/3125000000000000000 : ℝ) ≤ (1250120077777691/1250000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (3126394119576963327/3125000000000000000 : ℝ)^1024 ≤ (1250120077777691/1250000000000000 : ℝ)^4755 := by
      have hnat : (3126394119576963327 : ℕ)^1024*1250000000000000^4755 ≤ 1250120077777691^4755*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126394119576963327 3125000000000000000 1250120077777691 1250000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250120077777691/1250000000000000 : ℝ)) (X := (3126394119576963327/3125000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(344428484475509/12500000000000000000 : ℝ) ≤ ((14822981821059432929/14825000000000000000 : ℝ)+2*(420973631403/593000000000000 : ℝ)*(1303/12500 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (14822981821059432929/14825000000000000000 : ℝ)+2*(420973631403/593000000000000 : ℝ)*(1303/12500 : ℝ)=(5000059337479361/5000000000000000 : ℝ) by norm_num, show 1+2*(344428484475509/12500000000000000000 : ℝ)=(6250344428484475509/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1394119576963327/6250000000000000000 : ℝ)+(344428484475509/12500000000000000000 : ℝ) ≤ ((14822981821059432929/14825000000000000000 : ℝ)+(420973631403/593000000000000 : ℝ)*((8177/50000 : ℝ)+(1303/12500 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (14822981821059432929/14825000000000000000 : ℝ)+(420973631403/593000000000000 : ℝ)*((8177/50000 : ℝ)+(1303/12500 : ℝ))=(80004317188721/80000000000000 : ℝ) by norm_num, show 1+(1394119576963327/6250000000000000000 : ℝ)+(344428484475509/12500000000000000000 : ℝ)=(12503132667638402163/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1394119576963327/6250000000000000000 : ℝ) ≤ ((14822981821059432929/14825000000000000000 : ℝ)+2*(420973631403/593000000000000 : ℝ)*(8177/50000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (14822981821059432929/14825000000000000000 : ℝ)+2*(420973631403/593000000000000 : ℝ)*(8177/50000 : ℝ)=(1250120077777691/1250000000000000 : ℝ) by norm_num, show 1+2*(1394119576963327/6250000000000000000 : ℝ)=(3126394119576963327/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14822981821059432929/14825000000000000000 : ℝ)*(X 1 0+X 2 0)+(420973631403/593000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (1303/12500 : ℝ)) (hi := (8177/50000 : ℝ)) (c := (14822981821059432929/14825000000000000000 : ℝ)) (alpha := (420973631403/593000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14822981821059432929/14825000000000000000 : ℝ)*(X 0 1+X 2 1)+(420973631403/593000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (1303/12500 : ℝ)) (hi := (8177/50000 : ℝ)) (c := (14822981821059432929/14825000000000000000 : ℝ)) (alpha := (420973631403/593000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14822981821059432929/14825000000000000000 : ℝ)*(X 0 2+X 1 2)+(420973631403/593000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (1303/12500 : ℝ)) (hi := (8177/50000 : ℝ)) (c := (14822981821059432929/14825000000000000000 : ℝ)) (alpha := (420973631403/593000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1704281899/10000000000 : ℝ)*X 0 0+(1364859163/2500000000 : ℝ)*X 0 1+(5180816951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16729877/31250000 : ℝ)*X 1 0+(-461987857/2500000000 : ℝ)*X 1 1+(5180816427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353560663/10000000000 : ℝ)*X 2 0+(5180816617/10000000000 : ℝ)*X 2 1+(-923975573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((105313667/250000000 : ℝ)*X 0 0+(3880926597/10000000000 : ℝ)*X 0 1+(2282794773/5000000000 : ℝ)*X 0 2+(105313667/250000000 : ℝ)*X 1 0+(3880926597/10000000000 : ℝ)*X 1 1+(2282794773/5000000000 : ℝ)*X 1 2+(105313667/250000000 : ℝ)*X 2 0+(3880926597/10000000000 : ℝ)*X 2 1+(2282794773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-852176223/5000000000 : ℝ)*X 0 0+(5182887213/10000000000 : ℝ)*X 0 1+(2728672209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279566003/10000000000 : ℝ)*X 1 0+(-1571423497/10000000000 : ℝ)*X 1 1+(2728672209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279566003/10000000000 : ℝ)*X 2 0+(2728672209/5000000000 : ℝ)*X 2 1+(-1571423497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4212719151/10000000000 : ℝ)*X 0 0+(285031397/625000000 : ℝ)*X 0 1+(3886067381/10000000000 : ℝ)*X 0 2+(4212719151/10000000000 : ℝ)*X 1 0+(285031397/625000000 : ℝ)*X 1 1+(3886067381/10000000000 : ℝ)*X 1 2+(4212719151/10000000000 : ℝ)*X 2 0+(285031397/625000000 : ℝ)*X 2 1+(3886067381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1212355752861104816600310243/370625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18467387/3125000000000 : ℝ)*(base19) + (329367509/100000000000000 : ℝ)*(base23) + (148298177/100000000000000 : ℝ)*(lower2) + (18965273/100000000000000 : ℝ)*(upper3) + (7867719/25000000000000 : ℝ)*(upper5) + (1262424325594563/50000000000000 : ℝ)*(major0) + (1262424325594563/50000000000000 : ℝ)*(major1) + (1262424325594563/50000000000000 : ℝ)*(major2) + (448640236312917/12500000000000 : ℝ)*(sp0) + (897281027866841/25000000000000 : ℝ)*(sp1) + (44864054663203/1250000000000 : ℝ)*(sp2) + (1460572290392293/100000000000000 : ℝ)*(sp3) + (702980103/25000000000000 : ℝ)*(sp4) + (4010503/2000000000000 : ℝ)*(sp7) + (1460572490917443/100000000000000 : ℝ)*(f.failure) + (897281175605937/25000000000000 : ℝ)*(f.sum) + (11326654114839/14825000000000000000000000000 : ℝ)*base65 + (1461577147853459973/741250000000000000000000000000000 : ℝ)*base68 + (7288081844457209973/741250000000000000000000000000000 : ℝ)*base70 + (4025120077219709973/741250000000000000000000000000000 : ℝ)*base72 + (3065987929029/926562500000000000000000000 : ℝ)*base73 + (3675436654292209973/741250000000000000000000000000000 : ℝ)*base76 + (4763208023319709973/741250000000000000000000000000000 : ℝ)*base78 + (12322651785898459973/741250000000000000000000000000000 : ℝ)*base80 + (13446039692711/14825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3908073/2000000000000000000000 : ℝ)*base89 + (3908073/2000000000000000000000 : ℝ)*base91 + (3908073/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138233814139667154864273/14825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1430544231/100000000000000 : ℝ)*(base19) + (774342049/50000000000000 : ℝ)*(base23) + (226929999/50000000000000 : ℝ)*(lower1) + (39197393/20000000000000 : ℝ)*(upper3) + (26574287/50000000000000 : ℝ)*(lower4) + (48323589/25000000000000 : ℝ)*(upper5) + (1281563494000197/50000000000000 : ℝ)*(major0) + (1281563494000197/50000000000000 : ℝ)*(major1) + (1281563494000197/50000000000000 : ℝ)*(major2) + (77912297/6250000000000 : ℝ)*(sp2) + (1821768975829519/50000000000000 : ℝ)*(sp4) + (1821768260557403/50000000000000 : ℝ)*(sp5) + (3643535156378187/100000000000000 : ℝ)*(sp6) + (1482715713529333/100000000000000 : ℝ)*(sp7) + (1482715713529333/100000000000000 : ℝ)*(f.failure) + (1821768975829519/50000000000000 : ℝ)*(f.sum) + (2081193000623/1853125000000000000000000000 : ℝ)*base66 + (9263669602506562013/741250000000000000000000000000000 : ℝ)*base67 + (6279723543832187987/741250000000000000000000000000000 : ℝ)*base70 + (12770134647677812013/741250000000000000000000000000000 : ℝ)*base71 + (718754437341/14825000000000000000000000000 : ℝ)*base73 + (80992314660372187987/741250000000000000000000000000000 : ℝ)*base76 + (134436867780937987/741250000000000000000000000000000 : ℝ)*base78 + (6895259434746562013/741250000000000000000000000000000 : ℝ)*base79 + (56285661143759/14825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10364863/2000000000000000000000 : ℝ)*base89 + (10364863/2000000000000000000000 : ℝ)*base91 + (10364863/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1610_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1303/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1610_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1610_s5_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8521459/50000000 : ℝ)*x 0 + (2729693779/5000000000 : ℝ)*x 1 + (80950929/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8521459/50000000 : ℝ)^4759 ≤ (5246038797173/50000000000000 : ℝ)^3735 := by
    have hnat : (8521459 : ℕ)^4759*50000000000000^3735 ≤ 5246038797173^3735*50000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8521459 50000000 5246038797173 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729693779/5000000000 : ℝ)^4759 ≤ (1445201665269/3125000000000 : ℝ)^3735 := by
    have hnat : (2729693779 : ℕ)^4759*3125000000000^3735 ≤ 1445201665269^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729693779 5000000000 1445201665269 3125000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80950929/156250000 : ℝ)^4759 ≤ (108153672767/250000000000 : ℝ)^3735 := by
    have hnat : (80950929 : ℕ)^4759*250000000000^3735 ≤ 108153672767^3735*156250000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80950929 156250000 108153672767 250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8521459/50000000 : ℝ), (2729693779/5000000000 : ℝ), (80950929/156250000 : ℝ)] ![(5246038797173/50000000000000 : ℝ), (1445201665269/3125000000000 : ℝ), (108153672767/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8521459/50000000 : ℝ)|^4759 ≤ (5246038797173/50000000000000 : ℝ)^3735
        have hw : |(-8521459/50000000 : ℝ)|=(8521459/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729693779/5000000000 : ℝ)|^4759 ≤ (1445201665269/3125000000000 : ℝ)^3735
        have hw : |(2729693779/5000000000 : ℝ)|=(2729693779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80950929/156250000 : ℝ)|^4759 ≤ (108153672767/250000000000 : ℝ)^3735
        have hw : |(80950929/156250000 : ℝ)|=(80950929/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070709477/2000000000 : ℝ)*x 0 + (-1847912021/10000000000 : ℝ)*x 1 + (5180859507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070709477/2000000000 : ℝ)^4759 ≤ (45107124781641/100000000000000 : ℝ)^3735 := by
    have hnat : (1070709477 : ℕ)^4759*100000000000000^3735 ≤ 45107124781641^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070709477 2000000000 45107124781641 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847912021/10000000000 : ℝ)^4759 ≤ (11631405556589/100000000000000 : ℝ)^3735 := by
    have hnat : (1847912021 : ℕ)^4759*100000000000000^3735 ≤ 11631405556589^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847912021 10000000000 11631405556589 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180859507/10000000000 : ℝ)^4759 ≤ (21630734824709/50000000000000 : ℝ)^3735 := by
    have hnat : (5180859507 : ℕ)^4759*50000000000000^3735 ≤ 21630734824709^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180859507 10000000000 21630734824709 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070709477/2000000000 : ℝ), (-1847912021/10000000000 : ℝ), (5180859507/10000000000 : ℝ)] ![(45107124781641/100000000000000 : ℝ), (11631405556589/100000000000000 : ℝ), (21630734824709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070709477/2000000000 : ℝ)|^4759 ≤ (45107124781641/100000000000000 : ℝ)^3735
        have hw : |(1070709477/2000000000 : ℝ)|=(1070709477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1847912021/10000000000 : ℝ)|^4759 ≤ (11631405556589/100000000000000 : ℝ)^3735
        have hw : |(-1847912021/10000000000 : ℝ)|=(1847912021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180859507/10000000000 : ℝ)|^4759 ≤ (21630734824709/50000000000000 : ℝ)^3735
        have hw : |(5180859507/10000000000 : ℝ)|=(5180859507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353547447/10000000000 : ℝ)*x 0 + (5180859557/10000000000 : ℝ)*x 1 + (-28873623/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353547447/10000000000 : ℝ)^4759 ≤ (11276781361813/25000000000000 : ℝ)^3735 := by
    have hnat : (5353547447 : ℕ)^4759*25000000000000^3735 ≤ 11276781361813^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353547447 10000000000 11276781361813 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180859557/10000000000 : ℝ)^4759 ≤ (43261470181397/100000000000000 : ℝ)^3735 := by
    have hnat : (5180859557 : ℕ)^4759*100000000000000^3735 ≤ 43261470181397^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180859557 10000000000 43261470181397 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28873623/156250000 : ℝ)^4759 ≤ (2326280872321/20000000000000 : ℝ)^3735 := by
    have hnat : (28873623 : ℕ)^4759*20000000000000^3735 ≤ 2326280872321^3735*156250000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28873623 156250000 2326280872321 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353547447/10000000000 : ℝ), (5180859557/10000000000 : ℝ), (-28873623/156250000 : ℝ)] ![(11276781361813/25000000000000 : ℝ), (43261470181397/100000000000000 : ℝ), (2326280872321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353547447/10000000000 : ℝ)|^4759 ≤ (11276781361813/25000000000000 : ℝ)^3735
        have hw : |(5353547447/10000000000 : ℝ)|=(5353547447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180859557/10000000000 : ℝ)|^4759 ≤ (43261470181397/100000000000000 : ℝ)^3735
        have hw : |(5180859557/10000000000 : ℝ)|=(5180859557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28873623/156250000 : ℝ)|^4759 ≤ (2326280872321/20000000000000 : ℝ)^3735
        have hw : |(-28873623/156250000 : ℝ)|=(28873623/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4212552881/10000000000 : ℝ)*x 0 + (3881038591/10000000000 : ℝ)*x 1 + (1141369091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212552881/10000000000 : ℝ)^4759 ≤ (16618027794129/50000000000000 : ℝ)^3735 := by
    have hnat : (4212552881 : ℕ)^4759*50000000000000^3735 ≤ 16618027794129^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212552881 10000000000 16618027794129 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3881038591/10000000000 : ℝ)^4759 ≤ (29940053325333/100000000000000 : ℝ)^3735 := by
    have hnat : (3881038591 : ℕ)^4759*100000000000000^3735 ≤ 29940053325333^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881038591 10000000000 29940053325333 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141369091/2500000000 : ℝ)^4759 ≤ (18411945530037/50000000000000 : ℝ)^3735 := by
    have hnat : (1141369091 : ℕ)^4759*50000000000000^3735 ≤ 18411945530037^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141369091 2500000000 18411945530037 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212552881/10000000000 : ℝ), (3881038591/10000000000 : ℝ), (1141369091/2500000000 : ℝ)] ![(16618027794129/50000000000000 : ℝ), (29940053325333/100000000000000 : ℝ), (18411945530037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212552881/10000000000 : ℝ)|^4759 ≤ (16618027794129/50000000000000 : ℝ)^3735
        have hw : |(4212552881/10000000000 : ℝ)|=(4212552881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3881038591/10000000000 : ℝ)|^4759 ≤ (29940053325333/100000000000000 : ℝ)^3735
        have hw : |(3881038591/10000000000 : ℝ)|=(3881038591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141369091/2500000000 : ℝ)|^4759 ≤ (18411945530037/50000000000000 : ℝ)^3735
        have hw : |(1141369091/2500000000 : ℝ)|=(1141369091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1704361899/10000000000 : ℝ)*x 0 + (2591464281/5000000000 : ℝ)*x 1 + (5457296779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1704361899/10000000000 : ℝ)^4759 ≤ (26231568651/250000000000 : ℝ)^3735 := by
    have hnat : (1704361899 : ℕ)^4759*250000000000^3735 ≤ 26231568651^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704361899 10000000000 26231568651 250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591464281/5000000000 : ℝ)^4759 ≤ (21641742367049/50000000000000 : ℝ)^3735 := by
    have hnat : (2591464281 : ℕ)^4759*50000000000000^3735 ≤ 21641742367049^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591464281 5000000000 21641742367049 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457296779/10000000000 : ℝ)^4759 ≤ (4622388779013/10000000000000 : ℝ)^3735 := by
    have hnat : (5457296779 : ℕ)^4759*10000000000000^3735 ≤ 4622388779013^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457296779 10000000000 4622388779013 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1704361899/10000000000 : ℝ), (2591464281/5000000000 : ℝ), (5457296779/10000000000 : ℝ)] ![(26231568651/250000000000 : ℝ), (21641742367049/50000000000000 : ℝ), (4622388779013/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1704361899/10000000000 : ℝ)|^4759 ≤ (26231568651/250000000000 : ℝ)^3735
        have hw : |(-1704361899/10000000000 : ℝ)|=(1704361899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591464281/5000000000 : ℝ)|^4759 ≤ (21641742367049/50000000000000 : ℝ)^3735
        have hw : |(2591464281/5000000000 : ℝ)|=(2591464281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457296779/10000000000 : ℝ)|^4759 ≤ (4622388779013/10000000000000 : ℝ)^3735
        have hw : |(5457296779/10000000000 : ℝ)|=(5457296779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279577289/10000000000 : ℝ)*x 0 + (-1571474761/10000000000 : ℝ)*x 1 + (2728648397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279577289/10000000000 : ℝ)^4759 ≤ (8862903286267/20000000000000 : ℝ)^3735 := by
    have hnat : (5279577289 : ℕ)^4759*20000000000000^3735 ≤ 8862903286267^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279577289 10000000000 8862903286267 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1571474761/10000000000 : ℝ)^4759 ≤ (4730797798831/50000000000000 : ℝ)^3735 := by
    have hnat : (1571474761 : ℕ)^4759*50000000000000^3735 ≤ 4730797798831^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571474761 10000000000 4730797798831 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728648397/5000000000 : ℝ)^4759 ≤ (23111943976007/50000000000000 : ℝ)^3735 := by
    have hnat : (2728648397 : ℕ)^4759*50000000000000^3735 ≤ 23111943976007^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728648397 5000000000 23111943976007 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279577289/10000000000 : ℝ), (-1571474761/10000000000 : ℝ), (2728648397/5000000000 : ℝ)] ![(8862903286267/20000000000000 : ℝ), (4730797798831/50000000000000 : ℝ), (23111943976007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279577289/10000000000 : ℝ)|^4759 ≤ (8862903286267/20000000000000 : ℝ)^3735
        have hw : |(5279577289/10000000000 : ℝ)|=(5279577289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1571474761/10000000000 : ℝ)|^4759 ≤ (4730797798831/50000000000000 : ℝ)^3735
        have hw : |(-1571474761/10000000000 : ℝ)|=(1571474761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728648397/5000000000 : ℝ)|^4759 ≤ (23111943976007/50000000000000 : ℝ)^3735
        have hw : |(2728648397/5000000000 : ℝ)|=(2728648397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279577509/10000000000 : ℝ)*x 0 + (2728648277/5000000000 : ℝ)*x 1 + (-196434349/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279577509/10000000000 : ℝ)^4759 ≤ (44314518784187/100000000000000 : ℝ)^3735 := by
    have hnat : (5279577509 : ℕ)^4759*100000000000000^3735 ≤ 44314518784187^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279577509 10000000000 44314518784187 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728648277/5000000000 : ℝ)^4759 ≤ (46223885361863/100000000000000 : ℝ)^3735 := by
    have hnat : (2728648277 : ℕ)^4759*100000000000000^3735 ≤ 46223885361863^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728648277 5000000000 46223885361863 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196434349/1250000000 : ℝ)^4759 ≤ (9461595835479/100000000000000 : ℝ)^3735 := by
    have hnat : (196434349 : ℕ)^4759*100000000000000^3735 ≤ 9461595835479^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196434349 1250000000 9461595835479 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279577509/10000000000 : ℝ), (2728648277/5000000000 : ℝ), (-196434349/1250000000 : ℝ)] ![(44314518784187/100000000000000 : ℝ), (46223885361863/100000000000000 : ℝ), (9461595835479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279577509/10000000000 : ℝ)|^4759 ≤ (44314518784187/100000000000000 : ℝ)^3735
        have hw : |(5279577509/10000000000 : ℝ)|=(5279577509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728648277/5000000000 : ℝ)|^4759 ≤ (46223885361863/100000000000000 : ℝ)^3735
        have hw : |(2728648277/5000000000 : ℝ)|=(2728648277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196434349/1250000000 : ℝ)|^4759 ≤ (9461595835479/100000000000000 : ℝ)^3735
        have hw : |(-196434349/1250000000 : ℝ)|=(196434349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s5_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (842545073/2000000000 : ℝ)*x 0 + (4560392183/10000000000 : ℝ)*x 1 + (3886176137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842545073/2000000000 : ℝ)^4759 ≤ (33237789553799/100000000000000 : ℝ)^3735 := by
    have hnat : (842545073 : ℕ)^4759*100000000000000^3735 ≤ 33237789553799^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842545073 2000000000 33237789553799 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4560392183/10000000000 : ℝ)^4759 ≤ (4596456078907/12500000000000 : ℝ)^3735 := by
    have hnat : (4560392183 : ℕ)^4759*12500000000000^3735 ≤ 4596456078907^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560392183 10000000000 4596456078907 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3886176137/10000000000 : ℝ)^4759 ≤ (14995280897271/50000000000000 : ℝ)^3735 := by
    have hnat : (3886176137 : ℕ)^4759*50000000000000^3735 ≤ 14995280897271^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886176137 10000000000 14995280897271 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842545073/2000000000 : ℝ), (4560392183/10000000000 : ℝ), (3886176137/10000000000 : ℝ)] ![(33237789553799/100000000000000 : ℝ), (4596456078907/12500000000000 : ℝ), (14995280897271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842545073/2000000000 : ℝ)|^4759 ≤ (33237789553799/100000000000000 : ℝ)^3735
        have hw : |(842545073/2000000000 : ℝ)|=(842545073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4560392183/10000000000 : ℝ)|^4759 ≤ (4596456078907/12500000000000 : ℝ)^3735
        have hw : |(4560392183/10000000000 : ℝ)|=(4560392183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3886176137/10000000000 : ℝ)|^4759 ≤ (14995280897271/50000000000000 : ℝ)^3735
        have hw : |(3886176137/10000000000 : ℝ)|=(3886176137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2609/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16341/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2087/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2087/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2087/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2087/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2087/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2087/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2087/20000 : ℝ) ^ (4755/1024 : ℝ) ≤ (346119481284679/12500000000000000000 : ℝ) := by
    have hpowers : (2087/20000 : ℝ)^4755 ≤ (346119481284679/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2087 : ℕ)^4755*12500000000000000000^1024 ≤ 346119481284679^1024*20000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2087 20000 346119481284679 12500000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2087/20000 : ℝ)) (X := (346119481284679/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8171/50000 : ℝ) ^ (4755/1024 : ℝ) ≤ (22230012271774649/100000000000000000000 : ℝ) := by
    have hpowers : (8171/50000 : ℝ)^4755 ≤ (22230012271774649/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8171 : ℕ)^4755*100000000000000000000^1024 ≤ 22230012271774649^1024*50000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8171 50000 22230012271774649 100000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8171/50000 : ℝ)) (X := (22230012271774649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250346119481284679/6250000000000000000 : ℝ) ≤ (2500029814397361/2500000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (6250346119481284679/6250000000000000000 : ℝ)^1024 ≤ (2500029814397361/2500000000000000 : ℝ)^4755 := by
      have hnat : (6250346119481284679 : ℕ)^1024*2500000000000000^4755 ≤ 2500029814397361^4755*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250346119481284679 6250000000000000000 2500029814397361 2500000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500029814397361/2500000000000000 : ℝ)) (X := (6250346119481284679/6250000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024998968122052081/100000000000000000000 : ℝ) ≤ (312516822051173/312500000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (100024998968122052081/100000000000000000000 : ℝ)^1024 ≤ (312516822051173/312500000000000 : ℝ)^4755 := by
      have hnat : (100024998968122052081 : ℕ)^1024*312500000000000^4755 ≤ 312516822051173^4755*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024998968122052081 100000000000000000000 312516822051173 312500000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312516822051173/312500000000000 : ℝ)) (X := (100024998968122052081/100000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022230012271774649/50000000000000000000 : ℝ) ≤ (2500239338421407/2500000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (50022230012271774649/50000000000000000000 : ℝ)^1024 ≤ (2500239338421407/2500000000000000 : ℝ)^4755 := by
      have hnat : (50022230012271774649 : ℕ)^1024*2500000000000000^4755 ≤ 2500239338421407^4755*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022230012271774649 50000000000000000000 2500239338421407 2500000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500239338421407/2500000000000000 : ℝ)) (X := (50022230012271774649/50000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(346119481284679/12500000000000000000 : ℝ) ≤ ((82488769443878723/82500000000000000 : ℝ)+2*(585262637/825000000000 : ℝ)*(2087/20000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (82488769443878723/82500000000000000 : ℝ)+2*(585262637/825000000000 : ℝ)*(2087/20000 : ℝ)=(2500029814397361/2500000000000000 : ℝ) by norm_num, show 1+2*(346119481284679/12500000000000000000 : ℝ)=(6250346119481284679/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22230012271774649/100000000000000000000 : ℝ)+(346119481284679/12500000000000000000 : ℝ) ≤ ((82488769443878723/82500000000000000 : ℝ)+(585262637/825000000000 : ℝ)*((8171/50000 : ℝ)+(2087/20000 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (82488769443878723/82500000000000000 : ℝ)+(585262637/825000000000 : ℝ)*((8171/50000 : ℝ)+(2087/20000 : ℝ))=(312516822051173/312500000000000 : ℝ) by norm_num, show 1+(22230012271774649/100000000000000000000 : ℝ)+(346119481284679/12500000000000000000 : ℝ)=(100024998968122052081/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22230012271774649/100000000000000000000 : ℝ) ≤ ((82488769443878723/82500000000000000 : ℝ)+2*(585262637/825000000000 : ℝ)*(8171/50000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (82488769443878723/82500000000000000 : ℝ)+2*(585262637/825000000000 : ℝ)*(8171/50000 : ℝ)=(2500239338421407/2500000000000000 : ℝ) by norm_num, show 1+2*(22230012271774649/100000000000000000000 : ℝ)=(50022230012271774649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (82488769443878723/82500000000000000 : ℝ)*(X 1 0+X 2 0)+(585262637/825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (82488769443878723/82500000000000000 : ℝ)) (alpha := (585262637/825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (82488769443878723/82500000000000000 : ℝ)*(X 0 1+X 2 1)+(585262637/825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (82488769443878723/82500000000000000 : ℝ)) (alpha := (585262637/825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (82488769443878723/82500000000000000 : ℝ)*(X 0 2+X 1 2)+(585262637/825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (82488769443878723/82500000000000000 : ℝ)) (alpha := (585262637/825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8521459/50000000 : ℝ)*X 0 0+(2729693779/5000000000 : ℝ)*X 0 1+(80950929/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070709477/2000000000 : ℝ)*X 1 0+(-1847912021/10000000000 : ℝ)*X 1 1+(5180859507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353547447/10000000000 : ℝ)*X 2 0+(5180859557/10000000000 : ℝ)*X 2 1+(-28873623/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4212552881/10000000000 : ℝ)*X 0 0+(3881038591/10000000000 : ℝ)*X 0 1+(1141369091/2500000000 : ℝ)*X 0 2+(4212552881/10000000000 : ℝ)*X 1 0+(3881038591/10000000000 : ℝ)*X 1 1+(1141369091/2500000000 : ℝ)*X 1 2+(4212552881/10000000000 : ℝ)*X 2 0+(3881038591/10000000000 : ℝ)*X 2 1+(1141369091/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1704361899/10000000000 : ℝ)*X 0 0+(2591464281/5000000000 : ℝ)*X 0 1+(5457296779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279577289/10000000000 : ℝ)*X 1 0+(-1571474761/10000000000 : ℝ)*X 1 1+(2728648397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279577509/10000000000 : ℝ)*X 2 0+(2728648277/5000000000 : ℝ)*X 2 1+(-196434349/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842545073/2000000000 : ℝ)*X 0 0+(4560392183/10000000000 : ℝ)*X 0 1+(3886176137/10000000000 : ℝ)*X 0 2+(842545073/2000000000 : ℝ)*X 1 0+(4560392183/10000000000 : ℝ)*X 1 1+(3886176137/10000000000 : ℝ)*X 1 2+(842545073/2000000000 : ℝ)*X 2 0+(4560392183/10000000000 : ℝ)*X 2 1+(3886176137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49446304458253725879333/21484375000000000000000000000 : ℝ) := by norm_num
    linear_combination (321007821/100000000000000 : ℝ)*(base19) + (361774941/100000000000000 : ℝ)*(base23) + (1026749/50000000000000 : ℝ)*(upper4) + (51917191/50000000000000 : ℝ)*(upper5) + (315710504943807/12500000000000 : ℝ)*(major0) + (315710504943807/12500000000000 : ℝ)*(major1) + (315710504943807/12500000000000 : ℝ)*(major2) + (3590305779341861/100000000000000 : ℝ)*(sp0) + (3590311716851113/100000000000000 : ℝ)*(sp1) + (1795155947440009/50000000000000 : ℝ)*(sp2) + (182631853001091/12500000000000 : ℝ)*(sp3) + (3238656549/50000000000000 : ℝ)*(sp4) + (109398013/50000000000000 : ℝ)*(sp5) + (92172053/10000000000000 : ℝ)*(sp7) + (730527872864629/50000000000000 : ℝ)*(f.failure) + (3590312256654959/100000000000000 : ℝ)*(f.sum) + (25016698021/13750000000000000000000000 : ℝ)*base66 + (2461356570689487/343750000000000000000000000000 : ℝ)*base67 + (1680773605439487/343750000000000000000000000000 : ℝ)*base69 + (2158161478970737/343750000000000000000000000000 : ℝ)*base71 + (14799928951/55000000000000000000000000 : ℝ)*base73 + (316731167904263/343750000000000000000000000000 : ℝ)*base76 + (78506686560513/343750000000000000000000000000 : ℝ)*base78 + (2251407300939487/343750000000000000000000000000 : ℝ)*base79 + (15686665767/27500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5779519/1000000000000000000000 : ℝ)*base89 + (5779519/1000000000000000000000 : ℝ)*base91 + (5779519/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (605195491795147831699179/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1348484131/100000000000000 : ℝ)*(base19) + (165291049/10000000000000 : ℝ)*(base23) + (439305011/100000000000000 : ℝ)*(lower1) + (178738383/100000000000000 : ℝ)*(upper3) + (73330053/100000000000000 : ℝ)*(lower4) + (209596547/100000000000000 : ℝ)*(upper5) + (2563959428952603/100000000000000 : ℝ)*(major0) + (2563959428952603/100000000000000 : ℝ)*(major1) + (2563959428952603/100000000000000 : ℝ)*(major2) + (194953921/20000000000000 : ℝ)*(sp2) + (182236063590403/5000000000000 : ℝ)*(sp4) + (455589990415491/12500000000000 : ℝ)*(sp5) + (911179661031991/25000000000000 : ℝ)*(sp6) + (370799315831551/25000000000000 : ℝ)*(sp7) + (370799315831551/25000000000000 : ℝ)*(f.failure) + (182236063590403/5000000000000 : ℝ)*(f.sum) + (922481217/1250000000000000000000000 : ℝ)*base65 + (3447923503658607/250000000000000000000000000000 : ℝ)*base68 + (2051938412658607/250000000000000000000000000000 : ℝ)*base70 + (232839153658607/250000000000000000000000000000 : ℝ)*base72 + (18133567/19531250000000000000000 : ℝ)*base74 + (16740350435658607/250000000000000000000000000000 : ℝ)*base76 + (796398883408607/250000000000000000000000000000 : ℝ)*base78 + (388628666091393/250000000000000000000000000000 : ℝ)*base79 + (1608192627/312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4490461/500000000000000000000 : ℝ)*base89 + (4490461/500000000000000000000 : ℝ)*base91 + (4490461/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1610_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1610_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1610_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1610_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1610_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1610_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

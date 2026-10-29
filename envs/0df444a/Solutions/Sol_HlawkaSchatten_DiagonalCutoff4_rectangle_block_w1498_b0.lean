-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1498_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:51:39.051998+00:00
-- url     : https://prove2.me/submissions/70964001-d783-4011-95fa-4bf619930f45

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
theorem support_rectangle_w1498_s0_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85039181/500000000 : ℝ)*x 0 + (296184469/500000000 : ℝ)*x 1 + (2424641851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85039181/500000000 : ℝ)^4493 ≤ (5041009264299/50000000000000 : ℝ)^3469 := by
    have hnat : (85039181 : ℕ)^4493*50000000000000^3469 ≤ 5041009264299^3469*500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85039181 500000000 5041009264299 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296184469/500000000 : ℝ)^4493 ≤ (50753350392753/100000000000000 : ℝ)^3469 := by
    have hnat : (296184469 : ℕ)^4493*100000000000000^3469 ≤ 50753350392753^3469*500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296184469 500000000 50753350392753 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2424641851/5000000000 : ℝ)^4493 ≤ (39164631072747/100000000000000 : ℝ)^3469 := by
    have hnat : (2424641851 : ℕ)^4493*100000000000000^3469 ≤ 39164631072747^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424641851 5000000000 39164631072747 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85039181/500000000 : ℝ), (296184469/500000000 : ℝ), (2424641851/5000000000 : ℝ)] ![(5041009264299/50000000000000 : ℝ), (50753350392753/100000000000000 : ℝ), (39164631072747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85039181/500000000 : ℝ)|^4493 ≤ (5041009264299/50000000000000 : ℝ)^3469
        have hw : |(-85039181/500000000 : ℝ)|=(85039181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296184469/500000000 : ℝ)|^4493 ≤ (50753350392753/100000000000000 : ℝ)^3469
        have hw : |(296184469/500000000 : ℝ)|=(296184469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2424641851/5000000000 : ℝ)|^4493 ≤ (39164631072747/100000000000000 : ℝ)^3469
        have hw : |(2424641851/5000000000 : ℝ)|=(2424641851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (685129129/1250000000 : ℝ)*x 0 + (-72003253/312500000 : ℝ)*x 1 + (4849283681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685129129/1250000000 : ℝ)^4493 ≤ (45896363778963/100000000000000 : ℝ)^3469 := by
    have hnat : (685129129 : ℕ)^4493*100000000000000^3469 ≤ 45896363778963^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685129129 1250000000 45896363778963 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72003253/312500000 : ℝ)^4493 ≤ (3734751336497/25000000000000 : ℝ)^3469 := by
    have hnat : (72003253 : ℕ)^4493*25000000000000^3469 ≤ 3734751336497^3469*312500000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72003253 312500000 3734751336497 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4849283681/10000000000 : ℝ)^4493 ≤ (19582315426539/50000000000000 : ℝ)^3469 := by
    have hnat : (4849283681 : ℕ)^4493*50000000000000^3469 ≤ 19582315426539^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849283681 10000000000 19582315426539 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685129129/1250000000 : ℝ), (-72003253/312500000 : ℝ), (4849283681/10000000000 : ℝ)] ![(45896363778963/100000000000000 : ℝ), (3734751336497/25000000000000 : ℝ), (19582315426539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685129129/1250000000 : ℝ)|^4493 ≤ (45896363778963/100000000000000 : ℝ)^3469
        have hw : |(685129129/1250000000 : ℝ)|=(685129129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72003253/312500000 : ℝ)|^4493 ≤ (3734751336497/25000000000000 : ℝ)^3469
        have hw : |(-72003253/312500000 : ℝ)|=(72003253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4849283681/10000000000 : ℝ)|^4493 ≤ (19582315426539/50000000000000 : ℝ)^3469
        have hw : |(4849283681/10000000000 : ℝ)|=(4849283681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5481033061/10000000000 : ℝ)*x 0 + (484928369/1000000000 : ℝ)*x 1 + (-144006503/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5481033061/10000000000 : ℝ)^4493 ≤ (45896364093481/100000000000000 : ℝ)^3469 := by
    have hnat : (5481033061 : ℕ)^4493*100000000000000^3469 ≤ 45896364093481^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481033061 10000000000 45896364093481 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484928369/1000000000 : ℝ)^4493 ≤ (19582315473611/50000000000000 : ℝ)^3469 := by
    have hnat : (484928369 : ℕ)^4493*50000000000000^3469 ≤ 19582315473611^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484928369 1000000000 19582315473611 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144006503/625000000 : ℝ)^4493 ≤ (7469502471453/50000000000000 : ℝ)^3469 := by
    have hnat : (144006503 : ℕ)^4493*50000000000000^3469 ≤ 7469502471453^3469*625000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144006503 625000000 7469502471453 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5481033061/10000000000 : ℝ), (484928369/1000000000 : ℝ), (-144006503/625000000 : ℝ)] ![(45896364093481/100000000000000 : ℝ), (19582315473611/50000000000000 : ℝ), (7469502471453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5481033061/10000000000 : ℝ)|^4493 ≤ (45896364093481/100000000000000 : ℝ)^3469
        have hw : |(5481033061/10000000000 : ℝ)|=(5481033061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(484928369/1000000000 : ℝ)|^4493 ≤ (19582315473611/50000000000000 : ℝ)^3469
        have hw : |(484928369/1000000000 : ℝ)|=(484928369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-144006503/625000000 : ℝ)|^4493 ≤ (7469502471453/50000000000000 : ℝ)^3469
        have hw : |(-144006503/625000000 : ℝ)|=(144006503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2074470151/5000000000 : ℝ)*x 0 + (3091244157/10000000000 : ℝ)*x 1 + (2751767731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074470151/5000000000 : ℝ)^4493 ≤ (32000562907261/100000000000000 : ℝ)^3469 := by
    have hnat : (2074470151 : ℕ)^4493*100000000000000^3469 ≤ 32000562907261^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074470151 5000000000 32000562907261 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091244157/10000000000 : ℝ)^4493 ≤ (21858876363873/100000000000000 : ℝ)^3469 := by
    have hnat : (3091244157 : ℕ)^4493*100000000000000^3469 ≤ 21858876363873^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091244157 10000000000 21858876363873 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751767731/5000000000 : ℝ)^4493 ≤ (46140560722133/100000000000000 : ℝ)^3469 := by
    have hnat : (2751767731 : ℕ)^4493*100000000000000^3469 ≤ 46140560722133^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751767731 5000000000 46140560722133 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074470151/5000000000 : ℝ), (3091244157/10000000000 : ℝ), (2751767731/5000000000 : ℝ)] ![(32000562907261/100000000000000 : ℝ), (21858876363873/100000000000000 : ℝ), (46140560722133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074470151/5000000000 : ℝ)|^4493 ≤ (32000562907261/100000000000000 : ℝ)^3469
        have hw : |(2074470151/5000000000 : ℝ)|=(2074470151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091244157/10000000000 : ℝ)|^4493 ≤ (21858876363873/100000000000000 : ℝ)^3469
        have hw : |(3091244157/10000000000 : ℝ)|=(3091244157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751767731/5000000000 : ℝ)|^4493 ≤ (46140560722133/100000000000000 : ℝ)^3469
        have hw : |(2751767731/5000000000 : ℝ)|=(2751767731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340885083/2000000000 : ℝ)*x 0 + (4876760173/10000000000 : ℝ)*x 1 + (2947613389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340885083/2000000000 : ℝ)^4493 ≤ (10109987931907/100000000000000 : ℝ)^3469 := by
    have hnat : (340885083 : ℕ)^4493*100000000000000^3469 ≤ 10109987931907^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340885083 2000000000 10109987931907 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4876760173/10000000000 : ℝ)^4493 ≤ (39452286169997/100000000000000 : ℝ)^3469 := by
    have hnat : (4876760173 : ℕ)^4493*100000000000000^3469 ≤ 39452286169997^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876760173 10000000000 39452286169997 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2947613389/5000000000 : ℝ)^4493 ≤ (50437725888559/100000000000000 : ℝ)^3469 := by
    have hnat : (2947613389 : ℕ)^4493*100000000000000^3469 ≤ 50437725888559^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947613389 5000000000 50437725888559 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340885083/2000000000 : ℝ), (4876760173/10000000000 : ℝ), (2947613389/5000000000 : ℝ)] ![(10109987931907/100000000000000 : ℝ), (39452286169997/100000000000000 : ℝ), (50437725888559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340885083/2000000000 : ℝ)|^4493 ≤ (10109987931907/100000000000000 : ℝ)^3469
        have hw : |(-340885083/2000000000 : ℝ)|=(340885083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4876760173/10000000000 : ℝ)|^4493 ≤ (39452286169997/100000000000000 : ℝ)^3469
        have hw : |(4876760173/10000000000 : ℝ)|=(4876760173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2947613389/5000000000 : ℝ)|^4493 ≤ (50437725888559/100000000000000 : ℝ)^3469
        have hw : |(2947613389/5000000000 : ℝ)|=(2947613389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187563529/10000000000 : ℝ)*x 0 + (-1258161373/10000000000 : ℝ)*x 1 + (18422583/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187563529/10000000000 : ℝ)^4493 ≤ (2671189257079/6250000000000 : ℝ)^3469 := by
    have hnat : (5187563529 : ℕ)^4493*6250000000000^3469 ≤ 2671189257079^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187563529 10000000000 2671189257079 6250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1258161373/10000000000 : ℝ)^4493 ≤ (1705812099771/25000000000000 : ℝ)^3469 := by
    have hnat : (1258161373 : ℕ)^4493*25000000000000^3469 ≤ 1705812099771^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258161373 10000000000 1705812099771 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18422583/31250000 : ℝ)^4493 ≤ (6304715434107/12500000000000 : ℝ)^3469 := by
    have hnat : (18422583 : ℕ)^4493*12500000000000^3469 ≤ 6304715434107^3469*31250000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18422583 31250000 6304715434107 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187563529/10000000000 : ℝ), (-1258161373/10000000000 : ℝ), (18422583/31250000 : ℝ)] ![(2671189257079/6250000000000 : ℝ), (1705812099771/25000000000000 : ℝ), (6304715434107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187563529/10000000000 : ℝ)|^4493 ≤ (2671189257079/6250000000000 : ℝ)^3469
        have hw : |(5187563529/10000000000 : ℝ)|=(5187563529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1258161373/10000000000 : ℝ)|^4493 ≤ (1705812099771/25000000000000 : ℝ)^3469
        have hw : |(-1258161373/10000000000 : ℝ)|=(1258161373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18422583/31250000 : ℝ)|^4493 ≤ (6304715434107/12500000000000 : ℝ)^3469
        have hw : |(18422583/31250000 : ℝ)|=(18422583/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187563599/10000000000 : ℝ)*x 0 + (1473806649/2500000000 : ℝ)*x 1 + (-1258161211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187563599/10000000000 : ℝ)^4493 ≤ (21369514430107/50000000000000 : ℝ)^3469 := by
    have hnat : (5187563599 : ℕ)^4493*50000000000000^3469 ≤ 21369514430107^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187563599 10000000000 21369514430107 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1473806649/2500000000 : ℝ)^4493 ≤ (50437723871779/100000000000000 : ℝ)^3469 := by
    have hnat : (1473806649 : ℕ)^4493*100000000000000^3469 ≤ 50437723871779^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473806649 2500000000 50437723871779 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1258161211/10000000000 : ℝ)^4493 ≤ (682324726119/10000000000000 : ℝ)^3469 := by
    have hnat : (1258161211 : ℕ)^4493*10000000000000^3469 ≤ 682324726119^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258161211 10000000000 682324726119 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187563599/10000000000 : ℝ), (1473806649/2500000000 : ℝ), (-1258161211/10000000000 : ℝ)] ![(21369514430107/50000000000000 : ℝ), (50437723871779/100000000000000 : ℝ), (682324726119/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187563599/10000000000 : ℝ)|^4493 ≤ (21369514430107/50000000000000 : ℝ)^3469
        have hw : |(5187563599/10000000000 : ℝ)|=(5187563599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1473806649/2500000000 : ℝ)|^4493 ≤ (50437723871779/100000000000000 : ℝ)^3469
        have hw : |(1473806649/2500000000 : ℝ)|=(1473806649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1258161211/10000000000 : ℝ)|^4493 ≤ (682324726119/10000000000000 : ℝ)^3469
        have hw : |(-1258161211/10000000000 : ℝ)|=(1258161211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s0_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4157116949/10000000000 : ℝ)*x 0 + (1088368883/2000000000 : ℝ)*x 1 + (315514981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4157116949/10000000000 : ℝ)^4493 ≤ (641645378513/2000000000000 : ℝ)^3469 := by
    have hnat : (4157116949 : ℕ)^4493*2000000000000^3469 ≤ 641645378513^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157116949 10000000000 641645378513 2000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088368883/2000000000 : ℝ)^4493 ≤ (45471794463931/100000000000000 : ℝ)^3469 := by
    have hnat : (1088368883 : ℕ)^4493*100000000000000^3469 ≤ 45471794463931^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088368883 2000000000 45471794463931 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315514981/1000000000 : ℝ)^4493 ≤ (11222968300073/50000000000000 : ℝ)^3469 := by
    have hnat : (315514981 : ℕ)^4493*50000000000000^3469 ≤ 11222968300073^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315514981 1000000000 11222968300073 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4157116949/10000000000 : ℝ), (1088368883/2000000000 : ℝ), (315514981/1000000000 : ℝ)] ![(641645378513/2000000000000 : ℝ), (45471794463931/100000000000000 : ℝ), (11222968300073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4157116949/10000000000 : ℝ)|^4493 ≤ (641645378513/2000000000000 : ℝ)^3469
        have hw : |(4157116949/10000000000 : ℝ)|=(4157116949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088368883/2000000000 : ℝ)|^4493 ≤ (45471794463931/100000000000000 : ℝ)^3469
        have hw : |(1088368883/2000000000 : ℝ)|=(1088368883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315514981/1000000000 : ℝ)|^4493 ≤ (11222968300073/50000000000000 : ℝ)^3469
        have hw : |(315514981/1000000000 : ℝ)|=(315514981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (529/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25667/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4491/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4491 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4491*1^1024 ≤ 0^1024*1^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4491/1024 : ℝ) ≤ (898892424134362919/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4491 ≤ (898892424134362919/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4491*50000000000000000000^1024 ≤ 898892424134362919^1024*5^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 898892424134362919 50000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (898892424134362919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4491 := by
      have hnat : (1 : ℕ)^1024*1^4491 ≤ 1^4491*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50898892424134362919/50000000000000000000 : ℝ) ≤ (5020355052444549/5000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50898892424134362919/50000000000000000000 : ℝ)^1024 ≤ (5020355052444549/5000000000000000 : ℝ)^4491 := by
      have hnat : (50898892424134362919 : ℕ)^1024*5000000000000000^4491 ≤ 5020355052444549^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50898892424134362919 50000000000000000000 5020355052444549 5000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020355052444549/5000000000000000 : ℝ)) (X := (50898892424134362919/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25898892424134362919/25000000000000000000 : ℝ) ≤ (2520355052444549/2500000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (25898892424134362919/25000000000000000000 : ℝ)^1024 ≤ (2520355052444549/2500000000000000 : ℝ)^4491 := by
      have hnat : (25898892424134362919 : ℕ)^1024*2500000000000000^4491 ≤ 2520355052444549^4491*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25898892424134362919 25000000000000000000 2520355052444549 2500000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2520355052444549/2500000000000000 : ℝ)) (X := (25898892424134362919/25000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(20355052444549/2000000000000000 : ℝ)*(0 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20355052444549/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(898892424134362919/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(20355052444549/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (1 : ℝ)+(20355052444549/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5020355052444549/5000000000000000 : ℝ) by norm_num, show 1+(898892424134362919/50000000000000000000 : ℝ)+(0 : ℝ)=(50898892424134362919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(898892424134362919/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(20355052444549/2000000000000000 : ℝ)*(2/5 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20355052444549/2000000000000000 : ℝ)*(2/5 : ℝ)=(2520355052444549/2500000000000000 : ℝ) by norm_num, show 1+2*(898892424134362919/50000000000000000000 : ℝ)=(25898892424134362919/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(20355052444549/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20355052444549/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(20355052444549/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20355052444549/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(20355052444549/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20355052444549/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85039181/500000000 : ℝ)*X 0 0+(296184469/500000000 : ℝ)*X 0 1+(2424641851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((685129129/1250000000 : ℝ)*X 1 0+(-72003253/312500000 : ℝ)*X 1 1+(4849283681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5481033061/10000000000 : ℝ)*X 2 0+(484928369/1000000000 : ℝ)*X 2 1+(-144006503/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2074470151/5000000000 : ℝ)*X 0 0+(3091244157/10000000000 : ℝ)*X 0 1+(2751767731/5000000000 : ℝ)*X 0 2+(2074470151/5000000000 : ℝ)*X 1 0+(3091244157/10000000000 : ℝ)*X 1 1+(2751767731/5000000000 : ℝ)*X 1 2+(2074470151/5000000000 : ℝ)*X 2 0+(3091244157/10000000000 : ℝ)*X 2 1+(2751767731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-340885083/2000000000 : ℝ)*X 0 0+(4876760173/10000000000 : ℝ)*X 0 1+(2947613389/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5187563529/10000000000 : ℝ)*X 1 0+(-1258161373/10000000000 : ℝ)*X 1 1+(18422583/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5187563599/10000000000 : ℝ)*X 2 0+(1473806649/2500000000 : ℝ)*X 2 1+(-1258161211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4157116949/10000000000 : ℝ)*X 0 0+(1088368883/2000000000 : ℝ)*X 0 1+(315514981/1000000000 : ℝ)*X 0 2+(4157116949/10000000000 : ℝ)*X 1 0+(1088368883/2000000000 : ℝ)*X 1 1+(315514981/1000000000 : ℝ)*X 1 2+(4157116949/10000000000 : ℝ)*X 2 0+(1088368883/2000000000 : ℝ)*X 2 1+(315514981/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71772979396759872345249/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (344839/500000000000 : ℝ)*(base1) + (1608284941/100000000000000 : ℝ)*(base19) + (1613209549/100000000000000 : ℝ)*(base23) + (195288879/100000000000000 : ℝ)*(upper3) + (210249743/100000000000000 : ℝ)*(upper5) + (336326735405233/50000000000000 : ℝ)*(major0) + (336326735405233/50000000000000 : ℝ)*(major1) + (336326735405233/50000000000000 : ℝ)*(major2) + (930752437872117/100000000000000 : ℝ)*(sp0) + (116344559377809/12500000000000 : ℝ)*(sp1) + (116344558762233/12500000000000 : ℝ)*(sp2) + (207273022724957/50000000000000 : ℝ)*(sp3) + (714300387/12500000000000 : ℝ)*(sp4) + (313081567/12500000000000 : ℝ)*(sp7) + (414548619070251/100000000000000 : ℝ)*(f.failure) + (930758083307413/100000000000000 : ℝ)*(f.sum) + (70031861324917/50000000000000000000000000000 : ℝ)*base65 + (277929576324917/100000000000000000000000000000 : ℝ)*base67 + (185293751924917/100000000000000000000000000000 : ℝ)*base69 + (207408597324917/100000000000000000000000000000 : ℝ)*base71 + (62255095624917/50000000000000000000000000000 : ℝ)*base73 + (62869990924917/100000000000000000000000000000 : ℝ)*base75 + (355889937324917/100000000000000000000000000000 : ℝ)*base77 + (150802932875083/100000000000000000000000000000 : ℝ)*base80 + (16599029124917/50000000000000000000000000000 : ℝ)*base81 + (806167/500000000000000000000 : ℝ)*base90 + (806167/500000000000000000000 : ℝ)*base92 + (806167/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (232271107605069896747409/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1941781867/100000000000000 : ℝ)*(base19) + (1977997979/100000000000000 : ℝ)*(base23) + (3837849/3125000000000 : ℝ)*(base32) + (28390131/10000000000000 : ℝ)*(upper3) + (103564647/50000000000000 : ℝ)*(upper5) + (354795071478047/50000000000000 : ℝ)*(major0) + (354795071478047/50000000000000 : ℝ)*(major1) + (354795071478047/50000000000000 : ℝ)*(major2) + (2350756659/50000000000000 : ℝ)*(sp1) + (255374707/5000000000000 : ℝ)*(sp2) + (245466927437113/25000000000000 : ℝ)*(sp4) + (490930533226633/50000000000000 : ℝ)*(sp5) + (245465156064083/25000000000000 : ℝ)*(sp6) + (437312143657753/100000000000000 : ℝ)*(sp7) + (437312266468921/100000000000000 : ℝ)*(f.failure) + (245466927437113/25000000000000 : ℝ)*(f.sum) + (7481537465803/50000000000000000000000000000 : ℝ)*base65 + (381876230784197/100000000000000000000000000000 : ℝ)*base68 + (1037968520284197/100000000000000000000000000000 : ℝ)*base70 + (70427210384197/100000000000000000000000000000 : ℝ)*base72 + (55711200865803/50000000000000000000000000000 : ℝ)*base73 + (220874606484197/100000000000000000000000000000 : ℝ)*base76 + (80603762184197/100000000000000000000000000000 : ℝ)*base78 + (25714258384197/100000000000000000000000000000 : ℝ)*base80 + (158684069584197/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2993443/500000000000000000000 : ℝ)*base89 + (2993443/500000000000000000000 : ℝ)*base91 + (2993443/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1498_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (529/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25667/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1498_s1_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464567347/2500000000 : ℝ)*x 0 + (2790003849/5000000000 : ℝ)*x 1 + (1272951839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464567347/2500000000 : ℝ)^4493 ≤ (2826830986843/25000000000000 : ℝ)^3469 := by
    have hnat : (464567347 : ℕ)^4493*25000000000000^3469 ≤ 2826830986843^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464567347 2500000000 2826830986843 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2790003849/5000000000 : ℝ)^4493 ≤ (4697263839719/10000000000000 : ℝ)^3469 := by
    have hnat : (2790003849 : ℕ)^4493*10000000000000^3469 ≤ 4697263839719^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790003849 5000000000 4697263839719 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272951839/2500000000 : ℝ)^4493 ≤ (8344007527073/20000000000000 : ℝ)^3469 := by
    have hnat : (1272951839 : ℕ)^4493*20000000000000^3469 ≤ 8344007527073^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272951839 2500000000 8344007527073 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464567347/2500000000 : ℝ), (2790003849/5000000000 : ℝ), (1272951839/2500000000 : ℝ)] ![(2826830986843/25000000000000 : ℝ), (4697263839719/10000000000000 : ℝ), (8344007527073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464567347/2500000000 : ℝ)|^4493 ≤ (2826830986843/25000000000000 : ℝ)^3469
        have hw : |(-464567347/2500000000 : ℝ)|=(464567347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2790003849/5000000000 : ℝ)|^4493 ≤ (4697263839719/10000000000000 : ℝ)^3469
        have hw : |(2790003849/5000000000 : ℝ)|=(2790003849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1272951839/2500000000 : ℝ)|^4493 ≤ (8344007527073/20000000000000 : ℝ)^3469
        have hw : |(1272951839/2500000000 : ℝ)|=(1272951839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389195581/10000000000 : ℝ)*x 0 + (-1057898111/5000000000 : ℝ)*x 1 + (5091808033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389195581/10000000000 : ℝ)^4493 ≤ (44902817290141/100000000000000 : ℝ)^3469 := by
    have hnat : (5389195581 : ℕ)^4493*100000000000000^3469 ≤ 44902817290141^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389195581 10000000000 44902817290141 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057898111/5000000000 : ℝ)^4493 ≤ (13377137865473/100000000000000 : ℝ)^3469 := by
    have hnat : (1057898111 : ℕ)^4493*100000000000000^3469 ≤ 13377137865473^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057898111 5000000000 13377137865473 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5091808033/10000000000 : ℝ)^4493 ≤ (8344008963963/20000000000000 : ℝ)^3469 := by
    have hnat : (5091808033 : ℕ)^4493*20000000000000^3469 ≤ 8344008963963^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091808033 10000000000 8344008963963 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389195581/10000000000 : ℝ), (-1057898111/5000000000 : ℝ), (5091808033/10000000000 : ℝ)] ![(44902817290141/100000000000000 : ℝ), (13377137865473/100000000000000 : ℝ), (8344008963963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389195581/10000000000 : ℝ)|^4493 ≤ (44902817290141/100000000000000 : ℝ)^3469
        have hw : |(5389195581/10000000000 : ℝ)|=(5389195581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057898111/5000000000 : ℝ)|^4493 ≤ (13377137865473/100000000000000 : ℝ)^3469
        have hw : |(-1057898111/5000000000 : ℝ)|=(1057898111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5091808033/10000000000 : ℝ)|^4493 ≤ (8344008963963/20000000000000 : ℝ)^3469
        have hw : |(5091808033/10000000000 : ℝ)|=(5091808033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694598089/5000000000 : ℝ)*x 0 + (5091807657/10000000000 : ℝ)*x 1 + (-528948981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694598089/5000000000 : ℝ)^4493 ≤ (22451411866333/50000000000000 : ℝ)^3469 := by
    have hnat : (2694598089 : ℕ)^4493*50000000000000^3469 ≤ 22451411866333^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694598089 5000000000 22451411866333 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091807657/10000000000 : ℝ)^4493 ≤ (41720040829633/100000000000000 : ℝ)^3469 := by
    have hnat : (5091807657 : ℕ)^4493*100000000000000^3469 ≤ 41720040829633^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091807657 10000000000 41720040829633 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528948981/2500000000 : ℝ)^4493 ≤ (3344283856301/25000000000000 : ℝ)^3469 := by
    have hnat : (528948981 : ℕ)^4493*25000000000000^3469 ≤ 3344283856301^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528948981 2500000000 3344283856301 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694598089/5000000000 : ℝ), (5091807657/10000000000 : ℝ), (-528948981/2500000000 : ℝ)] ![(22451411866333/50000000000000 : ℝ), (41720040829633/100000000000000 : ℝ), (3344283856301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694598089/5000000000 : ℝ)|^4493 ≤ (22451411866333/50000000000000 : ℝ)^3469
        have hw : |(2694598089/5000000000 : ℝ)|=(2694598089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091807657/10000000000 : ℝ)|^4493 ≤ (41720040829633/100000000000000 : ℝ)^3469
        have hw : |(5091807657/10000000000 : ℝ)|=(5091807657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528948981/2500000000 : ℝ)|^4493 ≤ (3344283856301/25000000000000 : ℝ)^3469
        have hw : |(-528948981/2500000000 : ℝ)|=(528948981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254714631/10000000000 : ℝ)*x 0 + (3736800823/10000000000 : ℝ)*x 1 + (2416461839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254714631/10000000000 : ℝ)^4493 ≤ (1322446774923/4000000000000 : ℝ)^3469 := by
    have hnat : (4254714631 : ℕ)^4493*4000000000000^3469 ≤ 1322446774923^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254714631 10000000000 1322446774923 4000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3736800823/10000000000 : ℝ)^4493 ≤ (13972623384609/50000000000000 : ℝ)^3469 := by
    have hnat : (3736800823 : ℕ)^4493*50000000000000^3469 ≤ 13972623384609^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736800823 10000000000 13972623384609 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416461839/5000000000 : ℝ)^4493 ≤ (9748395962543/25000000000000 : ℝ)^3469 := by
    have hnat : (2416461839 : ℕ)^4493*25000000000000^3469 ≤ 9748395962543^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416461839 5000000000 9748395962543 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254714631/10000000000 : ℝ), (3736800823/10000000000 : ℝ), (2416461839/5000000000 : ℝ)] ![(1322446774923/4000000000000 : ℝ), (13972623384609/50000000000000 : ℝ), (9748395962543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254714631/10000000000 : ℝ)|^4493 ≤ (1322446774923/4000000000000 : ℝ)^3469
        have hw : |(4254714631/10000000000 : ℝ)|=(4254714631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3736800823/10000000000 : ℝ)|^4493 ≤ (13972623384609/50000000000000 : ℝ)^3469
        have hw : |(3736800823/10000000000 : ℝ)|=(3736800823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2416461839/5000000000 : ℝ)|^4493 ≤ (9748395962543/25000000000000 : ℝ)^3469
        have hw : |(2416461839/5000000000 : ℝ)|=(2416461839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929299403/5000000000 : ℝ)*x 0 + (1019475309/2000000000 : ℝ)*x 1 + (1393586791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929299403/5000000000 : ℝ)^4493 ≤ (11309920170229/100000000000000 : ℝ)^3469 := by
    have hnat : (929299403 : ℕ)^4493*100000000000000^3469 ≤ 11309920170229^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929299403 5000000000 11309920170229 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019475309/2000000000 : ℝ)^4493 ≤ (4177914844223/10000000000000 : ℝ)^3469 := by
    have hnat : (1019475309 : ℕ)^4493*10000000000000^3469 ≤ 4177914844223^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019475309 2000000000 4177914844223 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1393586791/2500000000 : ℝ)^4493 ≤ (938218627371/2000000000000 : ℝ)^3469 := by
    have hnat : (1393586791 : ℕ)^4493*2000000000000^3469 ≤ 938218627371^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393586791 2500000000 938218627371 2000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929299403/5000000000 : ℝ), (1019475309/2000000000 : ℝ), (1393586791/2500000000 : ℝ)] ![(11309920170229/100000000000000 : ℝ), (4177914844223/10000000000000 : ℝ), (938218627371/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929299403/5000000000 : ℝ)|^4493 ≤ (11309920170229/100000000000000 : ℝ)^3469
        have hw : |(-929299403/5000000000 : ℝ)|=(929299403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1019475309/2000000000 : ℝ)|^4493 ≤ (4177914844223/10000000000000 : ℝ)^3469
        have hw : |(1019475309/2000000000 : ℝ)|=(1019475309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1393586791/2500000000 : ℝ)|^4493 ≤ (938218627371/2000000000000 : ℝ)^3469
        have hw : |(1393586791/2500000000 : ℝ)|=(1393586791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260827669/10000000000 : ℝ)*x 0 + (-40831417/250000000 : ℝ)*x 1 + (5574347283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260827669/10000000000 : ℝ)^4493 ≤ (8704486549599/20000000000000 : ℝ)^3469 := by
    have hnat : (5260827669 : ℕ)^4493*20000000000000^3469 ≤ 8704486549599^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260827669 10000000000 8704486549599 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40831417/250000000 : ℝ)^4493 ≤ (2391658643187/25000000000000 : ℝ)^3469 := by
    have hnat : (40831417 : ℕ)^4493*25000000000000^3469 ≤ 2391658643187^3469*250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40831417 250000000 2391658643187 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5574347283/10000000000 : ℝ)^4493 ≤ (46910932665607/100000000000000 : ℝ)^3469 := by
    have hnat : (5574347283 : ℕ)^4493*100000000000000^3469 ≤ 46910932665607^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574347283 10000000000 46910932665607 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260827669/10000000000 : ℝ), (-40831417/250000000 : ℝ), (5574347283/10000000000 : ℝ)] ![(8704486549599/20000000000000 : ℝ), (2391658643187/25000000000000 : ℝ), (46910932665607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260827669/10000000000 : ℝ)|^4493 ≤ (8704486549599/20000000000000 : ℝ)^3469
        have hw : |(5260827669/10000000000 : ℝ)|=(5260827669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40831417/250000000 : ℝ)|^4493 ≤ (2391658643187/25000000000000 : ℝ)^3469
        have hw : |(-40831417/250000000 : ℝ)|=(40831417/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5574347283/10000000000 : ℝ)|^4493 ≤ (46910932665607/100000000000000 : ℝ)^3469
        have hw : |(5574347283/10000000000 : ℝ)|=(5574347283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526082757/1000000000 : ℝ)*x 0 + (2787173653/5000000000 : ℝ)*x 1 + (-1633256787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526082757/1000000000 : ℝ)^4493 ≤ (10880607921803/25000000000000 : ℝ)^3469 := by
    have hnat : (526082757 : ℕ)^4493*25000000000000^3469 ≤ 10880607921803^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526082757 1000000000 10880607921803 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787173653/5000000000 : ℝ)^4493 ≤ (46910932916299/100000000000000 : ℝ)^3469 := by
    have hnat : (2787173653 : ℕ)^4493*100000000000000^3469 ≤ 46910932916299^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787173653 5000000000 46910932916299 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633256787/10000000000 : ℝ)^4493 ≤ (1913327076899/20000000000000 : ℝ)^3469 := by
    have hnat : (1633256787 : ℕ)^4493*20000000000000^3469 ≤ 1913327076899^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633256787 10000000000 1913327076899 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526082757/1000000000 : ℝ), (2787173653/5000000000 : ℝ), (-1633256787/10000000000 : ℝ)] ![(10880607921803/25000000000000 : ℝ), (46910932916299/100000000000000 : ℝ), (1913327076899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526082757/1000000000 : ℝ)|^4493 ≤ (10880607921803/25000000000000 : ℝ)^3469
        have hw : |(526082757/1000000000 : ℝ)|=(526082757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787173653/5000000000 : ℝ)|^4493 ≤ (46910932916299/100000000000000 : ℝ)^3469
        have hw : |(2787173653/5000000000 : ℝ)|=(2787173653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1633256787/10000000000 : ℝ)|^4493 ≤ (1913327076899/20000000000000 : ℝ)^3469
        have hw : |(-1633256787/10000000000 : ℝ)|=(1633256787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s1_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127727387/5000000000 : ℝ)*x 0 + (19281683/40000000 : ℝ)*x 1 + (1874754723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127727387/5000000000 : ℝ)^4493 ≤ (8267154630593/25000000000000 : ℝ)^3469 := by
    have hnat : (2127727387 : ℕ)^4493*25000000000000^3469 ≤ 8267154630593^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127727387 5000000000 8267154630593 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19281683/40000000 : ℝ)^4493 ≤ (38862978458353/100000000000000 : ℝ)^3469 := by
    have hnat : (19281683 : ℕ)^4493*100000000000000^3469 ≤ 38862978458353^3469*40000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19281683 40000000 38862978458353 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1874754723/5000000000 : ℝ)^4493 ≤ (14034201499019/50000000000000 : ℝ)^3469 := by
    have hnat : (1874754723 : ℕ)^4493*50000000000000^3469 ≤ 14034201499019^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874754723 5000000000 14034201499019 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127727387/5000000000 : ℝ), (19281683/40000000 : ℝ), (1874754723/5000000000 : ℝ)] ![(8267154630593/25000000000000 : ℝ), (38862978458353/100000000000000 : ℝ), (14034201499019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127727387/5000000000 : ℝ)|^4493 ≤ (8267154630593/25000000000000 : ℝ)^3469
        have hw : |(2127727387/5000000000 : ℝ)|=(2127727387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19281683/40000000 : ℝ)|^4493 ≤ (38862978458353/100000000000000 : ℝ)^3469
        have hw : |(19281683/40000000 : ℝ)|=(19281683/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1874754723/5000000000 : ℝ)|^4493 ≤ (14034201499019/50000000000000 : ℝ)^3469
        have hw : |(1874754723/5000000000 : ℝ)|=(1874754723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (529/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2041/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2311/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (529/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (529/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (529/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (529/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (529/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (529/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (529/20000 : ℝ) ^ (4491/1024 : ℝ) ≤ (12054958925139/100000000000000000000 : ℝ) := by
    have hpowers : (529/20000 : ℝ)^4491 ≤ (12054958925139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (529 : ℕ)^4491*100000000000000000000^1024 ≤ 12054958925139^1024*20000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        529 20000 12054958925139 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (529/20000 : ℝ)) (X := (12054958925139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25667/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (1284226152816121/500000000000000000 : ℝ) := by
    have hpowers : (25667/100000 : ℝ)^4491 ≤ (1284226152816121/500000000000000000 : ℝ)^1024 := by
      have hnat : (25667 : ℕ)^4491*500000000000000000^1024 ≤ 1284226152816121^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25667 100000 1284226152816121 500000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25667/100000 : ℝ)) (X := (1284226152816121/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000012054958925139/50000000000000000000 : ℝ) ≤ (10000000549733993/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50000012054958925139/50000000000000000000 : ℝ)^1024 ≤ (10000000549733993/10000000000000000 : ℝ)^4491 := by
      have hnat : (50000012054958925139 : ℕ)^1024*10000000000000000^4491 ≤ 10000000549733993^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000012054958925139 50000000000000000000 10000000549733993 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000549733993/10000000000000000 : ℝ)) (X := (50000012054958925139/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100256857285522149339/100000000000000000000 : ℝ) ≤ (1250731355714669/1250000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (100256857285522149339/100000000000000000000 : ℝ)^1024 ≤ (1250731355714669/1250000000000000 : ℝ)^4491 := by
      have hnat : (100256857285522149339 : ℕ)^1024*1250000000000000^4491 ≤ 1250731355714669^4491*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100256857285522149339 100000000000000000000 1250731355714669 1250000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250731355714669/1250000000000000 : ℝ)) (X := (100256857285522149339/100000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (251284226152816121/250000000000000000 : ℝ) ≤ (10011701141700711/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (251284226152816121/250000000000000000 : ℝ)^1024 ≤ (10011701141700711/10000000000000000 : ℝ)^4491 := by
      have hnat : (251284226152816121 : ℕ)^1024*10000000000000000^4491 ≤ 10011701141700711^4491*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251284226152816121 250000000000000000 10011701141700711 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011701141700711/10000000000000000 : ℝ)) (X := (251284226152816121/250000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12054958925139/100000000000000000000 : ℝ) ≤ ((28773633073778002217/28777500000000000000 : ℝ)+2*(5850295983359/2302200000000000 : ℝ)*(529/20000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (28773633073778002217/28777500000000000000 : ℝ)+2*(5850295983359/2302200000000000 : ℝ)*(529/20000 : ℝ)=(10000000549733993/10000000000000000 : ℝ) by norm_num, show 1+2*(12054958925139/100000000000000000000 : ℝ)=(50000012054958925139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1284226152816121/500000000000000000 : ℝ)+(12054958925139/100000000000000000000 : ℝ) ≤ ((28773633073778002217/28777500000000000000 : ℝ)+(5850295983359/2302200000000000 : ℝ)*((25667/100000 : ℝ)+(529/20000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (28773633073778002217/28777500000000000000 : ℝ)+(5850295983359/2302200000000000 : ℝ)*((25667/100000 : ℝ)+(529/20000 : ℝ))=(1250731355714669/1250000000000000 : ℝ) by norm_num, show 1+(1284226152816121/500000000000000000 : ℝ)+(12054958925139/100000000000000000000 : ℝ)=(100256857285522149339/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1284226152816121/500000000000000000 : ℝ) ≤ ((28773633073778002217/28777500000000000000 : ℝ)+2*(5850295983359/2302200000000000 : ℝ)*(25667/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (28773633073778002217/28777500000000000000 : ℝ)+2*(5850295983359/2302200000000000 : ℝ)*(25667/100000 : ℝ)=(10011701141700711/10000000000000000 : ℝ) by norm_num, show 1+2*(1284226152816121/500000000000000000 : ℝ)=(251284226152816121/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28773633073778002217/28777500000000000000 : ℝ)*(X 1 0+X 2 0)+(5850295983359/2302200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (529/20000 : ℝ)) (hi := (25667/100000 : ℝ)) (c := (28773633073778002217/28777500000000000000 : ℝ)) (alpha := (5850295983359/2302200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28773633073778002217/28777500000000000000 : ℝ)*(X 0 1+X 2 1)+(5850295983359/2302200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (529/20000 : ℝ)) (hi := (25667/100000 : ℝ)) (c := (28773633073778002217/28777500000000000000 : ℝ)) (alpha := (5850295983359/2302200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28773633073778002217/28777500000000000000 : ℝ)*(X 0 2+X 1 2)+(5850295983359/2302200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (529/20000 : ℝ)) (hi := (25667/100000 : ℝ)) (c := (28773633073778002217/28777500000000000000 : ℝ)) (alpha := (5850295983359/2302200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-464567347/2500000000 : ℝ)*X 0 0+(2790003849/5000000000 : ℝ)*X 0 1+(1272951839/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5389195581/10000000000 : ℝ)*X 1 0+(-1057898111/5000000000 : ℝ)*X 1 1+(5091808033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2694598089/5000000000 : ℝ)*X 2 0+(5091807657/10000000000 : ℝ)*X 2 1+(-528948981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4254714631/10000000000 : ℝ)*X 0 0+(3736800823/10000000000 : ℝ)*X 0 1+(2416461839/5000000000 : ℝ)*X 0 2+(4254714631/10000000000 : ℝ)*X 1 0+(3736800823/10000000000 : ℝ)*X 1 1+(2416461839/5000000000 : ℝ)*X 1 2+(4254714631/10000000000 : ℝ)*X 2 0+(3736800823/10000000000 : ℝ)*X 2 1+(2416461839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929299403/5000000000 : ℝ)*X 0 0+(1019475309/2000000000 : ℝ)*X 0 1+(1393586791/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260827669/10000000000 : ℝ)*X 1 0+(-40831417/250000000 : ℝ)*X 1 1+(5574347283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526082757/1000000000 : ℝ)*X 2 0+(2787173653/5000000000 : ℝ)*X 2 1+(-1633256787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127727387/5000000000 : ℝ)*X 0 0+(19281683/40000000 : ℝ)*X 0 1+(1874754723/5000000000 : ℝ)*X 0 2+(2127727387/5000000000 : ℝ)*X 1 0+(19281683/40000000 : ℝ)*X 1 1+(1874754723/5000000000 : ℝ)*X 1 2+(2127727387/5000000000 : ℝ)*X 2 0+(19281683/40000000 : ℝ)*X 2 1+(1874754723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540474814995267113280172319/79937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1491318861/100000000000000 : ℝ)*(base19) + (1696036679/100000000000000 : ℝ)*(base23) + (5036297/5000000000000 : ℝ)*(upper3) + (5980511/50000000000000 : ℝ)*(upper4) + (276806999/100000000000000 : ℝ)*(upper5) + (740171667772907/50000000000000 : ℝ)*(major0) + (740171667772907/50000000000000 : ℝ)*(major1) + (740171667772907/50000000000000 : ℝ)*(major2) + (102417593564873/5000000000000 : ℝ)*(sp0) + (512091583870151/25000000000000 : ℝ)*(sp1) + (1024183065381393/50000000000000 : ℝ)*(sp2) + (456156408724499/50000000000000 : ℝ)*(sp3) + (3191100401/20000000000000 : ℝ)*(sp4) + (1160293849/20000000000000 : ℝ)*(sp7) + (912318618918243/100000000000000 : ℝ)*(f.failure) + (409673565359893/20000000000000 : ℝ)*(f.sum) + (253319231797577/57555000000000000000000000000 : ℝ)*base66 + (2690453002302059227/479625000000000000000000000000000 : ℝ)*base68 + (4488070036757684227/479625000000000000000000000000000 : ℝ)*base70 + (4568303528373434227/479625000000000000000000000000000 : ℝ)*base72 + (237303180821267/57555000000000000000000000000 : ℝ)*base74 + (3769933448585684227/479625000000000000000000000000000 : ℝ)*base76 + (4543277167824434227/479625000000000000000000000000000 : ℝ)*base78 + (3155752849138184227/479625000000000000000000000000000 : ℝ)*base80 + (127580192646137/57555000000000000000000000000 : ℝ)*base82 + (5673169/500000000000000000000 : ℝ)*base89 + (5673169/500000000000000000000 : ℝ)*base91 + (5673169/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2196458451087884115214520027/239812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1749521837/100000000000000 : ℝ)*(base19) + (1830144013/100000000000000 : ℝ)*(base23) + (124751549/50000000000000 : ℝ)*(upper3) + (50548929/100000000000000 : ℝ)*(lower4) + (162087389/100000000000000 : ℝ)*(upper5) + (1515174125312681/100000000000000 : ℝ)*(major0) + (1515174125312681/100000000000000 : ℝ)*(major1) + (1515174125312681/100000000000000 : ℝ)*(major2) + (11392308809/100000000000000 : ℝ)*(sp1) + (6187714447/50000000000000 : ℝ)*(sp2) + (419312702032579/20000000000000 : ℝ)*(sp4) + (262068796041531/12500000000000 : ℝ)*(sp5) + (524137326147497/25000000000000 : ℝ)*(sp6) + (58361527197517/6250000000000 : ℝ)*(sp7) + (58361527197517/6250000000000 : ℝ)*(f.failure) + (419312702032579/20000000000000 : ℝ)*(f.sum) + (270411549361901/115110000000000000000000000000 : ℝ)*base66 + (2197198127475516241/959250000000000000000000000000000 : ℝ)*base68 + (2670364801307766241/959250000000000000000000000000000 : ℝ)*base70 + (4366004528945016241/959250000000000000000000000000000 : ℝ)*base72 + (321890109191659/115110000000000000000000000000 : ℝ)*base73 + (2085917950557983759/959250000000000000000000000000000 : ℝ)*base75 + (4901643350891766241/959250000000000000000000000000000 : ℝ)*base78 + (6099730165102266241/959250000000000000000000000000000 : ℝ)*base80 + (59652845378479/115110000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2411/31250000000000000000 : ℝ)*base89 + (2411/31250000000000000000 : ℝ)*base91 + (2411/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1498_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (529/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2041/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2311/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1498_s2_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-471111127/2500000000 : ℝ)*x 0 + (1365636169/2500000000 : ℝ)*x 1 + (5192340863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471111127/2500000000 : ℝ)^4493 ≤ (575701922357/5000000000000 : ℝ)^3469 := by
    have hnat : (471111127 : ℕ)^4493*5000000000000^3469 ≤ 575701922357^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471111127 2500000000 575701922357 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365636169/2500000000 : ℝ)^4493 ≤ (45695948958953/100000000000000 : ℝ)^3469 := by
    have hnat : (1365636169 : ℕ)^4493*100000000000000^3469 ≤ 45695948958953^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365636169 2500000000 45695948958953 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192340863/10000000000 : ℝ)^4493 ≤ (10697503147049/25000000000000 : ℝ)^3469 := by
    have hnat : (5192340863 : ℕ)^4493*25000000000000^3469 ≤ 10697503147049^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192340863 10000000000 10697503147049 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471111127/2500000000 : ℝ), (1365636169/2500000000 : ℝ), (5192340863/10000000000 : ℝ)] ![(575701922357/5000000000000 : ℝ), (45695948958953/100000000000000 : ℝ), (10697503147049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471111127/2500000000 : ℝ)|^4493 ≤ (575701922357/5000000000000 : ℝ)^3469
        have hw : |(-471111127/2500000000 : ℝ)|=(471111127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365636169/2500000000 : ℝ)|^4493 ≤ (45695948958953/100000000000000 : ℝ)^3469
        have hw : |(1365636169/2500000000 : ℝ)|=(1365636169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192340863/10000000000 : ℝ)|^4493 ≤ (10697503147049/25000000000000 : ℝ)^3469
        have hw : |(5192340863/10000000000 : ℝ)|=(5192340863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339871003/2500000000 : ℝ)*x 0 + (-2023659789/10000000000 : ℝ)*x 1 + (2596170079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339871003/2500000000 : ℝ)^4493 ≤ (44582446169987/100000000000000 : ℝ)^3469 := by
    have hnat : (1339871003 : ℕ)^4493*100000000000000^3469 ≤ 44582446169987^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339871003 2500000000 44582446169987 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2023659789/10000000000 : ℝ)^4493 ≤ (50510194981/400000000000 : ℝ)^3469 := by
    have hnat : (2023659789 : ℕ)^4493*400000000000^3469 ≤ 50510194981^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023659789 10000000000 50510194981 400000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596170079/5000000000 : ℝ)^4493 ≤ (42790005063301/100000000000000 : ℝ)^3469 := by
    have hnat : (2596170079 : ℕ)^4493*100000000000000^3469 ≤ 42790005063301^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596170079 5000000000 42790005063301 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339871003/2500000000 : ℝ), (-2023659789/10000000000 : ℝ), (2596170079/5000000000 : ℝ)] ![(44582446169987/100000000000000 : ℝ), (50510194981/400000000000 : ℝ), (42790005063301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339871003/2500000000 : ℝ)|^4493 ≤ (44582446169987/100000000000000 : ℝ)^3469
        have hw : |(1339871003/2500000000 : ℝ)|=(1339871003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2023659789/10000000000 : ℝ)|^4493 ≤ (50510194981/400000000000 : ℝ)^3469
        have hw : |(-2023659789/10000000000 : ℝ)|=(2023659789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596170079/5000000000 : ℝ)|^4493 ≤ (42790005063301/100000000000000 : ℝ)^3469
        have hw : |(2596170079/5000000000 : ℝ)|=(2596170079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679741919/5000000000 : ℝ)*x 0 + (5192340167/10000000000 : ℝ)*x 1 + (-2023660011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679741919/5000000000 : ℝ)^4493 ≤ (1393201384229/3125000000000 : ℝ)^3469 := by
    have hnat : (2679741919 : ℕ)^4493*3125000000000^3469 ≤ 1393201384229^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679741919 5000000000 1393201384229 3125000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192340167/10000000000 : ℝ)^4493 ≤ (42790005159363/100000000000000 : ℝ)^3469 := by
    have hnat : (5192340167 : ℕ)^4493*100000000000000^3469 ≤ 42790005159363^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192340167 10000000000 42790005159363 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023660011/10000000000 : ℝ)^4493 ≤ (1578443817429/12500000000000 : ℝ)^3469 := by
    have hnat : (2023660011 : ℕ)^4493*12500000000000^3469 ≤ 1578443817429^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023660011 10000000000 1578443817429 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679741919/5000000000 : ℝ), (5192340167/10000000000 : ℝ), (-2023660011/10000000000 : ℝ)] ![(1393201384229/3125000000000 : ℝ), (42790005159363/100000000000000 : ℝ), (1578443817429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679741919/5000000000 : ℝ)|^4493 ≤ (1393201384229/3125000000000 : ℝ)^3469
        have hw : |(2679741919/5000000000 : ℝ)|=(2679741919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192340167/10000000000 : ℝ)|^4493 ≤ (42790005159363/100000000000000 : ℝ)^3469
        have hw : |(5192340167/10000000000 : ℝ)|=(5192340167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2023660011/10000000000 : ℝ)|^4493 ≤ (1578443817429/12500000000000 : ℝ)^3469
        have hw : |(-2023660011/10000000000 : ℝ)|=(2023660011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427345749/1000000000 : ℝ)*x 0 + (3979360073/10000000000 : ℝ)*x 1 + (1146507673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427345749/1000000000 : ℝ)^4493 ≤ (2078120252961/6250000000000 : ℝ)^3469 := by
    have hnat : (427345749 : ℕ)^4493*6250000000000^3469 ≤ 2078120252961^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427345749 1000000000 2078120252961 6250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979360073/10000000000 : ℝ)^4493 ≤ (1515841315579/5000000000000 : ℝ)^3469 := by
    have hnat : (3979360073 : ℕ)^4493*5000000000000^3469 ≤ 1515841315579^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979360073 10000000000 1515841315579 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146507673/2500000000 : ℝ)^4493 ≤ (36433249617997/100000000000000 : ℝ)^3469 := by
    have hnat : (1146507673 : ℕ)^4493*100000000000000^3469 ≤ 36433249617997^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146507673 2500000000 36433249617997 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427345749/1000000000 : ℝ), (3979360073/10000000000 : ℝ), (1146507673/2500000000 : ℝ)] ![(2078120252961/6250000000000 : ℝ), (1515841315579/5000000000000 : ℝ), (36433249617997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427345749/1000000000 : ℝ)|^4493 ≤ (2078120252961/6250000000000 : ℝ)^3469
        have hw : |(427345749/1000000000 : ℝ)|=(427345749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979360073/10000000000 : ℝ)|^4493 ≤ (1515841315579/5000000000000 : ℝ)^3469
        have hw : |(3979360073/10000000000 : ℝ)|=(3979360073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146507673/2500000000 : ℝ)|^4493 ≤ (36433249617997/100000000000000 : ℝ)^3469
        have hw : |(1146507673/2500000000 : ℝ)|=(1146507673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18844991/100000000 : ℝ)*x 0 + (259702851/500000000 : ℝ)*x 1 + (1365203497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18844991/100000000 : ℝ)^4493 ≤ (2878617617643/25000000000000 : ℝ)^3469 := by
    have hnat : (18844991 : ℕ)^4493*25000000000000^3469 ≤ 2878617617643^3469*100000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18844991 100000000 2878617617643 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259702851/500000000 : ℝ)^4493 ≤ (21404165536271/50000000000000 : ℝ)^3469 := by
    have hnat : (259702851 : ℕ)^4493*50000000000000^3469 ≤ 21404165536271^3469*500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259702851 500000000 21404165536271 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365203497/2500000000 : ℝ)^4493 ≤ (22838599220053/50000000000000 : ℝ)^3469 := by
    have hnat : (1365203497 : ℕ)^4493*50000000000000^3469 ≤ 22838599220053^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365203497 2500000000 22838599220053 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18844991/100000000 : ℝ), (259702851/500000000 : ℝ), (1365203497/2500000000 : ℝ)] ![(2878617617643/25000000000000 : ℝ), (21404165536271/50000000000000 : ℝ), (22838599220053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18844991/100000000 : ℝ)|^4493 ≤ (2878617617643/25000000000000 : ℝ)^3469
        have hw : |(-18844991/100000000 : ℝ)|=(18844991/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259702851/500000000 : ℝ)|^4493 ≤ (21404165536271/50000000000000 : ℝ)^3469
        have hw : |(259702851/500000000 : ℝ)|=(259702851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365203497/2500000000 : ℝ)|^4493 ≤ (22838599220053/50000000000000 : ℝ)^3469
        have hw : |(1365203497/2500000000 : ℝ)|=(1365203497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288683719/10000000000 : ℝ)*x 0 + (-1755185349/10000000000 : ℝ)*x 1 + (2730407159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288683719/10000000000 : ℝ)^4493 ≤ (2738821414301/6250000000000 : ℝ)^3469 := by
    have hnat : (5288683719 : ℕ)^4493*6250000000000^3469 ≤ 2738821414301^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288683719 10000000000 2738821414301 6250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1755185349/10000000000 : ℝ)^4493 ≤ (10501655337603/100000000000000 : ℝ)^3469 := by
    have hnat : (1755185349 : ℕ)^4493*100000000000000^3469 ≤ 10501655337603^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755185349 10000000000 10501655337603 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730407159/5000000000 : ℝ)^4493 ≤ (9135440403041/20000000000000 : ℝ)^3469 := by
    have hnat : (2730407159 : ℕ)^4493*20000000000000^3469 ≤ 9135440403041^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730407159 5000000000 9135440403041 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288683719/10000000000 : ℝ), (-1755185349/10000000000 : ℝ), (2730407159/5000000000 : ℝ)] ![(2738821414301/6250000000000 : ℝ), (10501655337603/100000000000000 : ℝ), (9135440403041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288683719/10000000000 : ℝ)|^4493 ≤ (2738821414301/6250000000000 : ℝ)^3469
        have hw : |(5288683719/10000000000 : ℝ)|=(5288683719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1755185349/10000000000 : ℝ)|^4493 ≤ (10501655337603/100000000000000 : ℝ)^3469
        have hw : |(-1755185349/10000000000 : ℝ)|=(1755185349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730407159/5000000000 : ℝ)|^4493 ≤ (9135440403041/20000000000000 : ℝ)^3469
        have hw : |(2730407159/5000000000 : ℝ)|=(2730407159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8263567/15625000 : ℝ)*x 0 + (2730406819/5000000000 : ℝ)*x 1 + (-877593731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8263567/15625000 : ℝ)^4493 ≤ (21910566812463/50000000000000 : ℝ)^3469 := by
    have hnat : (8263567 : ℕ)^4493*50000000000000^3469 ≤ 21910566812463^3469*15625000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8263567 15625000 21910566812463 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730406819/5000000000 : ℝ)^4493 ≤ (45677194648333/100000000000000 : ℝ)^3469 := by
    have hnat : (2730406819 : ℕ)^4493*100000000000000^3469 ≤ 45677194648333^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730406819 5000000000 45677194648333 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877593731/5000000000 : ℝ)^4493 ≤ (2625417928011/25000000000000 : ℝ)^3469 := by
    have hnat : (877593731 : ℕ)^4493*25000000000000^3469 ≤ 2625417928011^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877593731 5000000000 2625417928011 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8263567/15625000 : ℝ), (2730406819/5000000000 : ℝ), (-877593731/5000000000 : ℝ)] ![(21910566812463/50000000000000 : ℝ), (45677194648333/100000000000000 : ℝ), (2625417928011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8263567/15625000 : ℝ)|^4493 ≤ (21910566812463/50000000000000 : ℝ)^3469
        have hw : |(8263567/15625000 : ℝ)|=(8263567/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730406819/5000000000 : ℝ)|^4493 ≤ (45677194648333/100000000000000 : ℝ)^3469
        have hw : |(2730406819/5000000000 : ℝ)|=(2730406819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-877593731/5000000000 : ℝ)|^4493 ≤ (2625417928011/25000000000000 : ℝ)^3469
        have hw : |(-877593731/5000000000 : ℝ)|=(877593731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s2_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427358407/1000000000 : ℝ)*x 0 + (4582180979/10000000000 : ℝ)*x 1 + (3983244127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427358407/1000000000 : ℝ)^4493 ≤ (16625599817619/50000000000000 : ℝ)^3469 := by
    have hnat : (427358407 : ℕ)^4493*50000000000000^3469 ≤ 16625599817619^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427358407 1000000000 16625599817619 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582180979/10000000000 : ℝ)^4493 ≤ (227460268839/625000000000 : ℝ)^3469 := by
    have hnat : (4582180979 : ℕ)^4493*625000000000^3469 ≤ 227460268839^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582180979 10000000000 227460268839 625000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983244127/10000000000 : ℝ)^4493 ≤ (30355157335481/100000000000000 : ℝ)^3469 := by
    have hnat : (3983244127 : ℕ)^4493*100000000000000^3469 ≤ 30355157335481^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983244127 10000000000 30355157335481 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427358407/1000000000 : ℝ), (4582180979/10000000000 : ℝ), (3983244127/10000000000 : ℝ)] ![(16625599817619/50000000000000 : ℝ), (227460268839/625000000000 : ℝ), (30355157335481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427358407/1000000000 : ℝ)|^4493 ≤ (16625599817619/50000000000000 : ℝ)^3469
        have hw : |(427358407/1000000000 : ℝ)|=(427358407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582180979/10000000000 : ℝ)|^4493 ≤ (227460268839/625000000000 : ℝ)^3469
        have hw : |(4582180979/10000000000 : ℝ)|=(4582180979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983244127/10000000000 : ℝ)|^4493 ≤ (30355157335481/100000000000000 : ℝ)^3469
        have hw : |(3983244127/10000000000 : ℝ)|=(3983244127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2311/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2041/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5167/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4013/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2311/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2041/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2311/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2041/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2311/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2041/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2311/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2041/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2311/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2041/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2311/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2041/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2041/25000 : ℝ) ^ (4491/1024 : ℝ) ≤ (1690001404957061/100000000000000000000 : ℝ) := by
    have hpowers : (2041/25000 : ℝ)^4491 ≤ (1690001404957061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2041 : ℕ)^4491*100000000000000000000^1024 ≤ 1690001404957061^1024*25000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2041 25000 1690001404957061 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2041/25000 : ℝ)) (X := (1690001404957061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2311/12500 : ℝ) ^ (4491/1024 : ℝ) ≤ (60921171869045239/100000000000000000000 : ℝ) := by
    have hpowers : (2311/12500 : ℝ)^4491 ≤ (60921171869045239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2311 : ℕ)^4491*100000000000000000000^1024 ≤ 60921171869045239^1024*12500^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2311 12500 60921171869045239 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2311/12500 : ℝ)) (X := (60921171869045239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001690001404957061/50000000000000000000 : ℝ) ≤ (10000077066972219/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50001690001404957061/50000000000000000000 : ℝ)^1024 ≤ (10000077066972219/10000000000000000 : ℝ)^4491 := by
      have hnat : (50001690001404957061 : ℕ)^1024*10000000000000000^4491 ≤ 10000077066972219^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001690001404957061 50000000000000000000 10000077066972219 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000077066972219/10000000000000000 : ℝ)) (X := (50001690001404957061/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000626111732740023/1000000000000000000 : ℝ) ≤ (10001427262356167/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (1000626111732740023/1000000000000000000 : ℝ)^1024 ≤ (10001427262356167/10000000000000000 : ℝ)^4491 := by
      have hnat : (1000626111732740023 : ℕ)^1024*10000000000000000^4491 ≤ 10001427262356167^4491*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000626111732740023 1000000000000000000 10001427262356167 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001427262356167/10000000000000000 : ℝ)) (X := (1000626111732740023/1000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50060921171869045239/50000000000000000000 : ℝ) ≤ (2000555491548023/2000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50060921171869045239/50000000000000000000 : ℝ)^1024 ≤ (2000555491548023/2000000000000000 : ℝ)^4491 := by
      have hnat : (50060921171869045239 : ℕ)^1024*2000000000000000^4491 ≤ 2000555491548023^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50060921171869045239 50000000000000000000 2000555491548023 2000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000555491548023/2000000000000000 : ℝ)) (X := (50060921171869045239/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1690001404957061/100000000000000000000 : ℝ) ≤ ((25804687412298021503/25810000000000000000 : ℝ)+2*(337548845987/258100000000000 : ℝ)*(2041/25000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (25804687412298021503/25810000000000000000 : ℝ)+2*(337548845987/258100000000000 : ℝ)*(2041/25000 : ℝ)=(10000077066972219/10000000000000000 : ℝ) by norm_num, show 1+2*(1690001404957061/100000000000000000000 : ℝ)=(50001690001404957061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60921171869045239/100000000000000000000 : ℝ)+(1690001404957061/100000000000000000000 : ℝ) ≤ ((25804687412298021503/25810000000000000000 : ℝ)+(337548845987/258100000000000 : ℝ)*((2311/12500 : ℝ)+(2041/25000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (25804687412298021503/25810000000000000000 : ℝ)+(337548845987/258100000000000 : ℝ)*((2311/12500 : ℝ)+(2041/25000 : ℝ))=(10001427262356167/10000000000000000 : ℝ) by norm_num, show 1+(60921171869045239/100000000000000000000 : ℝ)+(1690001404957061/100000000000000000000 : ℝ)=(1000626111732740023/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60921171869045239/100000000000000000000 : ℝ) ≤ ((25804687412298021503/25810000000000000000 : ℝ)+2*(337548845987/258100000000000 : ℝ)*(2311/12500 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (25804687412298021503/25810000000000000000 : ℝ)+2*(337548845987/258100000000000 : ℝ)*(2311/12500 : ℝ)=(2000555491548023/2000000000000000 : ℝ) by norm_num, show 1+2*(60921171869045239/100000000000000000000 : ℝ)=(50060921171869045239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25804687412298021503/25810000000000000000 : ℝ)*(X 1 0+X 2 0)+(337548845987/258100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (2041/25000 : ℝ)) (hi := (2311/12500 : ℝ)) (c := (25804687412298021503/25810000000000000000 : ℝ)) (alpha := (337548845987/258100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25804687412298021503/25810000000000000000 : ℝ)*(X 0 1+X 2 1)+(337548845987/258100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (2041/25000 : ℝ)) (hi := (2311/12500 : ℝ)) (c := (25804687412298021503/25810000000000000000 : ℝ)) (alpha := (337548845987/258100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25804687412298021503/25810000000000000000 : ℝ)*(X 0 2+X 1 2)+(337548845987/258100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (2041/25000 : ℝ)) (hi := (2311/12500 : ℝ)) (c := (25804687412298021503/25810000000000000000 : ℝ)) (alpha := (337548845987/258100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-471111127/2500000000 : ℝ)*X 0 0+(1365636169/2500000000 : ℝ)*X 0 1+(5192340863/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339871003/2500000000 : ℝ)*X 1 0+(-2023659789/10000000000 : ℝ)*X 1 1+(2596170079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679741919/5000000000 : ℝ)*X 2 0+(5192340167/10000000000 : ℝ)*X 2 1+(-2023660011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427345749/1000000000 : ℝ)*X 0 0+(3979360073/10000000000 : ℝ)*X 0 1+(1146507673/2500000000 : ℝ)*X 0 2+(427345749/1000000000 : ℝ)*X 1 0+(3979360073/10000000000 : ℝ)*X 1 1+(1146507673/2500000000 : ℝ)*X 1 2+(427345749/1000000000 : ℝ)*X 2 0+(3979360073/10000000000 : ℝ)*X 2 1+(1146507673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18844991/100000000 : ℝ)*X 0 0+(259702851/500000000 : ℝ)*X 0 1+(1365203497/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288683719/10000000000 : ℝ)*X 1 0+(-1755185349/10000000000 : ℝ)*X 1 1+(2730407159/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8263567/15625000 : ℝ)*X 2 0+(2730406819/5000000000 : ℝ)*X 2 1+(-877593731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((427358407/1000000000 : ℝ)*X 0 0+(4582180979/10000000000 : ℝ)*X 0 1+(3983244127/10000000000 : ℝ)*X 0 2+(427358407/1000000000 : ℝ)*X 1 0+(4582180979/10000000000 : ℝ)*X 1 1+(3983244127/10000000000 : ℝ)*X 1 2+(427358407/1000000000 : ℝ)*X 2 0+(4582180979/10000000000 : ℝ)*X 2 1+(3983244127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (848588763718979196288686997/129050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (636668451/20000000000000 : ℝ)*(base19) + (2706767377/100000000000000 : ℝ)*(base23) + (28461427/100000000000000 : ℝ)*(upper2) + (90557973/20000000000000 : ℝ)*(upper3) + (43896797/20000000000000 : ℝ)*(upper4) + (267467545110167/10000000000000 : ℝ)*(major0) + (267467545110167/10000000000000 : ℝ)*(major1) + (267467545110167/10000000000000 : ℝ)*(major2) + (3700948458220109/100000000000000 : ℝ)*(sp0) + (925243924078453/25000000000000 : ℝ)*(sp1) + (370097617288869/10000000000000 : ℝ)*(sp2) + (206044247897319/12500000000000 : ℝ)*(sp3) + (15210717979/50000000000000 : ℝ)*(sp4) + (17820180091/100000000000000 : ℝ)*(sp7) + (1648371803358643/100000000000000 : ℝ)*(f.failure) + (3700978879656067/100000000000000 : ℝ)*(f.sum) + (209543580263/129050000000000000000000000 : ℝ)*base66 + (163274892347921001/258100000000000000000000000000000 : ℝ)*base67 + (572704970454378999/258100000000000000000000000000000 : ℝ)*base70 + (137201536141421001/258100000000000000000000000000000 : ℝ)*base71 + (1253905347919/2581000000000000000000000000 : ℝ)*base74 + (3578557949723121001/258100000000000000000000000000000 : ℝ)*base75 + (1173744752514178999/258100000000000000000000000000000 : ℝ)*base78 + (2609392765121321001/258100000000000000000000000000000 : ℝ)*base79 + (12907843631873/2581000000000000000000000000 : ℝ)*base82 + (573631/500000000000000000000 : ℝ)*base90 + (573631/500000000000000000000 : ℝ)*base92 + (573631/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1796586438593581044738237597/322625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1317450361/100000000000000 : ℝ)*(base19) + (611865199/50000000000000 : ℝ)*(base23) + (82216289/20000000000000 : ℝ)*(lower4) + (1705183/5000000000000 : ℝ)*(lower5) + (1354588704126767/50000000000000 : ℝ)*(major0) + (1354588704126767/50000000000000 : ℝ)*(major1) + (1354588704126767/50000000000000 : ℝ)*(major2) + (13441199161/50000000000000 : ℝ)*(sp1) + (780333281/12500000000000 : ℝ)*(sp2) + (841119071/12500000000000 : ℝ)*(sp3) + (1874359833526867/50000000000000 : ℝ)*(sp4) + (3748691467205051/100000000000000 : ℝ)*(sp5) + (58573628135267/1562500000000 : ℝ)*(sp6) + (83481411743951/5000000000000 : ℝ)*(sp7) + (417408740957897/25000000000000 : ℝ)*(f.failure) + (1874359833526867/50000000000000 : ℝ)*(f.sum) + (23106160795771/6452500000000000000000000000 : ℝ)*base66 + (6928421329484770801/1290500000000000000000000000000000 : ℝ)*base67 + (953272659607229199/1290500000000000000000000000000000 : ℝ)*base70 + (945214843310270801/1290500000000000000000000000000000 : ℝ)*base71 + (19948063875177/12905000000000000000000000000 : ℝ)*base74 + (2608115154861770801/1290500000000000000000000000000000 : ℝ)*base75 + (11775786769954770801/1290500000000000000000000000000000 : ℝ)*base77 + (10054739035844770801/1290500000000000000000000000000000 : ℝ)*base79 + (18368650716401/6452500000000000000000000000 : ℝ)*base82 + (366451/125000000000000000000 : ℝ)*base89 + (366451/125000000000000000000 : ℝ)*base91 + (366451/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1498_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2311/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2041/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1498_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1498_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1498_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1498_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1498_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

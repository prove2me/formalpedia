-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1724_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:51.207997+00:00
-- url     : https://prove2.me/submissions/b1e09735-6d5a-4745-91c9-ff248ce588e8

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
theorem support_rectangle_w1724_s3_0 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340764817/2500000000 : ℝ)*x 0 + (1365308881/2500000000 : ℝ)*x 1 + (128495681/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340764817/2500000000 : ℝ)^5415 ≤ (8564063363667/100000000000000 : ℝ)^4391 := by
    have hnat : (340764817 : ℕ)^5415*100000000000000^4391 ≤ 8564063363667^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340764817 2500000000 8564063363667 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365308881/2500000000 : ℝ)^5415 ≤ (47427040076701/100000000000000 : ℝ)^4391 := by
    have hnat : (1365308881 : ℕ)^5415*100000000000000^4391 ≤ 47427040076701^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365308881 2500000000 47427040076701 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128495681/250000000 : ℝ)^5415 ≤ (22004448271641/50000000000000 : ℝ)^4391 := by
    have hnat : (128495681 : ℕ)^5415*50000000000000^4391 ≤ 22004448271641^4391*250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128495681 250000000 22004448271641 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340764817/2500000000 : ℝ), (1365308881/2500000000 : ℝ), (128495681/250000000 : ℝ)] ![(8564063363667/100000000000000 : ℝ), (47427040076701/100000000000000 : ℝ), (22004448271641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340764817/2500000000 : ℝ)|^5415 ≤ (8564063363667/100000000000000 : ℝ)^4391
        have hw : |(-340764817/2500000000 : ℝ)|=(340764817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365308881/2500000000 : ℝ)|^5415 ≤ (47427040076701/100000000000000 : ℝ)^4391
        have hw : |(1365308881/2500000000 : ℝ)|=(1365308881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128495681/250000000 : ℝ)|^5415 ≤ (22004448271641/50000000000000 : ℝ)^4391
        have hw : |(128495681/250000000 : ℝ)|=(128495681/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_1 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5338809613/10000000000 : ℝ)*x 0 + (-30590613/200000000 : ℝ)*x 1 + (5139827297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5338809613/10000000000 : ℝ)^5415 ≤ (11529840978391/25000000000000 : ℝ)^4391 := by
    have hnat : (5338809613 : ℕ)^5415*25000000000000^4391 ≤ 11529840978391^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338809613 10000000000 11529840978391 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30590613/200000000 : ℝ)^5415 ≤ (493586946503/5000000000000 : ℝ)^4391 := by
    have hnat : (30590613 : ℕ)^5415*5000000000000^4391 ≤ 493586946503^4391*200000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30590613 200000000 493586946503 5000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139827297/10000000000 : ℝ)^5415 ≤ (44008897145151/100000000000000 : ℝ)^4391 := by
    have hnat : (5139827297 : ℕ)^5415*100000000000000^4391 ≤ 44008897145151^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139827297 10000000000 44008897145151 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5338809613/10000000000 : ℝ), (-30590613/200000000 : ℝ), (5139827297/10000000000 : ℝ)] ![(11529840978391/25000000000000 : ℝ), (493586946503/5000000000000 : ℝ), (44008897145151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5338809613/10000000000 : ℝ)|^5415 ≤ (11529840978391/25000000000000 : ℝ)^4391
        have hw : |(5338809613/10000000000 : ℝ)|=(5338809613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30590613/200000000 : ℝ)|^5415 ≤ (493586946503/5000000000000 : ℝ)^4391
        have hw : |(-30590613/200000000 : ℝ)|=(30590613/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139827297/10000000000 : ℝ)|^5415 ≤ (44008897145151/100000000000000 : ℝ)^4391
        have hw : |(5139827297/10000000000 : ℝ)|=(5139827297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_2 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166837807/312500000 : ℝ)*x 0 + (1027965421/2000000000 : ℝ)*x 1 + (-764765311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166837807/312500000 : ℝ)^5415 ≤ (46119366161357/100000000000000 : ℝ)^4391 := by
    have hnat : (166837807 : ℕ)^5415*100000000000000^4391 ≤ 46119366161357^4391*312500000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166837807 312500000 46119366161357 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027965421/2000000000 : ℝ)^5415 ≤ (44008895117803/100000000000000 : ℝ)^4391 := by
    have hnat : (1027965421 : ℕ)^5415*100000000000000^4391 ≤ 44008895117803^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027965421 2000000000 44008895117803 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764765311/5000000000 : ℝ)^5415 ≤ (4935869353601/50000000000000 : ℝ)^4391 := by
    have hnat : (764765311 : ℕ)^5415*50000000000000^4391 ≤ 4935869353601^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764765311 5000000000 4935869353601 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166837807/312500000 : ℝ), (1027965421/2000000000 : ℝ), (-764765311/5000000000 : ℝ)] ![(46119366161357/100000000000000 : ℝ), (44008895117803/100000000000000 : ℝ), (4935869353601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166837807/312500000 : ℝ)|^5415 ≤ (46119366161357/100000000000000 : ℝ)^4391
        have hw : |(166837807/312500000 : ℝ)|=(166837807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027965421/2000000000 : ℝ)|^5415 ≤ (44008895117803/100000000000000 : ℝ)^4391
        have hw : |(1027965421/2000000000 : ℝ)|=(1027965421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764765311/5000000000 : ℝ)|^5415 ≤ (4935869353601/50000000000000 : ℝ)^4391
        have hw : |(-764765311/5000000000 : ℝ)|=(764765311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_3 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043567857/5000000000 : ℝ)*x 0 + (3623565253/10000000000 : ℝ)*x 1 + (4585217249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043567857/5000000000 : ℝ)^5415 ≤ (33174189380311/100000000000000 : ℝ)^4391 := by
    have hnat : (2043567857 : ℕ)^5415*100000000000000^4391 ≤ 33174189380311^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043567857 5000000000 33174189380311 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3623565253/10000000000 : ℝ)^5415 ≤ (14298640219323/50000000000000 : ℝ)^4391 := by
    have hnat : (3623565253 : ℕ)^5415*50000000000000^4391 ≤ 14298640219323^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623565253 10000000000 14298640219323 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4585217249/10000000000 : ℝ)^5415 ≤ (38228530171163/100000000000000 : ℝ)^4391 := by
    have hnat : (4585217249 : ℕ)^5415*100000000000000^4391 ≤ 38228530171163^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585217249 10000000000 38228530171163 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043567857/5000000000 : ℝ), (3623565253/10000000000 : ℝ), (4585217249/10000000000 : ℝ)] ![(33174189380311/100000000000000 : ℝ), (14298640219323/50000000000000 : ℝ), (38228530171163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043567857/5000000000 : ℝ)|^5415 ≤ (33174189380311/100000000000000 : ℝ)^4391
        have hw : |(2043567857/5000000000 : ℝ)|=(2043567857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3623565253/10000000000 : ℝ)|^5415 ≤ (14298640219323/50000000000000 : ℝ)^4391
        have hw : |(3623565253/10000000000 : ℝ)|=(3623565253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4585217249/10000000000 : ℝ)|^5415 ≤ (38228530171163/100000000000000 : ℝ)^4391
        have hw : |(4585217249/10000000000 : ℝ)|=(4585217249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_4 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1363202519/10000000000 : ℝ)*x 0 + (321464391/625000000 : ℝ)*x 1 + (2728789449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363202519/10000000000 : ℝ)^5415 ≤ (8565173312963/100000000000000 : ℝ)^4391 := by
    have hnat : (1363202519 : ℕ)^5415*100000000000000^4391 ≤ 8565173312963^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363202519 10000000000 8565173312963 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321464391/625000000 : ℝ)^5415 ≤ (22023472132777/50000000000000 : ℝ)^4391 := by
    have hnat : (321464391 : ℕ)^5415*50000000000000^4391 ≤ 22023472132777^4391*625000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321464391 625000000 22023472132777 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728789449/5000000000 : ℝ)^5415 ≤ (2369394120669/5000000000000 : ℝ)^4391 := by
    have hnat : (2728789449 : ℕ)^5415*5000000000000^4391 ≤ 2369394120669^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728789449 5000000000 2369394120669 5000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1363202519/10000000000 : ℝ), (321464391/625000000 : ℝ), (2728789449/5000000000 : ℝ)] ![(8565173312963/100000000000000 : ℝ), (22023472132777/50000000000000 : ℝ), (2369394120669/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1363202519/10000000000 : ℝ)|^5415 ≤ (8565173312963/100000000000000 : ℝ)^4391
        have hw : |(-1363202519/10000000000 : ℝ)|=(1363202519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321464391/625000000 : ℝ)|^5415 ≤ (22023472132777/50000000000000 : ℝ)^4391
        have hw : |(321464391/625000000 : ℝ)|=(321464391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728789449/5000000000 : ℝ)|^5415 ≤ (2369394120669/5000000000000 : ℝ)^4391
        have hw : |(2728789449/5000000000 : ℝ)|=(2728789449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_5 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252776677/10000000000 : ℝ)*x 0 + (-1211779033/10000000000 : ℝ)*x 1 + (5457578897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252776677/10000000000 : ℝ)^5415 ≤ (22602290078721/50000000000000 : ℝ)^4391 := by
    have hnat : (5252776677 : ℕ)^5415*50000000000000^4391 ≤ 22602290078721^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252776677 10000000000 22602290078721 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1211779033/10000000000 : ℝ)^5415 ≤ (7407537423059/100000000000000 : ℝ)^4391 := by
    have hnat : (1211779033 : ℕ)^5415*100000000000000^4391 ≤ 7407537423059^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211779033 10000000000 7407537423059 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457578897/10000000000 : ℝ)^5415 ≤ (47387882402673/100000000000000 : ℝ)^4391 := by
    have hnat : (5457578897 : ℕ)^5415*100000000000000^4391 ≤ 47387882402673^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457578897 10000000000 47387882402673 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252776677/10000000000 : ℝ), (-1211779033/10000000000 : ℝ), (5457578897/10000000000 : ℝ)] ![(22602290078721/50000000000000 : ℝ), (7407537423059/100000000000000 : ℝ), (47387882402673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252776677/10000000000 : ℝ)|^5415 ≤ (22602290078721/50000000000000 : ℝ)^4391
        have hw : |(5252776677/10000000000 : ℝ)|=(5252776677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1211779033/10000000000 : ℝ)|^5415 ≤ (7407537423059/100000000000000 : ℝ)^4391
        have hw : |(-1211779033/10000000000 : ℝ)|=(1211779033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457578897/10000000000 : ℝ)|^5415 ≤ (47387882402673/100000000000000 : ℝ)^4391
        have hw : |(5457578897/10000000000 : ℝ)|=(5457578897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_6 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252776677/10000000000 : ℝ)*x 0 + (2728789449/5000000000 : ℝ)*x 1 + (-151472379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252776677/10000000000 : ℝ)^5415 ≤ (22602290078721/50000000000000 : ℝ)^4391 := by
    have hnat : (5252776677 : ℕ)^5415*50000000000000^4391 ≤ 22602290078721^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252776677 10000000000 22602290078721 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728789449/5000000000 : ℝ)^5415 ≤ (2369394120669/5000000000000 : ℝ)^4391 := by
    have hnat : (2728789449 : ℕ)^5415*5000000000000^4391 ≤ 2369394120669^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728789449 5000000000 2369394120669 5000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151472379/1250000000 : ℝ)^5415 ≤ (46297108847/625000000000 : ℝ)^4391 := by
    have hnat : (151472379 : ℕ)^5415*625000000000^4391 ≤ 46297108847^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151472379 1250000000 46297108847 625000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252776677/10000000000 : ℝ), (2728789449/5000000000 : ℝ), (-151472379/1250000000 : ℝ)] ![(22602290078721/50000000000000 : ℝ), (2369394120669/5000000000000 : ℝ), (46297108847/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252776677/10000000000 : ℝ)|^5415 ≤ (22602290078721/50000000000000 : ℝ)^4391
        have hw : |(5252776677/10000000000 : ℝ)|=(5252776677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728789449/5000000000 : ℝ)|^5415 ≤ (2369394120669/5000000000000 : ℝ)^4391
        have hw : |(2728789449/5000000000 : ℝ)|=(2728789449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151472379/1250000000 : ℝ)|^5415 ≤ (46297108847/625000000000 : ℝ)^4391
        have hw : |(-151472379/1250000000 : ℝ)|=(151472379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s3_7 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (127736383/312500000 : ℝ)*x 0 + (114360929/250000000 : ℝ)*x 1 + (454313237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127736383/312500000 : ℝ)^5415 ≤ (33178478962429/100000000000000 : ℝ)^4391 := by
    have hnat : (127736383 : ℕ)^5415*100000000000000^4391 ≤ 33178478962429^4391*312500000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127736383 312500000 33178478962429 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114360929/250000000 : ℝ)^5415 ≤ (38117723499859/100000000000000 : ℝ)^4391 := by
    have hnat : (114360929 : ℕ)^5415*100000000000000^4391 ≤ 38117723499859^4391*250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114360929 250000000 38117723499859 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454313237/1250000000 : ℝ)^5415 ≤ (7175949380767/25000000000000 : ℝ)^4391 := by
    have hnat : (454313237 : ℕ)^5415*25000000000000^4391 ≤ 7175949380767^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454313237 1250000000 7175949380767 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127736383/312500000 : ℝ), (114360929/250000000 : ℝ), (454313237/1250000000 : ℝ)] ![(33178478962429/100000000000000 : ℝ), (38117723499859/100000000000000 : ℝ), (7175949380767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127736383/312500000 : ℝ)|^5415 ≤ (33178478962429/100000000000000 : ℝ)^4391
        have hw : |(127736383/312500000 : ℝ)|=(127736383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114360929/250000000 : ℝ)|^5415 ≤ (38117723499859/100000000000000 : ℝ)^4391
        have hw : |(114360929/250000000 : ℝ)|=(114360929/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454313237/1250000000 : ℝ)|^5415 ≤ (7175949380767/25000000000000 : ℝ)^4391
        have hw : |(454313237/1250000000 : ℝ)|=(454313237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1724_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5057/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (531/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10109/100000 : ℝ) ^ (5407/1024 : ℝ) ≤ (555376024833223/100000000000000000000 : ℝ) := by
    have hpowers : (10109/100000 : ℝ)^5407 ≤ (555376024833223/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10109 : ℕ)^5407*100000000000000000000^1024 ≤ 555376024833223^1024*100000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10109 100000 555376024833223 100000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10109/100000 : ℝ)) (X := (555376024833223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16999/100000 : ℝ) ^ (5407/1024 : ℝ) ≤ (8638234370490937/100000000000000000000 : ℝ) := by
    have hpowers : (16999/100000 : ℝ)^5407 ≤ (8638234370490937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16999 : ℕ)^5407*100000000000000000000^1024 ≤ 8638234370490937^1024*100000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16999 100000 8638234370490937 100000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16999/100000 : ℝ)) (X := (8638234370490937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000555376024833223/50000000000000000000 : ℝ) ≤ (5000010517893271/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (50000555376024833223/50000000000000000000 : ℝ)^1024 ≤ (5000010517893271/5000000000000000 : ℝ)^5407 := by
      have hnat : (50000555376024833223 : ℕ)^1024*5000000000000000^5407 ≤ 5000010517893271^5407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000555376024833223 50000000000000000000 5000010517893271 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010517893271/5000000000000000 : ℝ)) (X := (50000555376024833223/50000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (78132182508121347/78125000000000000 : ℝ) ≤ (10000174105904683/10000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (78132182508121347/78125000000000000 : ℝ)^1024 ≤ (10000174105904683/10000000000000000 : ℝ)^5407 := by
      have hnat : (78132182508121347 : ℕ)^1024*10000000000000000^5407 ≤ 10000174105904683^5407*78125000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78132182508121347 78125000000000000 10000174105904683 10000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000174105904683/10000000000000000 : ℝ)) (X := (78132182508121347/78125000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008638234370490937/50000000000000000000 : ℝ) ≤ (1250040897002853/1250000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (50008638234370490937/50000000000000000000 : ℝ)^1024 ≤ (1250040897002853/1250000000000000 : ℝ)^5407 := by
      have hnat : (50008638234370490937 : ℕ)^1024*1250000000000000^5407 ≤ 1250040897002853^5407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008638234370490937 50000000000000000000 1250040897002853 1250000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250040897002853/1250000000000000 : ℝ)) (X := (50008638234370490937/50000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(555376024833223/100000000000000000000 : ℝ) ≤ ((34448525082460349821/34450000000000000000 : ℝ)+2*(153070118141/689000000000000 : ℝ)*(10109/100000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (34448525082460349821/34450000000000000000 : ℝ)+2*(153070118141/689000000000000 : ℝ)*(10109/100000 : ℝ)=(5000010517893271/5000000000000000 : ℝ) by norm_num, show 1+2*(555376024833223/100000000000000000000 : ℝ)=(50000555376024833223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8638234370490937/100000000000000000000 : ℝ)+(555376024833223/100000000000000000000 : ℝ) ≤ ((34448525082460349821/34450000000000000000 : ℝ)+(153070118141/689000000000000 : ℝ)*((16999/100000 : ℝ)+(10109/100000 : ℝ)))^(5407/1024 : ℝ) := by
    rw [show (34448525082460349821/34450000000000000000 : ℝ)+(153070118141/689000000000000 : ℝ)*((16999/100000 : ℝ)+(10109/100000 : ℝ))=(10000174105904683/10000000000000000 : ℝ) by norm_num, show 1+(8638234370490937/100000000000000000000 : ℝ)+(555376024833223/100000000000000000000 : ℝ)=(78132182508121347/78125000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8638234370490937/100000000000000000000 : ℝ) ≤ ((34448525082460349821/34450000000000000000 : ℝ)+2*(153070118141/689000000000000 : ℝ)*(16999/100000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (34448525082460349821/34450000000000000000 : ℝ)+2*(153070118141/689000000000000 : ℝ)*(16999/100000 : ℝ)=(1250040897002853/1250000000000000 : ℝ) by norm_num, show 1+2*(8638234370490937/100000000000000000000 : ℝ)=(50008638234370490937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34448525082460349821/34450000000000000000 : ℝ)*(X 1 0+X 2 0)+(153070118141/689000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (10109/100000 : ℝ)) (hi := (16999/100000 : ℝ)) (c := (34448525082460349821/34450000000000000000 : ℝ)) (alpha := (153070118141/689000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34448525082460349821/34450000000000000000 : ℝ)*(X 0 1+X 2 1)+(153070118141/689000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (10109/100000 : ℝ)) (hi := (16999/100000 : ℝ)) (c := (34448525082460349821/34450000000000000000 : ℝ)) (alpha := (153070118141/689000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34448525082460349821/34450000000000000000 : ℝ)*(X 0 2+X 1 2)+(153070118141/689000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (10109/100000 : ℝ)) (hi := (16999/100000 : ℝ)) (c := (34448525082460349821/34450000000000000000 : ℝ)) (alpha := (153070118141/689000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-340764817/2500000000 : ℝ)*X 0 0+(1365308881/2500000000 : ℝ)*X 0 1+(128495681/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5338809613/10000000000 : ℝ)*X 1 0+(-30590613/200000000 : ℝ)*X 1 1+(5139827297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((166837807/312500000 : ℝ)*X 2 0+(1027965421/2000000000 : ℝ)*X 2 1+(-764765311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2043567857/5000000000 : ℝ)*X 0 0+(3623565253/10000000000 : ℝ)*X 0 1+(4585217249/10000000000 : ℝ)*X 0 2+(2043567857/5000000000 : ℝ)*X 1 0+(3623565253/10000000000 : ℝ)*X 1 1+(4585217249/10000000000 : ℝ)*X 1 2+(2043567857/5000000000 : ℝ)*X 2 0+(3623565253/10000000000 : ℝ)*X 2 1+(4585217249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1363202519/10000000000 : ℝ)*X 0 0+(321464391/625000000 : ℝ)*X 0 1+(2728789449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252776677/10000000000 : ℝ)*X 1 0+(-1211779033/10000000000 : ℝ)*X 1 1+(5457578897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252776677/10000000000 : ℝ)*X 2 0+(2728789449/5000000000 : ℝ)*X 2 1+(-151472379/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((127736383/312500000 : ℝ)*X 0 0+(114360929/250000000 : ℝ)*X 0 1+(454313237/1250000000 : ℝ)*X 0 2+(127736383/312500000 : ℝ)*X 1 0+(114360929/250000000 : ℝ)*X 1 1+(454313237/1250000000 : ℝ)*X 1 2+(127736383/312500000 : ℝ)*X 2 0+(114360929/250000000 : ℝ)*X 2 1+(454313237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22987123835815625007901742367/1722500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1987954639/100000000000000 : ℝ)*(base19) + (1984670789/100000000000000 : ℝ)*(base23) + (67402603/100000000000000 : ℝ)*(lower2) + (317548243/100000000000000 : ℝ)*(upper3) + (130876481/50000000000000 : ℝ)*(upper5) + (2075620154175591/100000000000000 : ℝ)*(major0) + (2075620154175591/100000000000000 : ℝ)*(major1) + (2075620154175591/100000000000000 : ℝ)*(major2) + (1555663905541277/50000000000000 : ℝ)*(sp0) + (1555673397217077/50000000000000 : ℝ)*(sp1) + (777836699429501/25000000000000 : ℝ)*(sp2) + (1039883732597441/100000000000000 : ℝ)*(sp3) + (10485653119/50000000000000 : ℝ)*(sp4) + (7348524619/100000000000000 : ℝ)*(sp7) + (51994554056103/5000000000000 : ℝ)*(f.failure) + (3111348782388793/100000000000000 : ℝ)*(f.sum) + (5982682745531/34450000000000000000000000000 : ℝ)*base65 + (1941053649070969211/3445000000000000000000000000000000 : ℝ)*base67 + (7797879959470969211/3445000000000000000000000000000000 : ℝ)*base69 + (1797818296764030789/3445000000000000000000000000000000 : ℝ)*base72 + (189391437726519/34450000000000000000000000000 : ℝ)*base74 + (9672769348440969211/3445000000000000000000000000000000 : ℝ)*base75 + (17955298763405969211/3445000000000000000000000000000000 : ℝ)*base77 + (4719899311149030789/3445000000000000000000000000000000 : ℝ)*base80 + (80579577358919/34450000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (123159/100000000000000000000 : ℝ)*base89 + (123159/100000000000000000000 : ℝ)*base91 + (123159/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180337765878848776315600353/33125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (735347921/100000000000000 : ℝ)*(base19) + (158199147/20000000000000 : ℝ)*(base23) + (108855401/50000000000000 : ℝ)*(lower1) + (28999217/25000000000000 : ℝ)*(upper3) + (12402549/50000000000000 : ℝ)*(lower4) + (112936961/100000000000000 : ℝ)*(upper5) + (530888070417403/25000000000000 : ℝ)*(major0) + (530888070417403/25000000000000 : ℝ)*(major1) + (530888070417403/25000000000000 : ℝ)*(major2) + (257195433/50000000000000 : ℝ)*(sp2) + (318319918054117/10000000000000 : ℝ)*(sp4) + (12732793780773/400000000000 : ℝ)*(sp5) + (318319787515457/10000000000000 : ℝ)*(sp6) + (106390520132607/10000000000000 : ℝ)*(sp7) + (106390520132607/10000000000000 : ℝ)*(f.failure) + (318319918054117/10000000000000 : ℝ)*(f.sum) + (16467550479901/4306250000000000000000000000 : ℝ)*base66 + (6915702733157484863/861250000000000000000000000000000 : ℝ)*base67 + (4630937062767515137/861250000000000000000000000000000 : ℝ)*base70 + (81474646236844984863/861250000000000000000000000000000 : ℝ)*base71 + (990428748319/1076562500000000000000000000 : ℝ)*base74 + (22436948878405015137/861250000000000000000000000000000 : ℝ)*base76 + (9374138817325015137/861250000000000000000000000000000 : ℝ)*base78 + (6106265728130015137/861250000000000000000000000000000 : ℝ)*base80 + (4674793935827/8612500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1207471/200000000000000000000 : ℝ)*base89 + (1207471/200000000000000000000 : ℝ)*base91 + (1207471/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1724_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (531/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1724_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1724_s4_0 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-681530989/5000000000 : ℝ)*x 0 + (1365306519/2500000000 : ℝ)*x 1 + (1027966967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681530989/5000000000 : ℝ)^5415 ≤ (4282042180631/50000000000000 : ℝ)^4391 := by
    have hnat : (681530989 : ℕ)^5415*50000000000000^4391 ≤ 4282042180631^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681530989 5000000000 4282042180631 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365306519/2500000000 : ℝ)^5415 ≤ (9485387778629/20000000000000 : ℝ)^4391 := by
    have hnat : (1365306519 : ℕ)^5415*20000000000000^4391 ≤ 9485387778629^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365306519 2500000000 9485387778629 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027966967/2000000000 : ℝ)^5415 ≤ (1760359069587/4000000000000 : ℝ)^4391 := by
    have hnat : (1027966967 : ℕ)^5415*4000000000000^4391 ≤ 1760359069587^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027966967 2000000000 1760359069587 4000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-681530989/5000000000 : ℝ), (1365306519/2500000000 : ℝ), (1027966967/2000000000 : ℝ)] ![(4282042180631/50000000000000 : ℝ), (9485387778629/20000000000000 : ℝ), (1760359069587/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-681530989/5000000000 : ℝ)|^5415 ≤ (4282042180631/50000000000000 : ℝ)^4391
        have hw : |(-681530989/5000000000 : ℝ)|=(681530989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365306519/2500000000 : ℝ)|^5415 ≤ (9485387778629/20000000000000 : ℝ)^4391
        have hw : |(1365306519/2500000000 : ℝ)|=(1365306519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027966967/2000000000 : ℝ)|^5415 ≤ (1760359069587/4000000000000 : ℝ)^4391
        have hw : |(1027966967/2000000000 : ℝ)|=(1027966967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s4_1 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5338806761/10000000000 : ℝ)*x 0 + (-1529524429/10000000000 : ℝ)*x 1 + (5139834863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5338806761/10000000000 : ℝ)^5415 ≤ (720614586423/1562500000000 : ℝ)^4391 := by
    have hnat : (5338806761 : ℕ)^5415*1562500000000^4391 ≤ 720614586423^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338806761 10000000000 720614586423 1562500000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529524429/10000000000 : ℝ)^5415 ≤ (9871689415777/100000000000000 : ℝ)^4391 := by
    have hnat : (1529524429 : ℕ)^5415*100000000000000^4391 ≤ 9871689415777^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529524429 10000000000 9871689415777 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139834863/10000000000 : ℝ)^5415 ≤ (4400897703533/10000000000000 : ℝ)^4391 := by
    have hnat : (5139834863 : ℕ)^5415*10000000000000^4391 ≤ 4400897703533^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139834863 10000000000 4400897703533 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5338806761/10000000000 : ℝ), (-1529524429/10000000000 : ℝ), (5139834863/10000000000 : ℝ)] ![(720614586423/1562500000000 : ℝ), (9871689415777/100000000000000 : ℝ), (4400897703533/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5338806761/10000000000 : ℝ)|^5415 ≤ (720614586423/1562500000000 : ℝ)^4391
        have hw : |(5338806761/10000000000 : ℝ)|=(5338806761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1529524429/10000000000 : ℝ)|^5415 ≤ (9871689415777/100000000000000 : ℝ)^4391
        have hw : |(-1529524429/10000000000 : ℝ)|=(1529524429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139834863/10000000000 : ℝ)|^5415 ≤ (4400897703533/10000000000000 : ℝ)^4391
        have hw : |(5139834863/10000000000 : ℝ)|=(5139834863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s4_2 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334701697/2500000000 : ℝ)*x 0 + (1027966899/2000000000 : ℝ)*x 1 + (-764762441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334701697/2500000000 : ℝ)^5415 ≤ (2882458363669/6250000000000 : ℝ)^4391 := by
    have hnat : (1334701697 : ℕ)^5415*6250000000000^4391 ≤ 2882458363669^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334701697 2500000000 2882458363669 6250000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027966899/2000000000 : ℝ)^5415 ≤ (44008973149579/100000000000000 : ℝ)^4391 := by
    have hnat : (1027966899 : ℕ)^5415*100000000000000^4391 ≤ 44008973149579^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027966899 2000000000 44008973149579 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764762441/5000000000 : ℝ)^5415 ≤ (98716930213/1000000000000 : ℝ)^4391 := by
    have hnat : (764762441 : ℕ)^5415*1000000000000^4391 ≤ 98716930213^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764762441 5000000000 98716930213 1000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334701697/2500000000 : ℝ), (1027966899/2000000000 : ℝ), (-764762441/5000000000 : ℝ)] ![(2882458363669/6250000000000 : ℝ), (44008973149579/100000000000000 : ℝ), (98716930213/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334701697/2500000000 : ℝ)|^5415 ≤ (2882458363669/6250000000000 : ℝ)^4391
        have hw : |(1334701697/2500000000 : ℝ)|=(1334701697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027966899/2000000000 : ℝ)|^5415 ≤ (44008973149579/100000000000000 : ℝ)^4391
        have hw : |(1027966899/2000000000 : ℝ)|=(1027966899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764762441/5000000000 : ℝ)|^5415 ≤ (98716930213/1000000000000 : ℝ)^4391
        have hw : |(-764762441/5000000000 : ℝ)|=(764762441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s4_3 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043568251/5000000000 : ℝ)*x 0 + (3623590521/10000000000 : ℝ)*x 1 + (1146298141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043568251/5000000000 : ℝ)^5415 ≤ (8293549316967/25000000000000 : ℝ)^4391 := by
    have hnat : (2043568251 : ℕ)^5415*25000000000000^4391 ≤ 8293549316967^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043568251 5000000000 8293549316967 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3623590521/10000000000 : ℝ)^5415 ≤ (28597526359237/100000000000000 : ℝ)^4391 := by
    have hnat : (3623590521 : ℕ)^5415*100000000000000^4391 ≤ 28597526359237^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623590521 10000000000 28597526359237 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146298141/2500000000 : ℝ)^5415 ≤ (4778534546107/12500000000000 : ℝ)^4391 := by
    have hnat : (1146298141 : ℕ)^5415*12500000000000^4391 ≤ 4778534546107^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146298141 2500000000 4778534546107 12500000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043568251/5000000000 : ℝ), (3623590521/10000000000 : ℝ), (1146298141/2500000000 : ℝ)] ![(8293549316967/25000000000000 : ℝ), (28597526359237/100000000000000 : ℝ), (4778534546107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043568251/5000000000 : ℝ)|^5415 ≤ (8293549316967/25000000000000 : ℝ)^4391
        have hw : |(2043568251/5000000000 : ℝ)|=(2043568251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3623590521/10000000000 : ℝ)|^5415 ≤ (28597526359237/100000000000000 : ℝ)^4391
        have hw : |(3623590521/10000000000 : ℝ)|=(3623590521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146298141/2500000000 : ℝ)|^5415 ≤ (4778534546107/12500000000000 : ℝ)^4391
        have hw : |(1146298141/2500000000 : ℝ)|=(1146298141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s4_4 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1363205359/10000000000 : ℝ)*x 0 + (5143437237/10000000000 : ℝ)*x 1 + (2728784979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363205359/10000000000 : ℝ)^5415 ≤ (4282597659181/50000000000000 : ℝ)^4391 := by
    have hnat : (1363205359 : ℕ)^5415*50000000000000^4391 ≤ 4282597659181^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363205359 10000000000 4282597659181 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143437237/10000000000 : ℝ)^5415 ≤ (44047017990703/100000000000000 : ℝ)^4391 := by
    have hnat : (5143437237 : ℕ)^5415*100000000000000^4391 ≤ 44047017990703^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143437237 10000000000 44047017990703 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728784979/5000000000 : ℝ)^5415 ≤ (23693893342607/50000000000000 : ℝ)^4391 := by
    have hnat : (2728784979 : ℕ)^5415*50000000000000^4391 ≤ 23693893342607^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728784979 5000000000 23693893342607 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1363205359/10000000000 : ℝ), (5143437237/10000000000 : ℝ), (2728784979/5000000000 : ℝ)] ![(4282597659181/50000000000000 : ℝ), (44047017990703/100000000000000 : ℝ), (23693893342607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1363205359/10000000000 : ℝ)|^5415 ≤ (4282597659181/50000000000000 : ℝ)^4391
        have hw : |(-1363205359/10000000000 : ℝ)|=(1363205359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143437237/10000000000 : ℝ)|^5415 ≤ (44047017990703/100000000000000 : ℝ)^4391
        have hw : |(5143437237/10000000000 : ℝ)|=(5143437237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728784979/5000000000 : ℝ)|^5415 ≤ (23693893342607/50000000000000 : ℝ)^4391
        have hw : |(2728784979/5000000000 : ℝ)|=(2728784979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s4_5 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626389203/5000000000 : ℝ)*x 0 + (5457569891/10000000000 : ℝ)*x 1 + (-75736837/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626389203/5000000000 : ℝ)^5415 ≤ (1412643703341/3125000000000 : ℝ)^4391 := by
    have hnat : (2626389203 : ℕ)^5415*3125000000000^4391 ≤ 1412643703341^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626389203 5000000000 1412643703341 3125000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457569891/10000000000 : ℝ)^5415 ≤ (47387785967789/100000000000000 : ℝ)^4391 := by
    have hnat : (5457569891 : ℕ)^5415*100000000000000^4391 ≤ 47387785967789^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457569891 10000000000 47387785967789 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75736837/625000000 : ℝ)^5415 ≤ (7407615514549/100000000000000 : ℝ)^4391 := by
    have hnat : (75736837 : ℕ)^5415*100000000000000^4391 ≤ 7407615514549^4391*625000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75736837 625000000 7407615514549 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626389203/5000000000 : ℝ), (5457569891/10000000000 : ℝ), (-75736837/625000000 : ℝ)] ![(1412643703341/3125000000000 : ℝ), (47387785967789/100000000000000 : ℝ), (7407615514549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626389203/5000000000 : ℝ)|^5415 ≤ (1412643703341/3125000000000 : ℝ)^4391
        have hw : |(2626389203/5000000000 : ℝ)|=(2626389203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457569891/10000000000 : ℝ)|^5415 ≤ (47387785967789/100000000000000 : ℝ)^4391
        have hw : |(5457569891/10000000000 : ℝ)|=(5457569891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75736837/625000000 : ℝ)|^5415 ≤ (7407615514549/100000000000000 : ℝ)^4391
        have hw : |(-75736837/625000000 : ℝ)|=(75736837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_s4_6 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043782923/5000000000 : ℝ)*x 0 + (2287206623/5000000000 : ℝ)*x 1 + (3634529493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043782923/5000000000 : ℝ)^5415 ≤ (33178494878067/100000000000000 : ℝ)^4391 := by
    have hnat : (2043782923 : ℕ)^5415*100000000000000^4391 ≤ 33178494878067^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043782923 5000000000 33178494878067 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287206623/5000000000 : ℝ)^5415 ≤ (38117477759621/100000000000000 : ℝ)^4391 := by
    have hnat : (2287206623 : ℕ)^5415*100000000000000^4391 ≤ 38117477759621^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287206623 5000000000 38117477759621 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3634529493/10000000000 : ℝ)^5415 ≤ (28704027342171/100000000000000 : ℝ)^4391 := by
    have hnat : (3634529493 : ℕ)^5415*100000000000000^4391 ≤ 28704027342171^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634529493 10000000000 28704027342171 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043782923/5000000000 : ℝ), (2287206623/5000000000 : ℝ), (3634529493/10000000000 : ℝ)] ![(33178494878067/100000000000000 : ℝ), (38117477759621/100000000000000 : ℝ), (28704027342171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043782923/5000000000 : ℝ)|^5415 ≤ (33178494878067/100000000000000 : ℝ)^4391
        have hw : |(2043782923/5000000000 : ℝ)|=(2043782923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2287206623/5000000000 : ℝ)|^5415 ≤ (38117477759621/100000000000000 : ℝ)^4391
        have hw : |(2287206623/5000000000 : ℝ)|=(2287206623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3634529493/10000000000 : ℝ)|^5415 ≤ (28704027342171/100000000000000 : ℝ)^4391
        have hw : |(3634529493/10000000000 : ℝ)|=(3634529493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1724_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2023/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (531/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (531/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5057/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (531/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5057/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (531/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5057/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (531/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5057/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (531/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5057/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (531/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5057/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5057/50000 : ℝ) ^ (5407/1024 : ℝ) ≤ (139207004913767/25000000000000000000 : ℝ) := by
    have hpowers : (5057/50000 : ℝ)^5407 ≤ (139207004913767/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5057 : ℕ)^5407*25000000000000000000^1024 ≤ 139207004913767^1024*50000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5057 50000 139207004913767 25000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5057/50000 : ℝ)) (X := (139207004913767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (531/3125 : ℝ) ^ (5407/1024 : ℝ) ≤ (4309734150314969/50000000000000000000 : ℝ) := by
    have hpowers : (531/3125 : ℝ)^5407 ≤ (4309734150314969/50000000000000000000 : ℝ)^1024 := by
      have hnat : (531 : ℕ)^5407*50000000000000000000^1024 ≤ 4309734150314969^1024*3125^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        531 3125 4309734150314969 50000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (531/3125 : ℝ)) (X := (4309734150314969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500139207004913767/12500000000000000000 : ℝ) ≤ (5000010545391501/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (12500139207004913767/12500000000000000000 : ℝ)^1024 ≤ (5000010545391501/5000000000000000 : ℝ)^5407 := by
      have hnat : (12500139207004913767 : ℕ)^1024*5000000000000000^5407 ≤ 5000010545391501^5407*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500139207004913767 12500000000000000000 5000010545391501 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010545391501/5000000000000000 : ℝ)) (X := (12500139207004913767/12500000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004588148160142503/50000000000000000000 : ℝ) ≤ (2500043444506997/2500000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (50004588148160142503/50000000000000000000 : ℝ)^1024 ≤ (2500043444506997/2500000000000000 : ℝ)^5407 := by
      have hnat : (50004588148160142503 : ℕ)^1024*2500000000000000^5407 ≤ 2500043444506997^5407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004588148160142503 50000000000000000000 2500043444506997 2500000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500043444506997/2500000000000000 : ℝ)) (X := (50004588148160142503/50000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004309734150314969/25000000000000000000 : ℝ) ≤ (5000163232636487/5000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (25004309734150314969/25000000000000000000 : ℝ)^1024 ≤ (5000163232636487/5000000000000000 : ℝ)^5407 := by
      have hnat : (25004309734150314969 : ℕ)^1024*5000000000000000^5407 ≤ 5000163232636487^5407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004309734150314969 25000000000000000000 5000163232636487 5000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000163232636487/5000000000000000 : ℝ)) (X := (25004309734150314969/25000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(139207004913767/25000000000000000000 : ℝ) ≤ ((17194264126203477737/17195000000000000000 : ℝ)+2*(76343622493/343900000000000 : ℝ)*(5057/50000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (17194264126203477737/17195000000000000000 : ℝ)+2*(76343622493/343900000000000 : ℝ)*(5057/50000 : ℝ)=(5000010545391501/5000000000000000 : ℝ) by norm_num, show 1+2*(139207004913767/25000000000000000000 : ℝ)=(12500139207004913767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4309734150314969/50000000000000000000 : ℝ)+(139207004913767/25000000000000000000 : ℝ) ≤ ((17194264126203477737/17195000000000000000 : ℝ)+(76343622493/343900000000000 : ℝ)*((531/3125 : ℝ)+(5057/50000 : ℝ)))^(5407/1024 : ℝ) := by
    rw [show (17194264126203477737/17195000000000000000 : ℝ)+(76343622493/343900000000000 : ℝ)*((531/3125 : ℝ)+(5057/50000 : ℝ))=(2500043444506997/2500000000000000 : ℝ) by norm_num, show 1+(4309734150314969/50000000000000000000 : ℝ)+(139207004913767/25000000000000000000 : ℝ)=(50004588148160142503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4309734150314969/50000000000000000000 : ℝ) ≤ ((17194264126203477737/17195000000000000000 : ℝ)+2*(76343622493/343900000000000 : ℝ)*(531/3125 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (17194264126203477737/17195000000000000000 : ℝ)+2*(76343622493/343900000000000 : ℝ)*(531/3125 : ℝ)=(5000163232636487/5000000000000000 : ℝ) by norm_num, show 1+2*(4309734150314969/50000000000000000000 : ℝ)=(25004309734150314969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17194264126203477737/17195000000000000000 : ℝ)*(X 1 0+X 2 0)+(76343622493/343900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (5057/50000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (17194264126203477737/17195000000000000000 : ℝ)) (alpha := (76343622493/343900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17194264126203477737/17195000000000000000 : ℝ)*(X 0 1+X 2 1)+(76343622493/343900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (5057/50000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (17194264126203477737/17195000000000000000 : ℝ)) (alpha := (76343622493/343900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17194264126203477737/17195000000000000000 : ℝ)*(X 0 2+X 1 2)+(76343622493/343900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (5057/50000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (17194264126203477737/17195000000000000000 : ℝ)) (alpha := (76343622493/343900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-681530989/5000000000 : ℝ)*X 0 0+(1365306519/2500000000 : ℝ)*X 0 1+(1027966967/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5338806761/10000000000 : ℝ)*X 1 0+(-1529524429/10000000000 : ℝ)*X 1 1+(5139834863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1334701697/2500000000 : ℝ)*X 2 0+(1027966899/2000000000 : ℝ)*X 2 1+(-764762441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2043568251/5000000000 : ℝ)*X 0 0+(3623590521/10000000000 : ℝ)*X 0 1+(1146298141/2500000000 : ℝ)*X 0 2+(2043568251/5000000000 : ℝ)*X 1 0+(3623590521/10000000000 : ℝ)*X 1 1+(1146298141/2500000000 : ℝ)*X 1 2+(2043568251/5000000000 : ℝ)*X 2 0+(3623590521/10000000000 : ℝ)*X 2 1+(1146298141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1363205359/10000000000 : ℝ)*X 0 0+(5143437237/10000000000 : ℝ)*X 0 1+(2728784979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626389203/5000000000 : ℝ)*X 2 0+(5457569891/10000000000 : ℝ)*X 2 1+(-75736837/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2043782923/5000000000 : ℝ)*X 0 0+(2287206623/5000000000 : ℝ)*X 0 1+(3634529493/10000000000 : ℝ)*X 0 2+(2043782923/5000000000 : ℝ)*X 1 0+(2287206623/5000000000 : ℝ)*X 1 1+(3634529493/10000000000 : ℝ)*X 1 2+(2043782923/5000000000 : ℝ)*X 2 0+(2287206623/5000000000 : ℝ)*X 2 1+(3634529493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (766340586812205885894022851/171950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140299487/50000000000000 : ℝ)*(base19) + (156343533/50000000000000 : ℝ)*(base23) + (16193133/50000000000000 : ℝ)*(upper2) + (7916183/10000000000000 : ℝ)*(upper3) + (415141322809747/20000000000000 : ℝ)*(major0) + (415141322809747/20000000000000 : ℝ)*(major1) + (415141322809747/20000000000000 : ℝ)*(major2) + (77786915173039/2500000000000 : ℝ)*(sp0) + (777869600299229/25000000000000 : ℝ)*(sp1) + (124459024772531/4000000000000 : ℝ)*(sp2) + (1039932637876257/100000000000000 : ℝ)*(sp3) + (2074874331/100000000000000 : ℝ)*(sp4) + (54995911/2000000000000 : ℝ)*(sp5) + (879933257/50000000000000 : ℝ)*(sp6) + (1039934397742771/100000000000000 : ℝ)*(f.failure) + (3111478681795891/100000000000000 : ℝ)*(f.sum) + (214730927647/171950000000000000000000000 : ℝ)*base66 + (1888543359312547461/343900000000000000000000000000000 : ℝ)*base68 + (1424372828642547461/343900000000000000000000000000000 : ℝ)*base70 + (1632886925237947461/343900000000000000000000000000000 : ℝ)*base72 + (903947029279/429875000000000000000000000 : ℝ)*base74 + (768690272101547461/343900000000000000000000000000000 : ℝ)*base76 + (529055593601547461/343900000000000000000000000000000 : ℝ)*base78 + (1002225078687747461/343900000000000000000000000000000 : ℝ)*base80 + (1358771252529/3439000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (24409763/2000000000000000000000 : ℝ)*base89 + (24409763/2000000000000000000000 : ℝ)*base91 + (24409763/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1724_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2023/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (531/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1724_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1724_box_0 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-263727311/2500000000 : ℝ)*x 0 + (676242299/1250000000 : ℝ)*x 1 + (2704969133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263727311/2500000000 : ℝ)^5415 ≤ (1560862639071/25000000000000 : ℝ)^4391 := by
    have hnat : (263727311 : ℕ)^5415*25000000000000^4391 ≤ 1560862639071^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263727311 2500000000 1560862639071 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676242299/1250000000 : ℝ)^5415 ≤ (4687827538767/10000000000000 : ℝ)^4391 := by
    have hnat : (676242299 : ℕ)^5415*10000000000000^4391 ≤ 4687827538767^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676242299 1250000000 4687827538767 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704969133/5000000000 : ℝ)^5415 ≤ (46878274041237/100000000000000 : ℝ)^4391 := by
    have hnat : (2704969133 : ℕ)^5415*100000000000000^4391 ≤ 46878274041237^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704969133 5000000000 46878274041237 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263727311/2500000000 : ℝ), (676242299/1250000000 : ℝ), (2704969133/5000000000 : ℝ)] ![(1560862639071/25000000000000 : ℝ), (4687827538767/10000000000000 : ℝ), (46878274041237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263727311/2500000000 : ℝ)|^5415 ≤ (1560862639071/25000000000000 : ℝ)^4391
        have hw : |(-263727311/2500000000 : ℝ)|=(263727311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676242299/1250000000 : ℝ)|^5415 ≤ (4687827538767/10000000000000 : ℝ)^4391
        have hw : |(676242299/1250000000 : ℝ)|=(676242299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704969133/5000000000 : ℝ)|^5415 ≤ (46878274041237/100000000000000 : ℝ)^4391
        have hw : |(2704969133/5000000000 : ℝ)|=(2704969133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_1 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224595241/10000000000 : ℝ)*x 0 + (-263593421/2000000000 : ℝ)*x 1 + (1352484597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224595241/10000000000 : ℝ)^5415 ≤ (44905684570737/100000000000000 : ℝ)^4391 := by
    have hnat : (5224595241 : ℕ)^5415*100000000000000^4391 ≤ 44905684570737^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224595241 10000000000 44905684570737 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263593421/2000000000 : ℝ)^5415 ≤ (4108020035287/50000000000000 : ℝ)^4391 := by
    have hnat : (263593421 : ℕ)^5415*50000000000000^4391 ≤ 4108020035287^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263593421 2000000000 4108020035287 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352484597/2500000000 : ℝ)^5415 ≤ (23439137672463/50000000000000 : ℝ)^4391 := by
    have hnat : (1352484597 : ℕ)^5415*50000000000000^4391 ≤ 23439137672463^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352484597 2500000000 23439137672463 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224595241/10000000000 : ℝ), (-263593421/2000000000 : ℝ), (1352484597/2500000000 : ℝ)] ![(44905684570737/100000000000000 : ℝ), (4108020035287/50000000000000 : ℝ), (23439137672463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224595241/10000000000 : ℝ)|^5415 ≤ (44905684570737/100000000000000 : ℝ)^4391
        have hw : |(5224595241/10000000000 : ℝ)|=(5224595241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263593421/2000000000 : ℝ)|^5415 ≤ (4108020035287/50000000000000 : ℝ)^4391
        have hw : |(-263593421/2000000000 : ℝ)|=(263593421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352484597/2500000000 : ℝ)|^5415 ≤ (23439137672463/50000000000000 : ℝ)^4391
        have hw : |(1352484597/2500000000 : ℝ)|=(1352484597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_2 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044919069/2000000000 : ℝ)*x 0 + (5409938253/10000000000 : ℝ)*x 1 + (-1317967149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044919069/2000000000 : ℝ)^5415 ≤ (44905685673081/100000000000000 : ℝ)^4391 := by
    have hnat : (1044919069 : ℕ)^5415*100000000000000^4391 ≤ 44905685673081^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044919069 2000000000 44905685673081 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409938253/10000000000 : ℝ)^5415 ≤ (46878273902319/100000000000000 : ℝ)^4391 := by
    have hnat : (5409938253 : ℕ)^5415*100000000000000^4391 ≤ 46878273902319^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409938253 10000000000 46878273902319 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317967149/10000000000 : ℝ)^5415 ≤ (821604040883/10000000000000 : ℝ)^4391 := by
    have hnat : (1317967149 : ℕ)^5415*10000000000000^4391 ≤ 821604040883^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317967149 10000000000 821604040883 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044919069/2000000000 : ℝ), (5409938253/10000000000 : ℝ), (-1317967149/10000000000 : ℝ)] ![(44905685673081/100000000000000 : ℝ), (46878273902319/100000000000000 : ℝ), (821604040883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044919069/2000000000 : ℝ)|^5415 ≤ (44905685673081/100000000000000 : ℝ)^4391
        have hw : |(1044919069/2000000000 : ℝ)|=(1044919069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409938253/10000000000 : ℝ)|^5415 ≤ (46878273902319/100000000000000 : ℝ)^4391
        have hw : |(5409938253/10000000000 : ℝ)|=(5409938253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1317967149/10000000000 : ℝ)|^5415 ≤ (821604040883/10000000000000 : ℝ)^4391
        have hw : |(-1317967149/10000000000 : ℝ)|=(1317967149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_3 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4467618863/10000000000 : ℝ)*x 0 + (979474789/2500000000 : ℝ)*x 1 + (3917899093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4467618863/10000000000 : ℝ)^5415 ≤ (18511532434501/50000000000000 : ℝ)^4391 := by
    have hnat : (4467618863 : ℕ)^5415*50000000000000^4391 ≤ 18511532434501^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467618863 10000000000 18511532434501 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979474789/2500000000 : ℝ)^5415 ≤ (31488467867713/100000000000000 : ℝ)^4391 := by
    have hnat : (979474789 : ℕ)^5415*100000000000000^4391 ≤ 31488467867713^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979474789 2500000000 31488467867713 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3917899093/10000000000 : ℝ)^5415 ≤ (31488467243297/100000000000000 : ℝ)^4391 := by
    have hnat : (3917899093 : ℕ)^5415*100000000000000^4391 ≤ 31488467243297^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3917899093 10000000000 31488467243297 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4467618863/10000000000 : ℝ), (979474789/2500000000 : ℝ), (3917899093/10000000000 : ℝ)] ![(18511532434501/50000000000000 : ℝ), (31488467867713/100000000000000 : ℝ), (31488467243297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4467618863/10000000000 : ℝ)|^5415 ≤ (18511532434501/50000000000000 : ℝ)^4391
        have hw : |(4467618863/10000000000 : ℝ)|=(4467618863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(979474789/2500000000 : ℝ)|^5415 ≤ (31488467867713/100000000000000 : ℝ)^4391
        have hw : |(979474789/2500000000 : ℝ)|=(979474789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3917899093/10000000000 : ℝ)|^5415 ≤ (31488467243297/100000000000000 : ℝ)^4391
        have hw : |(3917899093/10000000000 : ℝ)|=(3917899093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_4 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1691619351/10000000000 : ℝ)*x 0 + (1035581121/2000000000 : ℝ)*x 1 + (2588952789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1691619351/10000000000 : ℝ)^5415 ≤ (11177367163667/100000000000000 : ℝ)^4391 := by
    have hnat : (1691619351 : ℕ)^5415*100000000000000^4391 ≤ 11177367163667^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691619351 10000000000 11177367163667 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035581121/2000000000 : ℝ)^5415 ≤ (44411316553843/100000000000000 : ℝ)^4391 := by
    have hnat : (1035581121 : ℕ)^5415*100000000000000^4391 ≤ 44411316553843^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035581121 2000000000 44411316553843 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588952789/5000000000 : ℝ)^5415 ≤ (1387853633383/3125000000000 : ℝ)^4391 := by
    have hnat : (2588952789 : ℕ)^5415*3125000000000^4391 ≤ 1387853633383^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588952789 5000000000 1387853633383 3125000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1691619351/10000000000 : ℝ), (1035581121/2000000000 : ℝ), (2588952789/5000000000 : ℝ)] ![(11177367163667/100000000000000 : ℝ), (44411316553843/100000000000000 : ℝ), (1387853633383/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1691619351/10000000000 : ℝ)|^5415 ≤ (11177367163667/100000000000000 : ℝ)^4391
        have hw : |(-1691619351/10000000000 : ℝ)|=(1691619351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035581121/2000000000 : ℝ)|^5415 ≤ (44411316553843/100000000000000 : ℝ)^4391
        have hw : |(1035581121/2000000000 : ℝ)|=(1035581121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588952789/5000000000 : ℝ)|^5415 ≤ (1387853633383/3125000000000 : ℝ)^4391
        have hw : |(2588952789/5000000000 : ℝ)|=(2588952789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_5 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345359097/2500000000 : ℝ)*x 0 + (-355237013/2500000000 : ℝ)*x 1 + (5177905461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345359097/2500000000 : ℝ)^5415 ≤ (46573890916553/100000000000000 : ℝ)^4391 := by
    have hnat : (1345359097 : ℕ)^5415*100000000000000^4391 ≤ 46573890916553^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345359097 2500000000 46573890916553 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355237013/2500000000 : ℝ)^5415 ≤ (2253698511719/25000000000000 : ℝ)^4391 := by
    have hnat : (355237013 : ℕ)^5415*25000000000000^4391 ≤ 2253698511719^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355237013 2500000000 2253698511719 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177905461/10000000000 : ℝ)^5415 ≤ (5551414378839/12500000000000 : ℝ)^4391 := by
    have hnat : (5177905461 : ℕ)^5415*12500000000000^4391 ≤ 5551414378839^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177905461 10000000000 5551414378839 12500000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345359097/2500000000 : ℝ), (-355237013/2500000000 : ℝ), (5177905461/10000000000 : ℝ)] ![(46573890916553/100000000000000 : ℝ), (2253698511719/25000000000000 : ℝ), (5551414378839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345359097/2500000000 : ℝ)|^5415 ≤ (46573890916553/100000000000000 : ℝ)^4391
        have hw : |(1345359097/2500000000 : ℝ)|=(1345359097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355237013/2500000000 : ℝ)|^5415 ≤ (2253698511719/25000000000000 : ℝ)^4391
        have hw : |(-355237013/2500000000 : ℝ)|=(355237013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177905461/10000000000 : ℝ)|^5415 ≤ (5551414378839/12500000000000 : ℝ)^4391
        have hw : |(5177905461/10000000000 : ℝ)|=(5177905461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_6 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690718091/5000000000 : ℝ)*x 0 + (5177905661/10000000000 : ℝ)*x 1 + (-1420948061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690718091/5000000000 : ℝ)^5415 ≤ (46573888717951/100000000000000 : ℝ)^4391 := by
    have hnat : (2690718091 : ℕ)^5415*100000000000000^4391 ≤ 46573888717951^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690718091 5000000000 46573888717951 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177905661/10000000000 : ℝ)^5415 ≤ (44411317146171/100000000000000 : ℝ)^4391 := by
    have hnat : (5177905661 : ℕ)^5415*100000000000000^4391 ≤ 44411317146171^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177905661 10000000000 44411317146171 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1420948061/10000000000 : ℝ)^5415 ≤ (901479411729/10000000000000 : ℝ)^4391 := by
    have hnat : (1420948061 : ℕ)^5415*10000000000000^4391 ≤ 901479411729^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420948061 10000000000 901479411729 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690718091/5000000000 : ℝ), (5177905661/10000000000 : ℝ), (-1420948061/10000000000 : ℝ)] ![(46573888717951/100000000000000 : ℝ), (44411317146171/100000000000000 : ℝ), (901479411729/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690718091/5000000000 : ℝ)|^5415 ≤ (46573888717951/100000000000000 : ℝ)^4391
        have hw : |(2690718091/5000000000 : ℝ)|=(2690718091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177905661/10000000000 : ℝ)|^5415 ≤ (44411317146171/100000000000000 : ℝ)^4391
        have hw : |(5177905661/10000000000 : ℝ)|=(5177905661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1420948061/10000000000 : ℝ)|^5415 ≤ (901479411729/10000000000000 : ℝ)^4391
        have hw : |(-1420948061/10000000000 : ℝ)|=(1420948061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_7 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3690288543/10000000000 : ℝ)*x 0 + (4305757749/10000000000 : ℝ)*x 1 + (861151611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3690288543/10000000000 : ℝ)^5415 ≤ (2924805151849/10000000000000 : ℝ)^4391 := by
    have hnat : (3690288543 : ℕ)^5415*10000000000000^4391 ≤ 2924805151849^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690288543 10000000000 2924805151849 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4305757749/10000000000 : ℝ)^5415 ≤ (8843993170441/25000000000000 : ℝ)^4391 := by
    have hnat : (4305757749 : ℕ)^5415*25000000000000^4391 ≤ 8843993170441^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305757749 10000000000 8843993170441 25000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861151611/2000000000 : ℝ)^5415 ≤ (17687987891073/50000000000000 : ℝ)^4391 := by
    have hnat : (861151611 : ℕ)^5415*50000000000000^4391 ≤ 17687987891073^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861151611 2000000000 17687987891073 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3690288543/10000000000 : ℝ), (4305757749/10000000000 : ℝ), (861151611/2000000000 : ℝ)] ![(2924805151849/10000000000000 : ℝ), (8843993170441/25000000000000 : ℝ), (17687987891073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3690288543/10000000000 : ℝ)|^5415 ≤ (2924805151849/10000000000000 : ℝ)^4391
        have hw : |(3690288543/10000000000 : ℝ)|=(3690288543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4305757749/10000000000 : ℝ)|^5415 ≤ (8843993170441/25000000000000 : ℝ)^4391
        have hw : |(4305757749/10000000000 : ℝ)|=(4305757749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(861151611/2000000000 : ℝ)|^5415 ≤ (17687987891073/50000000000000 : ℝ)^4391
        have hw : |(861151611/2000000000 : ℝ)|=(861151611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_8 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1554498869/10000000000 : ℝ)*x 0 + (200238997/400000000 : ℝ)*x 1 + (10648647/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1554498869/10000000000 : ℝ)^5415 ≤ (10070843170503/100000000000000 : ℝ)^4391 := by
    have hnat : (1554498869 : ℕ)^5415*100000000000000^4391 ≤ 10070843170503^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554498869 10000000000 10070843170503 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200238997/400000000 : ℝ)^5415 ≤ (2662491061377/6250000000000 : ℝ)^4391 := by
    have hnat : (200238997 : ℕ)^5415*6250000000000^4391 ≤ 2662491061377^4391*400000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200238997 400000000 2662491061377 6250000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10648647/19531250 : ℝ)^5415 ≤ (47329299824969/100000000000000 : ℝ)^4391 := by
    have hnat : (10648647 : ℕ)^5415*100000000000000^4391 ≤ 47329299824969^4391*19531250^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10648647 19531250 47329299824969 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1554498869/10000000000 : ℝ), (200238997/400000000 : ℝ), (10648647/19531250 : ℝ)] ![(10070843170503/100000000000000 : ℝ), (2662491061377/6250000000000 : ℝ), (47329299824969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1554498869/10000000000 : ℝ)|^5415 ≤ (10070843170503/100000000000000 : ℝ)^4391
        have hw : |(-1554498869/10000000000 : ℝ)|=(1554498869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200238997/400000000 : ℝ)|^5415 ≤ (2662491061377/6250000000000 : ℝ)^4391
        have hw : |(200238997/400000000 : ℝ)|=(200238997/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10648647/19531250 : ℝ)|^5415 ≤ (47329299824969/100000000000000 : ℝ)^4391
        have hw : |(10648647/19531250 : ℝ)|=(10648647/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_9 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598057901/5000000000 : ℝ)*x 0 + (-1298507257/10000000000 : ℝ)*x 1 + (5452106497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598057901/5000000000 : ℝ)^5415 ≤ (4460401006287/10000000000000 : ℝ)^4391 := by
    have hnat : (2598057901 : ℕ)^5415*10000000000000^4391 ≤ 4460401006287^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598057901 5000000000 4460401006287 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298507257/10000000000 : ℝ)^5415 ≤ (4033349156413/50000000000000 : ℝ)^4391 := by
    have hnat : (1298507257 : ℕ)^5415*50000000000000^4391 ≤ 4033349156413^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298507257 10000000000 4033349156413 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452106497/10000000000 : ℝ)^5415 ≤ (47329291613969/100000000000000 : ℝ)^4391 := by
    have hnat : (5452106497 : ℕ)^5415*100000000000000^4391 ≤ 47329291613969^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452106497 10000000000 47329291613969 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598057901/5000000000 : ℝ), (-1298507257/10000000000 : ℝ), (5452106497/10000000000 : ℝ)] ![(4460401006287/10000000000000 : ℝ), (4033349156413/50000000000000 : ℝ), (47329291613969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598057901/5000000000 : ℝ)|^5415 ≤ (4460401006287/10000000000000 : ℝ)^4391
        have hw : |(2598057901/5000000000 : ℝ)|=(2598057901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1298507257/10000000000 : ℝ)|^5415 ≤ (4033349156413/50000000000000 : ℝ)^4391
        have hw : |(-1298507257/10000000000 : ℝ)|=(1298507257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452106497/10000000000 : ℝ)|^5415 ≤ (47329291613969/100000000000000 : ℝ)^4391
        have hw : |(5452106497/10000000000 : ℝ)|=(5452106497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_10 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196115693/10000000000 : ℝ)*x 0 + (5452107069/10000000000 : ℝ)*x 1 + (-81156663/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196115693/10000000000 : ℝ)^5415 ≤ (44604008909/100000000000 : ℝ)^4391 := by
    have hnat : (5196115693 : ℕ)^5415*100000000000^4391 ≤ 44604008909^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196115693 10000000000 44604008909 100000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452107069/10000000000 : ℝ)^5415 ≤ (47329297737427/100000000000000 : ℝ)^4391 := by
    have hnat : (5452107069 : ℕ)^5415*100000000000000^4391 ≤ 47329297737427^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452107069 10000000000 47329297737427 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81156663/625000000 : ℝ)^5415 ≤ (322667733633/4000000000000 : ℝ)^4391 := by
    have hnat : (81156663 : ℕ)^5415*4000000000000^4391 ≤ 322667733633^4391*625000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81156663 625000000 322667733633 4000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196115693/10000000000 : ℝ), (5452107069/10000000000 : ℝ), (-81156663/625000000 : ℝ)] ![(44604008909/100000000000 : ℝ), (47329297737427/100000000000000 : ℝ), (322667733633/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196115693/10000000000 : ℝ)|^5415 ≤ (44604008909/100000000000 : ℝ)^4391
        have hw : |(5196115693/10000000000 : ℝ)|=(5196115693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452107069/10000000000 : ℝ)|^5415 ≤ (47329297737427/100000000000000 : ℝ)^4391
        have hw : |(5452107069/10000000000 : ℝ)|=(5452107069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81156663/625000000 : ℝ)|^5415 ≤ (322667733633/4000000000000 : ℝ)^4391
        have hw : |(-81156663/625000000 : ℝ)|=(81156663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_11 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (920786447/2000000000 : ℝ)*x 0 + (961806441/2500000000 : ℝ)*x 1 + (961806451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (920786447/2000000000 : ℝ)^5415 ≤ (2401315158791/6250000000000 : ℝ)^4391 := by
    have hnat : (920786447 : ℕ)^5415*6250000000000^4391 ≤ 2401315158791^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920786447 2000000000 2401315158791 6250000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961806441/2500000000 : ℝ)^5415 ≤ (1539473926491/5000000000000 : ℝ)^4391 := by
    have hnat : (961806441 : ℕ)^5415*5000000000000^4391 ≤ 1539473926491^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961806441 2500000000 1539473926491 5000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961806451/2500000000 : ℝ)^5415 ≤ (6157895784919/20000000000000 : ℝ)^4391 := by
    have hnat : (961806451 : ℕ)^5415*20000000000000^4391 ≤ 6157895784919^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961806451 2500000000 6157895784919 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(920786447/2000000000 : ℝ), (961806441/2500000000 : ℝ), (961806451/2500000000 : ℝ)] ![(2401315158791/6250000000000 : ℝ), (1539473926491/5000000000000 : ℝ), (6157895784919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(920786447/2000000000 : ℝ)|^5415 ≤ (2401315158791/6250000000000 : ℝ)^4391
        have hw : |(920786447/2000000000 : ℝ)|=(920786447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(961806441/2500000000 : ℝ)|^5415 ≤ (1539473926491/5000000000000 : ℝ)^4391
        have hw : |(961806441/2500000000 : ℝ)|=(961806441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961806451/2500000000 : ℝ)|^5415 ≤ (6157895784919/20000000000000 : ℝ)^4391
        have hw : |(961806451/2500000000 : ℝ)|=(961806451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_12 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118619887/1000000000 : ℝ)*x 0 + (44591851/80000000 : ℝ)*x 1 + (644117963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118619887/1000000000 : ℝ)^5415 ≤ (1443035675399/20000000000000 : ℝ)^4391 := by
    have hnat : (118619887 : ℕ)^5415*20000000000000^4391 ≤ 1443035675399^4391*1000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118619887 1000000000 1443035675399 20000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44591851/80000000 : ℝ)^5415 ≤ (24318692901131/50000000000000 : ℝ)^4391 := by
    have hnat : (44591851 : ℕ)^5415*50000000000000^4391 ≤ 24318692901131^4391*80000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44591851 80000000 24318692901131 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644117963/1250000000 : ℝ)^5415 ≤ (44147435808051/100000000000000 : ℝ)^4391 := by
    have hnat : (644117963 : ℕ)^5415*100000000000000^4391 ≤ 44147435808051^4391*1250000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644117963 1250000000 44147435808051 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118619887/1000000000 : ℝ), (44591851/80000000 : ℝ), (644117963/1250000000 : ℝ)] ![(1443035675399/20000000000000 : ℝ), (24318692901131/50000000000000 : ℝ), (44147435808051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118619887/1000000000 : ℝ)|^5415 ≤ (1443035675399/20000000000000 : ℝ)^4391
        have hw : |(-118619887/1000000000 : ℝ)|=(118619887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44591851/80000000 : ℝ)|^5415 ≤ (24318692901131/50000000000000 : ℝ)^4391
        have hw : |(44591851/80000000 : ℝ)|=(44591851/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644117963/1250000000 : ℝ)|^5415 ≤ (44147435808051/100000000000000 : ℝ)^4391
        have hw : |(644117963/1250000000 : ℝ)|=(644117963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_13 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398341637/10000000000 : ℝ)*x 0 + (-715798407/5000000000 : ℝ)*x 1 + (1288235949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398341637/10000000000 : ℝ)^5415 ≤ (46754383694553/100000000000000 : ℝ)^4391 := by
    have hnat : (5398341637 : ℕ)^5415*100000000000000^4391 ≤ 46754383694553^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398341637 10000000000 46754383694553 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715798407/5000000000 : ℝ)^5415 ≤ (4549089756723/50000000000000 : ℝ)^4391 := by
    have hnat : (715798407 : ℕ)^5415*50000000000000^4391 ≤ 4549089756723^4391*5000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715798407 5000000000 4549089756723 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288235949/2500000000 : ℝ)^5415 ≤ (22073718390033/50000000000000 : ℝ)^4391 := by
    have hnat : (1288235949 : ℕ)^5415*50000000000000^4391 ≤ 22073718390033^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288235949 2500000000 22073718390033 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398341637/10000000000 : ℝ), (-715798407/5000000000 : ℝ), (1288235949/2500000000 : ℝ)] ![(46754383694553/100000000000000 : ℝ), (4549089756723/50000000000000 : ℝ), (22073718390033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398341637/10000000000 : ℝ)|^5415 ≤ (46754383694553/100000000000000 : ℝ)^4391
        have hw : |(5398341637/10000000000 : ℝ)|=(5398341637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715798407/5000000000 : ℝ)|^5415 ≤ (4549089756723/50000000000000 : ℝ)^4391
        have hw : |(-715798407/5000000000 : ℝ)|=(715798407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288235949/2500000000 : ℝ)|^5415 ≤ (22073718390033/50000000000000 : ℝ)^4391
        have hw : |(1288235949/2500000000 : ℝ)|=(1288235949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_14 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215933669/400000000 : ℝ)*x 0 + (5152943687/10000000000 : ℝ)*x 1 + (-1431596841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215933669/400000000 : ℝ)^5415 ≤ (46754384634449/100000000000000 : ℝ)^4391 := by
    have hnat : (215933669 : ℕ)^5415*100000000000000^4391 ≤ 46754384634449^4391*400000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215933669 400000000 46754384634449 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152943687/10000000000 : ℝ)^5415 ≤ (44147435628439/100000000000000 : ℝ)^4391 := by
    have hnat : (5152943687 : ℕ)^5415*100000000000000^4391 ≤ 44147435628439^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152943687 10000000000 44147435628439 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1431596841/10000000000 : ℝ)^5415 ≤ (4549089862527/50000000000000 : ℝ)^4391 := by
    have hnat : (1431596841 : ℕ)^5415*50000000000000^4391 ≤ 4549089862527^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431596841 10000000000 4549089862527 50000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215933669/400000000 : ℝ), (5152943687/10000000000 : ℝ), (-1431596841/10000000000 : ℝ)] ![(46754384634449/100000000000000 : ℝ), (44147435628439/100000000000000 : ℝ), (4549089862527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215933669/400000000 : ℝ)|^5415 ≤ (46754384634449/100000000000000 : ℝ)^4391
        have hw : |(215933669/400000000 : ℝ)|=(215933669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152943687/10000000000 : ℝ)|^5415 ≤ (44147435628439/100000000000000 : ℝ)^4391
        have hw : |(5152943687/10000000000 : ℝ)|=(5152943687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1431596841/10000000000 : ℝ)|^5415 ≤ (4549089862527/50000000000000 : ℝ)^4391
        have hw : |(-1431596841/10000000000 : ℝ)|=(1431596841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1724_box_15 (p : ℝ) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (900920531/2500000000 : ℝ)*x 0 + (4347369519/10000000000 : ℝ)*x 1 + (869473831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900920531/2500000000 : ℝ)^5415 ≤ (2840389220201/10000000000000 : ℝ)^4391 := by
    have hnat : (900920531 : ℕ)^5415*10000000000000^4391 ≤ 2840389220201^4391*2500000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900920531 2500000000 2840389220201 10000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4347369519/10000000000 : ℝ)^5415 ≤ (35798055745191/100000000000000 : ℝ)^4391 := by
    have hnat : (4347369519 : ℕ)^5415*100000000000000^4391 ≤ 35798055745191^4391*10000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347369519 10000000000 35798055745191 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (869473831/2000000000 : ℝ)^5415 ≤ (35798052048873/100000000000000 : ℝ)^4391 := by
    have hnat : (869473831 : ℕ)^5415*100000000000000^4391 ≤ 35798052048873^4391*2000000000^5415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869473831 2000000000 35798052048873 100000000000000 5415 4391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5415/1024 : ℝ)) 5415 4391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(900920531/2500000000 : ℝ), (4347369519/10000000000 : ℝ), (869473831/2000000000 : ℝ)] ![(2840389220201/10000000000000 : ℝ), (35798055745191/100000000000000 : ℝ), (35798052048873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(900920531/2500000000 : ℝ)|^5415 ≤ (2840389220201/10000000000000 : ℝ)^4391
        have hw : |(900920531/2500000000 : ℝ)|=(900920531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4347369519/10000000000 : ℝ)|^5415 ≤ (35798055745191/100000000000000 : ℝ)^4391
        have hw : |(4347369519/10000000000 : ℝ)|=(4347369519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(869473831/2000000000 : ℝ)|^5415 ≤ (35798052048873/100000000000000 : ℝ)^4391
        have hw : |(869473831/2000000000 : ℝ)|=(869473831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1724_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2023/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(33441/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58729/100000 : ℝ) ∧ (20481/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90619/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (531/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2023/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (531/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2023/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (531/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2023/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (531/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2023/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (531/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2023/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (531/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2023/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2023/20000 : ℝ) ^ (5407/1024 : ℝ) ≤ (34819924221447/6250000000000000000 : ℝ) := by
    have hpowers : (2023/20000 : ℝ)^5407 ≤ (34819924221447/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2023 : ℕ)^5407*6250000000000000000^1024 ≤ 34819924221447^1024*20000^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2023 20000 34819924221447 6250000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2023/20000 : ℝ)) (X := (34819924221447/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (531/3125 : ℝ) ^ (5407/1024 : ℝ) ≤ (4309734150314969/50000000000000000000 : ℝ) := by
    have hpowers : (531/3125 : ℝ)^5407 ≤ (4309734150314969/50000000000000000000 : ℝ)^1024 := by
      have hnat : (531 : ℕ)^5407*50000000000000000000^1024 ≤ 4309734150314969^1024*3125^5407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        531 3125 4309734150314969 50000000000000000000 5407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (531/3125 : ℝ)) (X := (4309734150314969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125034819924221447/3125000000000000000 : ℝ) ≤ (10000021101796267/10000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (3125034819924221447/3125000000000000000 : ℝ)^1024 ≤ (10000021101796267/10000000000000000 : ℝ)^5407 := by
      have hnat : (3125034819924221447 : ℕ)^1024*10000000000000000^5407 ≤ 10000021101796267^5407*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125034819924221447 3125000000000000000 10000021101796267 10000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000021101796267/10000000000000000 : ℝ)) (X := (3125034819924221447/3125000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000917658708817309/10000000000000000000 : ℝ) ≤ (500008689176713/500000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (10000917658708817309/10000000000000000000 : ℝ)^1024 ≤ (500008689176713/500000000000000 : ℝ)^5407 := by
      have hnat : (10000917658708817309 : ℕ)^1024*500000000000000^5407 ≤ 500008689176713^5407*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000917658708817309 10000000000000000000 500008689176713 500000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500008689176713/500000000000000 : ℝ)) (X := (10000917658708817309/10000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004309734150314969/25000000000000000000 : ℝ) ≤ (10000326465272253/10000000000000000 : ℝ) ^ (5407/1024 : ℝ) := by
    have hpowers : (25004309734150314969/25000000000000000000 : ℝ)^1024 ≤ (10000326465272253/10000000000000000 : ℝ)^5407 := by
      have hnat : (25004309734150314969 : ℕ)^1024*10000000000000000^5407 ≤ 10000326465272253^5407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004309734150314969 25000000000000000000 10000326465272253 10000000000000000 1024 5407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000326465272253/10000000000000000 : ℝ)) (X := (25004309734150314969/25000000000000000000 : ℝ)) (by norm_num) 5407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(34819924221447/6250000000000000000 : ℝ) ≤ ((68767056365493329769/68770000000000000000 : ℝ)+2*(152681737993/687700000000000 : ℝ)*(2023/20000 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (68767056365493329769/68770000000000000000 : ℝ)+2*(152681737993/687700000000000 : ℝ)*(2023/20000 : ℝ)=(10000021101796267/10000000000000000 : ℝ) by norm_num, show 1+2*(34819924221447/6250000000000000000 : ℝ)=(3125034819924221447/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4309734150314969/50000000000000000000 : ℝ)+(34819924221447/6250000000000000000 : ℝ) ≤ ((68767056365493329769/68770000000000000000 : ℝ)+(152681737993/687700000000000 : ℝ)*((531/3125 : ℝ)+(2023/20000 : ℝ)))^(5407/1024 : ℝ) := by
    rw [show (68767056365493329769/68770000000000000000 : ℝ)+(152681737993/687700000000000 : ℝ)*((531/3125 : ℝ)+(2023/20000 : ℝ))=(500008689176713/500000000000000 : ℝ) by norm_num, show 1+(4309734150314969/50000000000000000000 : ℝ)+(34819924221447/6250000000000000000 : ℝ)=(10000917658708817309/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4309734150314969/50000000000000000000 : ℝ) ≤ ((68767056365493329769/68770000000000000000 : ℝ)+2*(152681737993/687700000000000 : ℝ)*(531/3125 : ℝ))^(5407/1024 : ℝ) := by
    rw [show (68767056365493329769/68770000000000000000 : ℝ)+2*(152681737993/687700000000000 : ℝ)*(531/3125 : ℝ)=(10000326465272253/10000000000000000 : ℝ) by norm_num, show 1+2*(4309734150314969/50000000000000000000 : ℝ)=(25004309734150314969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68767056365493329769/68770000000000000000 : ℝ)*(X 1 0+X 2 0)+(152681737993/687700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (2023/20000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (68767056365493329769/68770000000000000000 : ℝ)) (alpha := (152681737993/687700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68767056365493329769/68770000000000000000 : ℝ)*(X 0 1+X 2 1)+(152681737993/687700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (2023/20000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (68767056365493329769/68770000000000000000 : ℝ)) (alpha := (152681737993/687700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68767056365493329769/68770000000000000000 : ℝ)*(X 0 2+X 1 2)+(152681737993/687700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5407/1024 : ℝ)) (lo := (2023/20000 : ℝ)) (hi := (531/3125 : ℝ)) (c := (68767056365493329769/68770000000000000000 : ℝ)) (alpha := (152681737993/687700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263727311/2500000000 : ℝ)*X 0 0+(676242299/1250000000 : ℝ)*X 0 1+(2704969133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5224595241/10000000000 : ℝ)*X 1 0+(-263593421/2000000000 : ℝ)*X 1 1+(1352484597/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1044919069/2000000000 : ℝ)*X 2 0+(5409938253/10000000000 : ℝ)*X 2 1+(-1317967149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4467618863/10000000000 : ℝ)*X 0 0+(979474789/2500000000 : ℝ)*X 0 1+(3917899093/10000000000 : ℝ)*X 0 2+(4467618863/10000000000 : ℝ)*X 1 0+(979474789/2500000000 : ℝ)*X 1 1+(3917899093/10000000000 : ℝ)*X 1 2+(4467618863/10000000000 : ℝ)*X 2 0+(979474789/2500000000 : ℝ)*X 2 1+(3917899093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1691619351/10000000000 : ℝ)*X 0 0+(1035581121/2000000000 : ℝ)*X 0 1+(2588952789/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345359097/2500000000 : ℝ)*X 1 0+(-355237013/2500000000 : ℝ)*X 1 1+(5177905461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2690718091/5000000000 : ℝ)*X 2 0+(5177905661/10000000000 : ℝ)*X 2 1+(-1420948061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3690288543/10000000000 : ℝ)*X 0 0+(4305757749/10000000000 : ℝ)*X 0 1+(861151611/2000000000 : ℝ)*X 0 2+(3690288543/10000000000 : ℝ)*X 1 0+(4305757749/10000000000 : ℝ)*X 1 1+(861151611/2000000000 : ℝ)*X 1 2+(3690288543/10000000000 : ℝ)*X 2 0+(4305757749/10000000000 : ℝ)*X 2 1+(861151611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1554498869/10000000000 : ℝ)*X 0 0+(200238997/400000000 : ℝ)*X 0 1+(10648647/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598057901/5000000000 : ℝ)*X 1 0+(-1298507257/10000000000 : ℝ)*X 1 1+(5452106497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196115693/10000000000 : ℝ)*X 2 0+(5452107069/10000000000 : ℝ)*X 2 1+(-81156663/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((920786447/2000000000 : ℝ)*X 0 0+(961806441/2500000000 : ℝ)*X 0 1+(961806451/2500000000 : ℝ)*X 0 2+(920786447/2000000000 : ℝ)*X 1 0+(961806441/2500000000 : ℝ)*X 1 1+(961806451/2500000000 : ℝ)*X 1 2+(920786447/2000000000 : ℝ)*X 2 0+(961806441/2500000000 : ℝ)*X 2 1+(961806451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-118619887/1000000000 : ℝ)*X 0 0+(44591851/80000000 : ℝ)*X 0 1+(644117963/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5398341637/10000000000 : ℝ)*X 1 0+(-715798407/5000000000 : ℝ)*X 1 1+(1288235949/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215933669/400000000 : ℝ)*X 2 0+(5152943687/10000000000 : ℝ)*X 2 1+(-1431596841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((900920531/2500000000 : ℝ)*X 0 0+(4347369519/10000000000 : ℝ)*X 0 1+(869473831/2000000000 : ℝ)*X 0 2+(900920531/2500000000 : ℝ)*X 1 0+(4347369519/10000000000 : ℝ)*X 1 1+(869473831/2000000000 : ℝ)*X 1 2+(900920531/2500000000 : ℝ)*X 2 0+(4347369519/10000000000 : ℝ)*X 2 1+(869473831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1724_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33441/50000 : ℝ) ≤ (-22112149664866576573347820445247/33062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2110701/50000000000000 : ℝ)*(lower0) + (1660329/100000000000000 : ℝ)*(lower2) + (13163217/50000000000000 : ℝ)*(lower3) + (34946383/100000000000000 : ℝ)*(lower4) + (4530209/50000000000000 : ℝ)*(lower5) + (347984658290973/25000000000000 : ℝ)*(major0) + (347984658290973/25000000000000 : ℝ)*(major1) + (347984658290973/25000000000000 : ℝ)*(major2) + (527201420799139/25000000000000 : ℝ)*(sp4) + (2108805020817951/100000000000000 : ℝ)*(sp5) + (52719975343033/2500000000000 : ℝ)*(sp6) + (697364865717097/100000000000000 : ℝ)*(sp7) + (132475721/20000000000000 : ℝ)*(sp13) + (1667368809/25000000000000 : ℝ)*(sp14) + (697364865717097/100000000000000 : ℝ)*(f.failure) + (527201420799139/25000000000000 : ℝ)*(f.sum) + (88300404699519/34385000000000000000000000000 : ℝ)*base66 + (18075312149878525237/1719250000000000000000000000000000 : ℝ)*base67 + (11370022810981025237/1719250000000000000000000000000000 : ℝ)*base69 + (2133281110466775237/1719250000000000000000000000000000 : ℝ)*base71 + (104720074866679/34385000000000000000000000000 : ℝ)*base74 + (7544991358638275237/1719250000000000000000000000000000 : ℝ)*base75 + (11758768775952025237/1719250000000000000000000000000000 : ℝ)*base77 + (534419389507474763/1719250000000000000000000000000000 : ℝ)*base80 + (54290345232241/34385000000000000000000000000 : ℝ)*base81 + (16463559/2000000000000000000000 : ℝ)*base90 + (16463559/2000000000000000000000 : ℝ)*base92 + (16463559/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58729/100000 : ℝ) ≤ (2019483868576085925719753710966917/3438500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4798203/100000000000000 : ℝ)*(upper0) + (5026093/50000000000000 : ℝ)*(upper3) + (4596377/50000000000000 : ℝ)*(upper4) + (1500819823791231/100000000000000 : ℝ)*(major0) + (1500819823791231/100000000000000 : ℝ)*(major1) + (1500819823791231/100000000000000 : ℝ)*(major2) + (1115073668398251/50000000000000 : ℝ)*(sp0) + (139384199818749/6250000000000 : ℝ)*(sp1) + (2230146492058729/100000000000000 : ℝ)*(sp2) + (751914568135923/100000000000000 : ℝ)*(sp3) + (647140041/100000000000000 : ℝ)*(sp5) + (28254333/50000000000000 : ℝ)*(sp7) + (507443523/100000000000000 : ℝ)*(sp8) + (84511331/6250000000000 : ℝ)*(sp10) + (751914624644589/100000000000000 : ℝ)*(f.failure) + (89205913769601/4000000000000 : ℝ)*(f.sum) + (75871868115237/34385000000000000000000000000 : ℝ)*base66 + (13343767514494755639/6877000000000000000000000000000000 : ℝ)*base67 + (39908417407389244361/6877000000000000000000000000000000 : ℝ)*base70 + (7082420694971244361/6877000000000000000000000000000000 : ℝ)*base72 + (269141981228067/34385000000000000000000000000 : ℝ)*base74 + (12554700442244361/6877000000000000000000000000000000 : ℝ)*base76 + (15268471747491755639/6877000000000000000000000000000000 : ℝ)*base77 + (47023063214359244361/6877000000000000000000000000000000 : ℝ)*base80 + (206099405059417/34385000000000000000000000000 : ℝ)*base82 + (14584317/2000000000000000000000 : ℝ)*base89 + (14584317/2000000000000000000000 : ℝ)*base91 + (14584317/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20481/25000 : ℝ) ≤ (704261088222000917790683568277707/859625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10381281/50000000000000 : ℝ)*(upper1) + (3442939/2500000000000 : ℝ)*(lower3) + (30319929/50000000000000 : ℝ)*(upper4) + (13290001/50000000000000 : ℝ)*(lower5) + (378386629736201/25000000000000 : ℝ)*(major0) + (378386629736201/25000000000000 : ℝ)*(major1) + (378386629736201/25000000000000 : ℝ)*(major2) + (31877509/1000000000000 : ℝ)*(sp0) + (3733899929/12500000000000 : ℝ)*(sp2) + (11813629959/100000000000000 : ℝ)*(sp3) + (2241490268878393/100000000000000 : ℝ)*(sp8) + (2241493456629293/100000000000000 : ℝ)*(sp9) + (112073179271493/5000000000000 : ℝ)*(sp10) + (758278918297909/100000000000000 : ℝ)*(sp11) + (189572682981967/25000000000000 : ℝ)*(f.failure) + (2241493456629293/100000000000000 : ℝ)*(f.sum) + (90481331275903/34385000000000000000000000000 : ℝ)*base66 + (9404105721766682431/1719250000000000000000000000000000 : ℝ)*base68 + (10369751316089182431/1719250000000000000000000000000000 : ℝ)*base70 + (9682814737016932431/1719250000000000000000000000000000 : ℝ)*base72 + (102966753917543/34385000000000000000000000000 : ℝ)*base74 + (10527802774917432431/1719250000000000000000000000000000 : ℝ)*base76 + (2906824861278567569/1719250000000000000000000000000000 : ℝ)*base77 + (905369491546567569/1719250000000000000000000000000000 : ℝ)*base79 + (304412445370003/34385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2487551/500000000000000000000 : ℝ)*base89 + (2487551/500000000000000000000 : ℝ)*base91 + (2487551/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90619/100000 : ℝ) ≤ (-59920030594359415436587800569787/66125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6499353/50000000000000 : ℝ)*(lower0) + (3205877/25000000000000 : ℝ)*(lower2) + (16853533/100000000000000 : ℝ)*(upper3) + (782149187850667/50000000000000 : ℝ)*(major0) + (782149187850667/50000000000000 : ℝ)*(major1) + (782149187850667/50000000000000 : ℝ)*(major2) + (50298573/20000000000000 : ℝ)*(sp0) + (79492967/4000000000000 : ℝ)*(sp5) + (422822039/6250000000000 : ℝ)*(sp6) + (58407971/50000000000000 : ℝ)*(sp8) + (593771068434891/25000000000000 : ℝ)*(sp12) + (593770663681049/25000000000000 : ℝ)*(sp13) + (593769469223937/25000000000000 : ℝ)*(sp14) + (391858771903197/50000000000000 : ℝ)*(sp15) + (391858771903197/50000000000000 : ℝ)*(f.failure) + (593771160512093/25000000000000 : ℝ)*(f.sum) + (37095381821/165312500000000000000000000 : ℝ)*base66 + (490342683932714929/264500000000000000000000000000000 : ℝ)*base68 + (1031113028991285071/264500000000000000000000000000000 : ℝ)*base69 + (257894051216714929/264500000000000000000000000000000 : ℝ)*base72 + (752941022221/661250000000000000000000000 : ℝ)*base73 + (452977389185214929/264500000000000000000000000000000 : ℝ)*base76 + (1668763002898714929/264500000000000000000000000000000 : ℝ)*base78 + (1454683077877714929/264500000000000000000000000000000 : ℝ)*base80 + (2676816754991/661250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4789741/1000000000000000000000 : ℝ)*base89 + (4789741/1000000000000000000000 : ℝ)*base91 + (4789741/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1724_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (531/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2023/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58729/100000 : ℝ) else (20481/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90619/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1724_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1724_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58729/100000 : ℝ) else (20481/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90619/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1724_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1724_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1724_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5407/1024 : ℝ) ≤ p) (hpb : p ≤ (5415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39919953/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58729/100000 : ℝ) else (20481/25000 : ℝ) ≤ X j i ∧ X j i ≤ (90619/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1724_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

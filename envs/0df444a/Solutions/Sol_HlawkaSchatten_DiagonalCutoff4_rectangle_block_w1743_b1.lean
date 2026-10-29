-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1743_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:44.329546+00:00
-- url     : https://prove2.me/submissions/a1c6c4d0-0833-4da8-9b31-b8456cf5f22c

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
theorem support_rectangle_w1743_s3_0 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-631168921/5000000000 : ℝ)*x 0 + (5506641849/10000000000 : ℝ)*x 1 + (5078905797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (631168921/5000000000 : ℝ)^5663 ≤ (3997068580937/50000000000000 : ℝ)^4639 := by
    have hnat : (631168921 : ℕ)^5663*50000000000000^4639 ≤ 3997068580937^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631168921 5000000000 3997068580937 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506641849/10000000000 : ℝ)^5663 ≤ (48271512663697/100000000000000 : ℝ)^4639 := by
    have hnat : (5506641849 : ℕ)^5663*100000000000000^4639 ≤ 48271512663697^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506641849 10000000000 48271512663697 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078905797/10000000000 : ℝ)^5663 ≤ (43734350169233/100000000000000 : ℝ)^4639 := by
    have hnat : (5078905797 : ℕ)^5663*100000000000000^4639 ≤ 43734350169233^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078905797 10000000000 43734350169233 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-631168921/5000000000 : ℝ), (5506641849/10000000000 : ℝ), (5078905797/10000000000 : ℝ)] ![(3997068580937/50000000000000 : ℝ), (48271512663697/100000000000000 : ℝ), (43734350169233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-631168921/5000000000 : ℝ)|^5663 ≤ (3997068580937/50000000000000 : ℝ)^4639
        have hw : |(-631168921/5000000000 : ℝ)|=(631168921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506641849/10000000000 : ℝ)|^5663 ≤ (48271512663697/100000000000000 : ℝ)^4639
        have hw : |(5506641849/10000000000 : ℝ)|=(5506641849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078905797/10000000000 : ℝ)|^5663 ≤ (43734350169233/100000000000000 : ℝ)^4639
        have hw : |(5078905797/10000000000 : ℝ)|=(5078905797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_1 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068241013/2000000000 : ℝ)*x 0 + (-148637411/1000000000 : ℝ)*x 1 + (5078905953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068241013/2000000000 : ℝ)^5663 ≤ (5813385308151/12500000000000 : ℝ)^4639 := by
    have hnat : (1068241013 : ℕ)^5663*12500000000000^4639 ≤ 5813385308151^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068241013 2000000000 5813385308151 12500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148637411/1000000000 : ℝ)^5663 ≤ (4879282856271/50000000000000 : ℝ)^4639 := by
    have hnat : (148637411 : ℕ)^5663*50000000000000^4639 ≤ 4879282856271^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148637411 1000000000 4879282856271 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078905953/10000000000 : ℝ)^5663 ≤ (8746870361813/20000000000000 : ℝ)^4639 := by
    have hnat : (5078905953 : ℕ)^5663*20000000000000^4639 ≤ 8746870361813^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078905953 10000000000 8746870361813 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068241013/2000000000 : ℝ), (-148637411/1000000000 : ℝ), (5078905953/10000000000 : ℝ)] ![(5813385308151/12500000000000 : ℝ), (4879282856271/50000000000000 : ℝ), (8746870361813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068241013/2000000000 : ℝ)|^5663 ≤ (5813385308151/12500000000000 : ℝ)^4639
        have hw : |(1068241013/2000000000 : ℝ)|=(1068241013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-148637411/1000000000 : ℝ)|^5663 ≤ (4879282856271/50000000000000 : ℝ)^4639
        have hw : |(-148637411/1000000000 : ℝ)|=(148637411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078905953/10000000000 : ℝ)|^5663 ≤ (8746870361813/20000000000000 : ℝ)^4639
        have hw : |(5078905953/10000000000 : ℝ)|=(5078905953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_2 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667650627/1250000000 : ℝ)*x 0 + (507890597/1000000000 : ℝ)*x 1 + (-185796769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667650627/1250000000 : ℝ)^5663 ≤ (74411331111/160000000000 : ℝ)^4639 := by
    have hnat : (667650627 : ℕ)^5663*160000000000^4639 ≤ 74411331111^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667650627 1250000000 74411331111 160000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507890597/1000000000 : ℝ)^5663 ≤ (10933587996941/25000000000000 : ℝ)^4639 := by
    have hnat : (507890597 : ℕ)^5663*25000000000000^4639 ≤ 10933587996941^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507890597 1000000000 10933587996941 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185796769/1250000000 : ℝ)^5663 ≤ (4879283024577/50000000000000 : ℝ)^4639 := by
    have hnat : (185796769 : ℕ)^5663*50000000000000^4639 ≤ 4879283024577^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185796769 1250000000 4879283024577 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667650627/1250000000 : ℝ), (507890597/1000000000 : ℝ), (-185796769/1250000000 : ℝ)] ![(74411331111/160000000000 : ℝ), (10933587996941/25000000000000 : ℝ), (4879283024577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667650627/1250000000 : ℝ)|^5663 ≤ (74411331111/160000000000 : ℝ)^4639
        have hw : |(667650627/1250000000 : ℝ)|=(667650627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(507890597/1000000000 : ℝ)|^5663 ≤ (10933587996941/25000000000000 : ℝ)^4639
        have hw : |(507890597/1000000000 : ℝ)|=(507890597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-185796769/1250000000 : ℝ)|^5663 ≤ (4879283024577/50000000000000 : ℝ)^4639
        have hw : |(-185796769/1250000000 : ℝ)|=(185796769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_3 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1008941161/2500000000 : ℝ)*x 0 + (3385586179/10000000000 : ℝ)*x 1 + (4750855339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008941161/2500000000 : ℝ)^5663 ≤ (16516156753407/50000000000000 : ℝ)^4639 := by
    have hnat : (1008941161 : ℕ)^5663*50000000000000^4639 ≤ 16516156753407^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008941161 2500000000 16516156753407 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3385586179/10000000000 : ℝ)^5663 ≤ (533134213359/2000000000000 : ℝ)^4639 := by
    have hnat : (3385586179 : ℕ)^5663*2000000000000^4639 ≤ 533134213359^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3385586179 10000000000 533134213359 2000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4750855339/10000000000 : ℝ)^5663 ≤ (8062195160853/20000000000000 : ℝ)^4639 := by
    have hnat : (4750855339 : ℕ)^5663*20000000000000^4639 ≤ 8062195160853^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750855339 10000000000 8062195160853 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1008941161/2500000000 : ℝ), (3385586179/10000000000 : ℝ), (4750855339/10000000000 : ℝ)] ![(16516156753407/50000000000000 : ℝ), (533134213359/2000000000000 : ℝ), (8062195160853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1008941161/2500000000 : ℝ)|^5663 ≤ (16516156753407/50000000000000 : ℝ)^4639
        have hw : |(1008941161/2500000000 : ℝ)|=(1008941161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3385586179/10000000000 : ℝ)|^5663 ≤ (533134213359/2000000000000 : ℝ)^4639
        have hw : |(3385586179/10000000000 : ℝ)|=(3385586179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4750855339/10000000000 : ℝ)|^5663 ≤ (8062195160853/20000000000000 : ℝ)^4639
        have hw : |(4750855339/10000000000 : ℝ)|=(4750855339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_4 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-631351957/5000000000 : ℝ)*x 0 + (127144589/250000000 : ℝ)*x 1 + (5499619289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (631351957/5000000000 : ℝ)^5663 ≤ (499810452569/6250000000000 : ℝ)^4639 := by
    have hnat : (631351957 : ℕ)^5663*6250000000000^4639 ≤ 499810452569^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631351957 5000000000 499810452569 6250000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127144589/250000000 : ℝ)^5663 ≤ (43806658243837/100000000000000 : ℝ)^4639 := by
    have hnat : (127144589 : ℕ)^5663*100000000000000^4639 ≤ 43806658243837^4639*250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127144589 250000000 43806658243837 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499619289/10000000000 : ℝ)^5663 ≤ (3012273406299/6250000000000 : ℝ)^4639 := by
    have hnat : (5499619289 : ℕ)^5663*6250000000000^4639 ≤ 3012273406299^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499619289 10000000000 3012273406299 6250000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-631351957/5000000000 : ℝ), (127144589/250000000 : ℝ), (5499619289/10000000000 : ℝ)] ![(499810452569/6250000000000 : ℝ), (43806658243837/100000000000000 : ℝ), (3012273406299/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-631351957/5000000000 : ℝ)|^5663 ≤ (499810452569/6250000000000 : ℝ)^4639
        have hw : |(-631351957/5000000000 : ℝ)|=(631351957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127144589/250000000 : ℝ)|^5663 ≤ (43806658243837/100000000000000 : ℝ)^4639
        have hw : |(127144589/250000000 : ℝ)|=(127144589/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499619289/10000000000 : ℝ)|^5663 ≤ (3012273406299/6250000000000 : ℝ)^4639
        have hw : |(5499619289/10000000000 : ℝ)|=(5499619289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_5 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227624143/10000000000 : ℝ)*x 0 + (-213132091/2000000000 : ℝ)*x 1 + (5499619531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227624143/10000000000 : ℝ)^5663 ≤ (45302653362213/100000000000000 : ℝ)^4639 := by
    have hnat : (5227624143 : ℕ)^5663*100000000000000^4639 ≤ 45302653362213^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227624143 10000000000 45302653362213 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213132091/2000000000 : ℝ)^5663 ≤ (6500969531931/100000000000000 : ℝ)^4639 := by
    have hnat : (213132091 : ℕ)^5663*100000000000000^4639 ≤ 6500969531931^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213132091 2000000000 6500969531931 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499619531/10000000000 : ℝ)^5663 ≤ (12049094272427/25000000000000 : ℝ)^4639 := by
    have hnat : (5499619531 : ℕ)^5663*25000000000000^4639 ≤ 12049094272427^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499619531 10000000000 12049094272427 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227624143/10000000000 : ℝ), (-213132091/2000000000 : ℝ), (5499619531/10000000000 : ℝ)] ![(45302653362213/100000000000000 : ℝ), (6500969531931/100000000000000 : ℝ), (12049094272427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227624143/10000000000 : ℝ)|^5663 ≤ (45302653362213/100000000000000 : ℝ)^4639
        have hw : |(5227624143/10000000000 : ℝ)|=(5227624143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213132091/2000000000 : ℝ)|^5663 ≤ (6500969531931/100000000000000 : ℝ)^4639
        have hw : |(-213132091/2000000000 : ℝ)|=(213132091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499619531/10000000000 : ℝ)|^5663 ≤ (12049094272427/25000000000000 : ℝ)^4639
        have hw : |(5499619531/10000000000 : ℝ)|=(5499619531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_6 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227623891/10000000000 : ℝ)*x 0 + (5499619953/10000000000 : ℝ)*x 1 + (-532830103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227623891/10000000000 : ℝ)^5663 ≤ (11325662674081/25000000000000 : ℝ)^4639 := by
    have hnat : (5227623891 : ℕ)^5663*25000000000000^4639 ≤ 11325662674081^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227623891 10000000000 11325662674081 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499619953/10000000000 : ℝ)^5663 ≤ (24098190802139/50000000000000 : ℝ)^4639 := by
    have hnat : (5499619953 : ℕ)^5663*50000000000000^4639 ≤ 24098190802139^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499619953 10000000000 24098190802139 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532830103/5000000000 : ℝ)^5663 ≤ (6500967677627/100000000000000 : ℝ)^4639 := by
    have hnat : (532830103 : ℕ)^5663*100000000000000^4639 ≤ 6500967677627^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532830103 5000000000 6500967677627 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227623891/10000000000 : ℝ), (5499619953/10000000000 : ℝ), (-532830103/5000000000 : ℝ)] ![(11325662674081/25000000000000 : ℝ), (24098190802139/50000000000000 : ℝ), (6500967677627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227623891/10000000000 : ℝ)|^5663 ≤ (11325662674081/25000000000000 : ℝ)^4639
        have hw : |(5227623891/10000000000 : ℝ)|=(5227623891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499619953/10000000000 : ℝ)|^5663 ≤ (24098190802139/50000000000000 : ℝ)^4639
        have hw : |(5499619953/10000000000 : ℝ)|=(5499619953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532830103/5000000000 : ℝ)|^5663 ≤ (6500967677627/100000000000000 : ℝ)^4639
        have hw : |(-532830103/5000000000 : ℝ)|=(532830103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s3_7 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (504616517/1250000000 : ℝ)*x 0 + (1182225967/2500000000 : ℝ)*x 1 + (3408000123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504616517/1250000000 : ℝ)^5663 ≤ (33043979000631/100000000000000 : ℝ)^4639 := by
    have hnat : (504616517 : ℕ)^5663*100000000000000^4639 ≤ 33043979000631^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504616517 1250000000 33043979000631 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182225967/2500000000 : ℝ)^5663 ≤ (40083719716741/100000000000000 : ℝ)^4639 := by
    have hnat : (1182225967 : ℕ)^5663*100000000000000^4639 ≤ 40083719716741^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182225967 2500000000 40083719716741 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3408000123/10000000000 : ℝ)^5663 ≤ (13436150636027/50000000000000 : ℝ)^4639 := by
    have hnat : (3408000123 : ℕ)^5663*50000000000000^4639 ≤ 13436150636027^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408000123 10000000000 13436150636027 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(504616517/1250000000 : ℝ), (1182225967/2500000000 : ℝ), (3408000123/10000000000 : ℝ)] ![(33043979000631/100000000000000 : ℝ), (40083719716741/100000000000000 : ℝ), (13436150636027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(504616517/1250000000 : ℝ)|^5663 ≤ (33043979000631/100000000000000 : ℝ)^4639
        have hw : |(504616517/1250000000 : ℝ)|=(504616517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1182225967/2500000000 : ℝ)|^5663 ≤ (40083719716741/100000000000000 : ℝ)^4639
        have hw : |(1182225967/2500000000 : ℝ)|=(1182225967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3408000123/10000000000 : ℝ)|^5663 ≤ (13436150636027/50000000000000 : ℝ)^4639
        have hw : |(3408000123/10000000000 : ℝ)|=(3408000123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1743_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1789/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (566/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8943/100000 : ℝ) ^ (5647/1024 : ℝ) ≤ (165119603383687/100000000000000000000 : ℝ) := by
    have hpowers : (8943/100000 : ℝ)^5647 ≤ (165119603383687/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8943 : ℕ)^5647*100000000000000000000^1024 ≤ 165119603383687^1024*100000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8943 100000 165119603383687 100000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8943/100000 : ℝ)) (X := (165119603383687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9057/50000 : ℝ) ^ (5647/1024 : ℝ) ≤ (8094873540386079/100000000000000000000 : ℝ) := by
    have hpowers : (9057/50000 : ℝ)^5647 ≤ (8094873540386079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9057 : ℕ)^5647*100000000000000000000^1024 ≤ 8094873540386079^1024*50000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9057 50000 8094873540386079 100000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9057/50000 : ℝ)) (X := (8094873540386079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000165119603383687/50000000000000000000 : ℝ) ≤ (10000005988391901/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (50000165119603383687/50000000000000000000 : ℝ)^1024 ≤ (10000005988391901/10000000000000000 : ℝ)^5647 := by
      have hnat : (50000165119603383687 : ℕ)^1024*10000000000000000^5647 ≤ 10000005988391901^5647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000165119603383687 50000000000000000000 10000005988391901 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005988391901/10000000000000000 : ℝ)) (X := (50000165119603383687/50000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004129996571884883/50000000000000000000 : ℝ) ≤ (10000149777705219/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (50004129996571884883/50000000000000000000 : ℝ)^1024 ≤ (10000149777705219/10000000000000000 : ℝ)^5647 := by
      have hnat : (50004129996571884883 : ℕ)^1024*10000000000000000^5647 ≤ 10000149777705219^5647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004129996571884883 50000000000000000000 10000149777705219 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000149777705219/10000000000000000 : ℝ)) (X := (50004129996571884883/50000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008094873540386079/50000000000000000000 : ℝ) ≤ (10000293567018537/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (50008094873540386079/50000000000000000000 : ℝ)^1024 ≤ (10000293567018537/10000000000000000 : ℝ)^5647 := by
      have hnat : (50008094873540386079 : ℕ)^1024*10000000000000000^5647 ≤ 10000293567018537^5647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008094873540386079 50000000000000000000 10000293567018537 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000293567018537/10000000000000000 : ℝ)) (X := (50008094873540386079/50000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(165119603383687/100000000000000000000 : ℝ) ≤ ((10189720344876013147/10190000000000000000 : ℝ)+2*(23964885553/152850000000000 : ℝ)*(8943/100000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (10189720344876013147/10190000000000000000 : ℝ)+2*(23964885553/152850000000000 : ℝ)*(8943/100000 : ℝ)=(10000005988391901/10000000000000000 : ℝ) by norm_num, show 1+2*(165119603383687/100000000000000000000 : ℝ)=(50000165119603383687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8094873540386079/100000000000000000000 : ℝ)+(165119603383687/100000000000000000000 : ℝ) ≤ ((10189720344876013147/10190000000000000000 : ℝ)+(23964885553/152850000000000 : ℝ)*((9057/50000 : ℝ)+(8943/100000 : ℝ)))^(5647/1024 : ℝ) := by
    rw [show (10189720344876013147/10190000000000000000 : ℝ)+(23964885553/152850000000000 : ℝ)*((9057/50000 : ℝ)+(8943/100000 : ℝ))=(10000149777705219/10000000000000000 : ℝ) by norm_num, show 1+(8094873540386079/100000000000000000000 : ℝ)+(165119603383687/100000000000000000000 : ℝ)=(50004129996571884883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8094873540386079/100000000000000000000 : ℝ) ≤ ((10189720344876013147/10190000000000000000 : ℝ)+2*(23964885553/152850000000000 : ℝ)*(9057/50000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (10189720344876013147/10190000000000000000 : ℝ)+2*(23964885553/152850000000000 : ℝ)*(9057/50000 : ℝ)=(10000293567018537/10000000000000000 : ℝ) by norm_num, show 1+2*(8094873540386079/100000000000000000000 : ℝ)=(50008094873540386079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10189720344876013147/10190000000000000000 : ℝ)*(X 1 0+X 2 0)+(23964885553/152850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (8943/100000 : ℝ)) (hi := (9057/50000 : ℝ)) (c := (10189720344876013147/10190000000000000000 : ℝ)) (alpha := (23964885553/152850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10189720344876013147/10190000000000000000 : ℝ)*(X 0 1+X 2 1)+(23964885553/152850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (8943/100000 : ℝ)) (hi := (9057/50000 : ℝ)) (c := (10189720344876013147/10190000000000000000 : ℝ)) (alpha := (23964885553/152850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10189720344876013147/10190000000000000000 : ℝ)*(X 0 2+X 1 2)+(23964885553/152850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (8943/100000 : ℝ)) (hi := (9057/50000 : ℝ)) (c := (10189720344876013147/10190000000000000000 : ℝ)) (alpha := (23964885553/152850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-631168921/5000000000 : ℝ)*X 0 0+(5506641849/10000000000 : ℝ)*X 0 1+(5078905797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068241013/2000000000 : ℝ)*X 1 0+(-148637411/1000000000 : ℝ)*X 1 1+(5078905953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667650627/1250000000 : ℝ)*X 2 0+(507890597/1000000000 : ℝ)*X 2 1+(-185796769/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1008941161/2500000000 : ℝ)*X 0 0+(3385586179/10000000000 : ℝ)*X 0 1+(4750855339/10000000000 : ℝ)*X 0 2+(1008941161/2500000000 : ℝ)*X 1 0+(3385586179/10000000000 : ℝ)*X 1 1+(4750855339/10000000000 : ℝ)*X 1 2+(1008941161/2500000000 : ℝ)*X 2 0+(3385586179/10000000000 : ℝ)*X 2 1+(4750855339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-631351957/5000000000 : ℝ)*X 0 0+(127144589/250000000 : ℝ)*X 0 1+(5499619289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227624143/10000000000 : ℝ)*X 1 0+(-213132091/2000000000 : ℝ)*X 1 1+(5499619531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5227623891/10000000000 : ℝ)*X 2 0+(5499619953/10000000000 : ℝ)*X 2 1+(-532830103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((504616517/1250000000 : ℝ)*X 0 0+(1182225967/2500000000 : ℝ)*X 0 1+(3408000123/10000000000 : ℝ)*X 0 2+(504616517/1250000000 : ℝ)*X 1 0+(1182225967/2500000000 : ℝ)*X 1 1+(3408000123/10000000000 : ℝ)*X 1 2+(504616517/1250000000 : ℝ)*X 2 0+(1182225967/2500000000 : ℝ)*X 2 1+(3408000123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1242922149044400548709345063/254750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (703262857/100000000000000 : ℝ)*(base19) + (16996957/2500000000000 : ℝ)*(base23) + (1034463/100000000000000 : ℝ)*(lower2) + (129995029/100000000000000 : ℝ)*(upper3) + (52336109/50000000000000 : ℝ)*(upper5) + (767590734844857/50000000000000 : ℝ)*(major0) + (767590734844857/50000000000000 : ℝ)*(major1) + (767590734844857/50000000000000 : ℝ)*(major2) + (584474150306141/25000000000000 : ℝ)*(sp0) + (292237737632719/12500000000000 : ℝ)*(sp1) + (292237740555791/12500000000000 : ℝ)*(sp2) + (45778635025577/6250000000000 : ℝ)*(sp3) + (1200620009/20000000000000 : ℝ)*(sp4) + (1006006327/50000000000000 : ℝ)*(sp7) + (366230086210943/50000000000000 : ℝ)*(f.failure) + (9132432048143/390625000000 : ℝ)*(f.sum) + (3992187537249/2547500000000000000000000000 : ℝ)*base65 + (1775870738056734979/509500000000000000000000000000000 : ℝ)*base67 + (1978697107929765021/509500000000000000000000000000000 : ℝ)*base70 + (518778166405265021/509500000000000000000000000000000 : ℝ)*base72 + (6188139850157/1273750000000000000000000000 : ℝ)*base73 + (1803706501211734979/509500000000000000000000000000000 : ℝ)*base75 + (3824094179598734979/509500000000000000000000000000000 : ℝ)*base77 + (3019896954378734979/509500000000000000000000000000000 : ℝ)*base79 + (9548582265501/2547500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2161897/1250000000000000000000 : ℝ)*base90 + (2161897/1250000000000000000000 : ℝ)*base92 + (2161897/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25792922915503728903309/5095000000000000000000000000 : ℝ) := by norm_num
    linear_combination (339010429/50000000000000 : ℝ)*(base19) + (781184303/100000000000000 : ℝ)*(base23) + (2759139/1562500000000 : ℝ)*(lower1) + (17785343/25000000000000 : ℝ)*(upper2) + (9351371/5000000000000 : ℝ)*(upper3) + (11058229/25000000000000 : ℝ)*(upper5) + (1586733507243373/100000000000000 : ℝ)*(major0) + (1586733507243373/100000000000000 : ℝ)*(major1) + (1586733507243373/100000000000000 : ℝ)*(major2) + (3845896067/100000000000000 : ℝ)*(sp2) + (2416410353560083/100000000000000 : ℝ)*(sp4) + (302051209442403/12500000000000 : ℝ)*(sp5) + (2416405726479713/100000000000000 : ℝ)*(sp6) + (378528246090011/50000000000000 : ℝ)*(sp7) + (378528246090011/50000000000000 : ℝ)*(f.failure) + (2416410353560083/100000000000000 : ℝ)*(f.sum) + (575282224633/238828125000000000000000000 : ℝ)*base66 + (10898075163348325507/3057000000000000000000000000000000 : ℝ)*base68 + (60439887832017325507/3057000000000000000000000000000000 : ℝ)*base70 + (6298431940115674493/3057000000000000000000000000000000 : ℝ)*base71 + (42094789819811/7642500000000000000000000000 : ℝ)*base74 + (40503037948433674493/3057000000000000000000000000000000 : ℝ)*base75 + (8882176782704674493/3057000000000000000000000000000000 : ℝ)*base77 + (2206100946291325507/3057000000000000000000000000000000 : ℝ)*base80 + (54831348274001/7642500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10769331/1250000000000000000000 : ℝ)*base89 + (10769331/1250000000000000000000 : ℝ)*base91 + (10769331/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1743_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1789/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (566/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1743_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1743_box_0 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-863693997/10000000000 : ℝ)*x 0 + (1086606099/2000000000 : ℝ)*x 1 + (5433030381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863693997/10000000000 : ℝ)^5663 ≤ (1257520121513/25000000000000 : ℝ)^4639 := by
    have hnat : (863693997 : ℕ)^5663*25000000000000^4639 ≤ 1257520121513^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863693997 10000000000 1257520121513 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086606099/2000000000 : ℝ)^5663 ≤ (47484960356939/100000000000000 : ℝ)^4639 := by
    have hnat : (1086606099 : ℕ)^5663*100000000000000^4639 ≤ 47484960356939^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086606099 2000000000 47484960356939 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433030381/10000000000 : ℝ)^5663 ≤ (47484959140639/100000000000000 : ℝ)^4639 := by
    have hnat : (5433030381 : ℕ)^5663*100000000000000^4639 ≤ 47484959140639^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433030381 10000000000 47484959140639 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-863693997/10000000000 : ℝ), (1086606099/2000000000 : ℝ), (5433030381/10000000000 : ℝ)] ![(1257520121513/25000000000000 : ℝ), (47484960356939/100000000000000 : ℝ), (47484959140639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-863693997/10000000000 : ℝ)|^5663 ≤ (1257520121513/25000000000000 : ℝ)^4639
        have hw : |(-863693997/10000000000 : ℝ)|=(863693997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086606099/2000000000 : ℝ)|^5663 ≤ (47484960356939/100000000000000 : ℝ)^4639
        have hw : |(1086606099/2000000000 : ℝ)|=(1086606099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433030381/10000000000 : ℝ)|^5663 ≤ (47484959140639/100000000000000 : ℝ)^4639
        have hw : |(5433030381/10000000000 : ℝ)|=(5433030381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_1 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129874707/250000000 : ℝ)*x 0 + (-1205558829/10000000000 : ℝ)*x 1 + (848911/1562500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129874707/250000000 : ℝ)^5663 ≤ (175615778679/390625000000 : ℝ)^4639 := by
    have hnat : (129874707 : ℕ)^5663*390625000000^4639 ≤ 175615778679^4639*250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129874707 250000000 175615778679 390625000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205558829/10000000000 : ℝ)^5663 ≤ (7557401304573/100000000000000 : ℝ)^4639 := by
    have hnat : (1205558829 : ℕ)^5663*100000000000000^4639 ≤ 7557401304573^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205558829 10000000000 7557401304573 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848911/1562500 : ℝ)^5663 ≤ (9496991868671/20000000000000 : ℝ)^4639 := by
    have hnat : (848911 : ℕ)^5663*20000000000000^4639 ≤ 9496991868671^4639*1562500^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848911 1562500 9496991868671 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129874707/250000000 : ℝ), (-1205558829/10000000000 : ℝ), (848911/1562500 : ℝ)] ![(175615778679/390625000000 : ℝ), (7557401304573/100000000000000 : ℝ), (9496991868671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129874707/250000000 : ℝ)|^5663 ≤ (175615778679/390625000000 : ℝ)^4639
        have hw : |(129874707/250000000 : ℝ)|=(129874707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1205558829/10000000000 : ℝ)|^5663 ≤ (7557401304573/100000000000000 : ℝ)^4639
        have hw : |(-1205558829/10000000000 : ℝ)|=(1205558829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848911/1562500 : ℝ)|^5663 ≤ (9496991868671/20000000000000 : ℝ)^4639
        have hw : |(848911/1562500 : ℝ)|=(848911/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_2 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194988267/10000000000 : ℝ)*x 0 + (5433030383/10000000000 : ℝ)*x 1 + (-120555887/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194988267/10000000000 : ℝ)^5663 ≤ (5619704900561/12500000000000 : ℝ)^4639 := by
    have hnat : (5194988267 : ℕ)^5663*12500000000000^4639 ≤ 5619704900561^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194988267 10000000000 5619704900561 12500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433030383/10000000000 : ℝ)^5663 ≤ (47484959161977/100000000000000 : ℝ)^4639 := by
    have hnat : (5433030383 : ℕ)^5663*100000000000000^4639 ≤ 47484959161977^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433030383 10000000000 47484959161977 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120555887/1000000000 : ℝ)^5663 ≤ (944675202291/12500000000000 : ℝ)^4639 := by
    have hnat : (120555887 : ℕ)^5663*12500000000000^4639 ≤ 944675202291^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120555887 1000000000 944675202291 12500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194988267/10000000000 : ℝ), (5433030383/10000000000 : ℝ), (-120555887/1000000000 : ℝ)] ![(5619704900561/12500000000000 : ℝ), (47484959161977/100000000000000 : ℝ), (944675202291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194988267/10000000000 : ℝ)|^5663 ≤ (5619704900561/12500000000000 : ℝ)^4639
        have hw : |(5194988267/10000000000 : ℝ)|=(5194988267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433030383/10000000000 : ℝ)|^5663 ≤ (47484959161977/100000000000000 : ℝ)^4639
        have hw : |(5433030383/10000000000 : ℝ)|=(5433030383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120555887/1000000000 : ℝ)|^5663 ≤ (944675202291/12500000000000 : ℝ)^4639
        have hw : |(-120555887/1000000000 : ℝ)|=(120555887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_3 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4563445671/10000000000 : ℝ)*x 0 + (3812040851/10000000000 : ℝ)*x 1 + (3812040883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4563445671/10000000000 : ℝ)^5663 ≤ (959458399049/2500000000000 : ℝ)^4639 := by
    have hnat : (4563445671 : ℕ)^5663*2500000000000^4639 ≤ 959458399049^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563445671 10000000000 959458399049 2500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3812040851/10000000000 : ℝ)^5663 ≤ (30810831849973/100000000000000 : ℝ)^4639 := by
    have hnat : (3812040851 : ℕ)^5663*100000000000000^4639 ≤ 30810831849973^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3812040851 10000000000 30810831849973 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3812040883/10000000000 : ℝ)^5663 ≤ (6162166433141/20000000000000 : ℝ)^4639 := by
    have hnat : (3812040883 : ℕ)^5663*20000000000000^4639 ≤ 6162166433141^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3812040883 10000000000 6162166433141 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4563445671/10000000000 : ℝ), (3812040851/10000000000 : ℝ), (3812040883/10000000000 : ℝ)] ![(959458399049/2500000000000 : ℝ), (30810831849973/100000000000000 : ℝ), (6162166433141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4563445671/10000000000 : ℝ)|^5663 ≤ (959458399049/2500000000000 : ℝ)^4639
        have hw : |(4563445671/10000000000 : ℝ)|=(4563445671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3812040851/10000000000 : ℝ)|^5663 ≤ (30810831849973/100000000000000 : ℝ)^4639
        have hw : |(3812040851/10000000000 : ℝ)|=(3812040851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3812040883/10000000000 : ℝ)|^5663 ≤ (6162166433141/20000000000000 : ℝ)^4639
        have hw : |(3812040883/10000000000 : ℝ)|=(3812040883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_4 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-425304157/2500000000 : ℝ)*x 0 + (5127579331/10000000000 : ℝ)*x 1 + (5127579187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425304157/2500000000 : ℝ)^5663 ≤ (11506934199739/100000000000000 : ℝ)^4639 := by
    have hnat : (425304157 : ℕ)^5663*100000000000000^4639 ≤ 11506934199739^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425304157 2500000000 11506934199739 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127579331/10000000000 : ℝ)^5663 ≤ (22123266825687/50000000000000 : ℝ)^4639 := by
    have hnat : (5127579331 : ℕ)^5663*50000000000000^4639 ≤ 22123266825687^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127579331 10000000000 22123266825687 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127579187/10000000000 : ℝ)^5663 ≤ (44246532134493/100000000000000 : ℝ)^4639 := by
    have hnat : (5127579187 : ℕ)^5663*100000000000000^4639 ≤ 44246532134493^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127579187 10000000000 44246532134493 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425304157/2500000000 : ℝ), (5127579331/10000000000 : ℝ), (5127579187/10000000000 : ℝ)] ![(11506934199739/100000000000000 : ℝ), (22123266825687/50000000000000 : ℝ), (44246532134493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425304157/2500000000 : ℝ)|^5663 ≤ (11506934199739/100000000000000 : ℝ)^4639
        have hw : |(-425304157/2500000000 : ℝ)|=(425304157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127579331/10000000000 : ℝ)|^5663 ≤ (22123266825687/50000000000000 : ℝ)^4639
        have hw : |(5127579331/10000000000 : ℝ)|=(5127579331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127579187/10000000000 : ℝ)|^5663 ≤ (44246532134493/100000000000000 : ℝ)^4639
        have hw : |(5127579187/10000000000 : ℝ)|=(5127579187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_5 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400077981/10000000000 : ℝ)*x 0 + (-1342720943/10000000000 : ℝ)*x 1 + (2563789651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400077981/10000000000 : ℝ)^5663 ≤ (9426723132211/20000000000000 : ℝ)^4639 := by
    have hnat : (5400077981 : ℕ)^5663*20000000000000^4639 ≤ 9426723132211^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400077981 10000000000 9426723132211 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342720943/10000000000 : ℝ)^5663 ≤ (1723970194761/20000000000000 : ℝ)^4639 := by
    have hnat : (1342720943 : ℕ)^5663*20000000000000^4639 ≤ 1723970194761^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342720943 10000000000 1723970194761 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563789651/5000000000 : ℝ)^5663 ≤ (44246533345891/100000000000000 : ℝ)^4639 := by
    have hnat : (2563789651 : ℕ)^5663*100000000000000^4639 ≤ 44246533345891^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563789651 5000000000 44246533345891 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400077981/10000000000 : ℝ), (-1342720943/10000000000 : ℝ), (2563789651/5000000000 : ℝ)] ![(9426723132211/20000000000000 : ℝ), (1723970194761/20000000000000 : ℝ), (44246533345891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400077981/10000000000 : ℝ)|^5663 ≤ (9426723132211/20000000000000 : ℝ)^4639
        have hw : |(5400077981/10000000000 : ℝ)|=(5400077981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342720943/10000000000 : ℝ)|^5663 ≤ (1723970194761/20000000000000 : ℝ)^4639
        have hw : |(-1342720943/10000000000 : ℝ)|=(1342720943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2563789651/5000000000 : ℝ)|^5663 ≤ (44246533345891/100000000000000 : ℝ)^4639
        have hw : |(2563789651/5000000000 : ℝ)|=(2563789651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_6 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675009731/1250000000 : ℝ)*x 0 + (5127579391/10000000000 : ℝ)*x 1 + (-268544201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675009731/1250000000 : ℝ)^5663 ≤ (47133614243941/100000000000000 : ℝ)^4639 := by
    have hnat : (675009731 : ℕ)^5663*100000000000000^4639 ≤ 47133614243941^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675009731 1250000000 47133614243941 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127579391/10000000000 : ℝ)^5663 ≤ (2765408392713/6250000000000 : ℝ)^4639 := by
    have hnat : (5127579391 : ℕ)^5663*6250000000000^4639 ≤ 2765408392713^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127579391 10000000000 2765408392713 6250000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268544201/2000000000 : ℝ)^5663 ≤ (2154962864921/25000000000000 : ℝ)^4639 := by
    have hnat : (268544201 : ℕ)^5663*25000000000000^4639 ≤ 2154962864921^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268544201 2000000000 2154962864921 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675009731/1250000000 : ℝ), (5127579391/10000000000 : ℝ), (-268544201/2000000000 : ℝ)] ![(47133614243941/100000000000000 : ℝ), (2765408392713/6250000000000 : ℝ), (2154962864921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675009731/1250000000 : ℝ)|^5663 ≤ (47133614243941/100000000000000 : ℝ)^4639
        have hw : |(675009731/1250000000 : ℝ)|=(675009731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127579391/10000000000 : ℝ)|^5663 ≤ (2765408392713/6250000000000 : ℝ)^4639
        have hw : |(5127579391/10000000000 : ℝ)|=(5127579391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268544201/2000000000 : ℝ)|^5663 ≤ (2154962864921/25000000000000 : ℝ)^4639
        have hw : |(-268544201/2000000000 : ℝ)|=(268544201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_7 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1736352027/5000000000 : ℝ)*x 0 + (435524719/1000000000 : ℝ)*x 1 + (4355247131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1736352027/5000000000 : ℝ)^5663 ≤ (6874103400031/25000000000000 : ℝ)^4639 := by
    have hnat : (1736352027 : ℕ)^5663*25000000000000^4639 ≤ 6874103400031^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736352027 5000000000 6874103400031 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435524719/1000000000 : ℝ)^5663 ≤ (3625179349723/10000000000000 : ℝ)^4639 := by
    have hnat : (435524719 : ℕ)^5663*10000000000000^4639 ≤ 3625179349723^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435524719 1000000000 3625179349723 10000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4355247131/10000000000 : ℝ)^5663 ≤ (36251792897727/100000000000000 : ℝ)^4639 := by
    have hnat : (4355247131 : ℕ)^5663*100000000000000^4639 ≤ 36251792897727^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355247131 10000000000 36251792897727 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1736352027/5000000000 : ℝ), (435524719/1000000000 : ℝ), (4355247131/10000000000 : ℝ)] ![(6874103400031/25000000000000 : ℝ), (3625179349723/10000000000000 : ℝ), (36251792897727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1736352027/5000000000 : ℝ)|^5663 ≤ (6874103400031/25000000000000 : ℝ)^4639
        have hw : |(1736352027/5000000000 : ℝ)|=(1736352027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(435524719/1000000000 : ℝ)|^5663 ≤ (3625179349723/10000000000000 : ℝ)^4639
        have hw : |(435524719/1000000000 : ℝ)|=(435524719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4355247131/10000000000 : ℝ)|^5663 ≤ (36251792897727/100000000000000 : ℝ)^4639
        have hw : |(4355247131/10000000000 : ℝ)|=(4355247131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_8 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1519299129/10000000000 : ℝ)*x 0 + (4895759293/10000000000 : ℝ)*x 1 + (5496220509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1519299129/10000000000 : ℝ)^5663 ≤ (5011543465609/50000000000000 : ℝ)^4639 := by
    have hnat : (1519299129 : ℕ)^5663*50000000000000^4639 ≤ 5011543465609^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519299129 10000000000 5011543465609 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4895759293/10000000000 : ℝ)^5663 ≤ (20908448167729/50000000000000 : ℝ)^4639 := by
    have hnat : (4895759293 : ℕ)^5663*50000000000000^4639 ≤ 20908448167729^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895759293 10000000000 20908448167729 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496220509/10000000000 : ℝ)^5663 ≤ (1505000522521/3125000000000 : ℝ)^4639 := by
    have hnat : (5496220509 : ℕ)^5663*3125000000000^4639 ≤ 1505000522521^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496220509 10000000000 1505000522521 3125000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1519299129/10000000000 : ℝ), (4895759293/10000000000 : ℝ), (5496220509/10000000000 : ℝ)] ![(5011543465609/50000000000000 : ℝ), (20908448167729/50000000000000 : ℝ), (1505000522521/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1519299129/10000000000 : ℝ)|^5663 ≤ (5011543465609/50000000000000 : ℝ)^4639
        have hw : |(-1519299129/10000000000 : ℝ)|=(1519299129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4895759293/10000000000 : ℝ)|^5663 ≤ (20908448167729/50000000000000 : ℝ)^4639
        have hw : |(4895759293/10000000000 : ℝ)|=(4895759293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496220509/10000000000 : ℝ)|^5663 ≤ (1505000522521/3125000000000 : ℝ)^4639
        have hw : |(5496220509/10000000000 : ℝ)|=(5496220509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_9 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152619967/10000000000 : ℝ)*x 0 + (-47027949/400000000 : ℝ)*x 1 + (2748110633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152619967/10000000000 : ℝ)^5663 ≤ (44510451115189/100000000000000 : ℝ)^4639 := by
    have hnat : (5152619967 : ℕ)^5663*100000000000000^4639 ≤ 44510451115189^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152619967 10000000000 44510451115189 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47027949/400000000 : ℝ)^5663 ≤ (1832381011469/25000000000000 : ℝ)^4639 := by
    have hnat : (47027949 : ℕ)^5663*25000000000000^4639 ≤ 1832381011469^4639*400000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47027949 400000000 1832381011469 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748110633/5000000000 : ℝ)^5663 ≤ (24080012408989/50000000000000 : ℝ)^4639 := by
    have hnat : (2748110633 : ℕ)^5663*50000000000000^4639 ≤ 24080012408989^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748110633 5000000000 24080012408989 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152619967/10000000000 : ℝ), (-47027949/400000000 : ℝ), (2748110633/5000000000 : ℝ)] ![(44510451115189/100000000000000 : ℝ), (1832381011469/25000000000000 : ℝ), (24080012408989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152619967/10000000000 : ℝ)|^5663 ≤ (44510451115189/100000000000000 : ℝ)^4639
        have hw : |(5152619967/10000000000 : ℝ)|=(5152619967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47027949/400000000 : ℝ)|^5663 ≤ (1832381011469/25000000000000 : ℝ)^4639
        have hw : |(-47027949/400000000 : ℝ)|=(47027949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748110633/5000000000 : ℝ)|^5663 ≤ (24080012408989/50000000000000 : ℝ)^4639
        have hw : |(2748110633/5000000000 : ℝ)|=(2748110633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_10 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152620149/10000000000 : ℝ)*x 0 + (2748110533/5000000000 : ℝ)*x 1 + (-235139751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152620149/10000000000 : ℝ)^5663 ≤ (44510453034421/100000000000000 : ℝ)^4639 := by
    have hnat : (5152620149 : ℕ)^5663*100000000000000^4639 ≤ 44510453034421^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152620149 10000000000 44510453034421 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748110533/5000000000 : ℝ)^5663 ≤ (48160022678663/100000000000000 : ℝ)^4639 := by
    have hnat : (2748110533 : ℕ)^5663*100000000000000^4639 ≤ 48160022678663^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748110533 5000000000 48160022678663 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235139751/2000000000 : ℝ)^5663 ≤ (1465904854837/20000000000000 : ℝ)^4639 := by
    have hnat : (235139751 : ℕ)^5663*20000000000000^4639 ≤ 1465904854837^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235139751 2000000000 1465904854837 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152620149/10000000000 : ℝ), (2748110533/5000000000 : ℝ), (-235139751/2000000000 : ℝ)] ![(44510453034421/100000000000000 : ℝ), (48160022678663/100000000000000 : ℝ), (1465904854837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152620149/10000000000 : ℝ)|^5663 ≤ (44510453034421/100000000000000 : ℝ)^4639
        have hw : |(5152620149/10000000000 : ℝ)|=(5152620149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748110533/5000000000 : ℝ)|^5663 ≤ (48160022678663/100000000000000 : ℝ)^4639
        have hw : |(2748110533/5000000000 : ℝ)|=(2748110533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235139751/2000000000 : ℝ)|^5663 ≤ (1465904854837/20000000000000 : ℝ)^4639
        have hw : |(-235139751/2000000000 : ℝ)|=(235139751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_11 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4778436343/10000000000 : ℝ)*x 0 + (3699245001/10000000000 : ℝ)*x 1 + (3699244533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4778436343/10000000000 : ℝ)^5663 ≤ (2537302572611/6250000000000 : ℝ)^4639 := by
    have hnat : (4778436343 : ℕ)^5663*6250000000000^4639 ≤ 2537302572611^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778436343 10000000000 2537302572611 6250000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3699245001/10000000000 : ℝ)^5663 ≤ (7425395427159/25000000000000 : ℝ)^4639 := by
    have hnat : (3699245001 : ℕ)^5663*25000000000000^4639 ≤ 7425395427159^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699245001 10000000000 7425395427159 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3699244533/10000000000 : ℝ)^5663 ≤ (1188063084863/4000000000000 : ℝ)^4639 := by
    have hnat : (3699244533 : ℕ)^5663*4000000000000^4639 ≤ 1188063084863^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699244533 10000000000 1188063084863 4000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4778436343/10000000000 : ℝ), (3699245001/10000000000 : ℝ), (3699244533/10000000000 : ℝ)] ![(2537302572611/6250000000000 : ℝ), (7425395427159/25000000000000 : ℝ), (1188063084863/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4778436343/10000000000 : ℝ)|^5663 ≤ (2537302572611/6250000000000 : ℝ)^4639
        have hw : |(4778436343/10000000000 : ℝ)|=(4778436343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3699245001/10000000000 : ℝ)|^5663 ≤ (7425395427159/25000000000000 : ℝ)^4639
        have hw : |(3699245001/10000000000 : ℝ)|=(3699245001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3699244533/10000000000 : ℝ)|^5663 ≤ (1188063084863/4000000000000 : ℝ)^4639
        have hw : |(3699244533/10000000000 : ℝ)|=(3699244533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_12 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-258086793/2500000000 : ℝ)*x 0 + (1130174219/2000000000 : ℝ)*x 1 + (5097216431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258086793/2500000000 : ℝ)^5663 ≤ (6253748435457/100000000000000 : ℝ)^4639 := by
    have hnat : (258086793 : ℕ)^5663*100000000000000^4639 ≤ 6253748435457^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258086793 2500000000 6253748435457 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130174219/2000000000 : ℝ)^5663 ≤ (24909674095543/50000000000000 : ℝ)^4639 := by
    have hnat : (1130174219 : ℕ)^5663*50000000000000^4639 ≤ 24909674095543^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130174219 2000000000 24909674095543 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097216431/10000000000 : ℝ)^5663 ≤ (43926903352651/100000000000000 : ℝ)^4639 := by
    have hnat : (5097216431 : ℕ)^5663*100000000000000^4639 ≤ 43926903352651^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097216431 10000000000 43926903352651 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258086793/2500000000 : ℝ), (1130174219/2000000000 : ℝ), (5097216431/10000000000 : ℝ)] ![(6253748435457/100000000000000 : ℝ), (24909674095543/50000000000000 : ℝ), (43926903352651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258086793/2500000000 : ℝ)|^5663 ≤ (6253748435457/100000000000000 : ℝ)^4639
        have hw : |(-258086793/2500000000 : ℝ)|=(258086793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130174219/2000000000 : ℝ)|^5663 ≤ (24909674095543/50000000000000 : ℝ)^4639
        have hw : |(1130174219/2000000000 : ℝ)|=(1130174219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097216431/10000000000 : ℝ)|^5663 ≤ (43926903352651/100000000000000 : ℝ)^4639
        have hw : |(5097216431/10000000000 : ℝ)|=(5097216431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_13 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420536233/10000000000 : ℝ)*x 0 + (-338916921/2500000000 : ℝ)*x 1 + (509721533/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420536233/10000000000 : ℝ)^5663 ≤ (47351689120999/100000000000000 : ℝ)^4639 := by
    have hnat : (5420536233 : ℕ)^5663*100000000000000^4639 ≤ 47351689120999^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420536233 10000000000 47351689120999 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338916921/2500000000 : ℝ)^5663 ≤ (8721419095163/100000000000000 : ℝ)^4639 := by
    have hnat : (338916921 : ℕ)^5663*100000000000000^4639 ≤ 8721419095163^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338916921 2500000000 8721419095163 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509721533/1000000000 : ℝ)^5663 ≤ (21963445885013/50000000000000 : ℝ)^4639 := by
    have hnat : (509721533 : ℕ)^5663*50000000000000^4639 ≤ 21963445885013^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509721533 1000000000 21963445885013 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420536233/10000000000 : ℝ), (-338916921/2500000000 : ℝ), (509721533/1000000000 : ℝ)] ![(47351689120999/100000000000000 : ℝ), (8721419095163/100000000000000 : ℝ), (21963445885013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420536233/10000000000 : ℝ)|^5663 ≤ (47351689120999/100000000000000 : ℝ)^4639
        have hw : |(5420536233/10000000000 : ℝ)|=(5420536233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338916921/2500000000 : ℝ)|^5663 ≤ (8721419095163/100000000000000 : ℝ)^4639
        have hw : |(-338916921/2500000000 : ℝ)|=(338916921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(509721533/1000000000 : ℝ)|^5663 ≤ (21963445885013/50000000000000 : ℝ)^4639
        have hw : |(509721533/1000000000 : ℝ)|=(509721533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_14 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420535779/10000000000 : ℝ)*x 0 + (2548608091/5000000000 : ℝ)*x 1 + (-1355667159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420535779/10000000000 : ℝ)^5663 ≤ (11837921069899/25000000000000 : ℝ)^4639 := by
    have hnat : (5420535779 : ℕ)^5663*25000000000000^4639 ≤ 11837921069899^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420535779 10000000000 11837921069899 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548608091/5000000000 : ℝ)^5663 ≤ (10981725183287/25000000000000 : ℝ)^4639 := by
    have hnat : (2548608091 : ℕ)^5663*25000000000000^4639 ≤ 10981725183287^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548608091 5000000000 10981725183287 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355667159/10000000000 : ℝ)^5663 ≤ (8721414972143/100000000000000 : ℝ)^4639 := by
    have hnat : (1355667159 : ℕ)^5663*100000000000000^4639 ≤ 8721414972143^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355667159 10000000000 8721414972143 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420535779/10000000000 : ℝ), (2548608091/5000000000 : ℝ), (-1355667159/10000000000 : ℝ)] ![(11837921069899/25000000000000 : ℝ), (10981725183287/25000000000000 : ℝ), (8721414972143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420535779/10000000000 : ℝ)|^5663 ≤ (11837921069899/25000000000000 : ℝ)^4639
        have hw : |(5420535779/10000000000 : ℝ)|=(5420535779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548608091/5000000000 : ℝ)|^5663 ≤ (10981725183287/25000000000000 : ℝ)^4639
        have hw : |(2548608091/5000000000 : ℝ)|=(2548608091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1355667159/10000000000 : ℝ)|^5663 ≤ (8721414972143/100000000000000 : ℝ)^4639
        have hw : |(-1355667159/10000000000 : ℝ)|=(1355667159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_box_15 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419882763/1250000000 : ℝ)*x 0 + (4409027291/10000000000 : ℝ)*x 1 + (4409028241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419882763/1250000000 : ℝ)^5663 ≤ (13200996617663/50000000000000 : ℝ)^4639 := by
    have hnat : (419882763 : ℕ)^5663*50000000000000^4639 ≤ 13200996617663^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419882763 1250000000 13200996617663 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4409027291/10000000000 : ℝ)^5663 ≤ (7359799707541/20000000000000 : ℝ)^4639 := by
    have hnat : (4409027291 : ℕ)^5663*20000000000000^4639 ≤ 7359799707541^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409027291 10000000000 7359799707541 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4409028241/10000000000 : ℝ)^5663 ≤ (7359801643379/20000000000000 : ℝ)^4639 := by
    have hnat : (4409028241 : ℕ)^5663*20000000000000^4639 ≤ 7359801643379^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409028241 10000000000 7359801643379 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419882763/1250000000 : ℝ), (4409027291/10000000000 : ℝ), (4409028241/10000000000 : ℝ)] ![(13200996617663/50000000000000 : ℝ), (7359799707541/20000000000000 : ℝ), (7359801643379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419882763/1250000000 : ℝ)|^5663 ≤ (13200996617663/50000000000000 : ℝ)^4639
        have hw : |(419882763/1250000000 : ℝ)|=(419882763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4409027291/10000000000 : ℝ)|^5663 ≤ (7359799707541/20000000000000 : ℝ)^4639
        have hw : |(4409027291/10000000000 : ℝ)|=(4409027291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4409028241/10000000000 : ℝ)|^5663 ≤ (7359801643379/20000000000000 : ℝ)^4639
        have hw : |(4409028241/10000000000 : ℝ)|=(4409028241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1743_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (566/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1789/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(4299/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57763/100000 : ℝ) ∧ (1623/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92767/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (566/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1789/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (566/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1789/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (566/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1789/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (566/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1789/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (566/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1789/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (566/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1789/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1789/20000 : ℝ) ^ (5647/1024 : ℝ) ≤ (33064669256181/20000000000000000000 : ℝ) := by
    have hpowers : (1789/20000 : ℝ)^5647 ≤ (33064669256181/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1789 : ℕ)^5647*20000000000000000000^1024 ≤ 33064669256181^1024*20000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1789 20000 33064669256181 20000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1789/20000 : ℝ)) (X := (33064669256181/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (566/3125 : ℝ) ^ (5647/1024 : ℝ) ≤ (2022486485538143/25000000000000000000 : ℝ) := by
    have hpowers : (566/3125 : ℝ)^5647 ≤ (2022486485538143/25000000000000000000 : ℝ)^1024 := by
      have hnat : (566 : ℕ)^5647*25000000000000000000^1024 ≤ 2022486485538143^1024*3125^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        566 3125 2022486485538143 25000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (566/3125 : ℝ)) (X := (2022486485538143/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000033064669256181/10000000000000000000 : ℝ) ≤ (10000005995781033/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (10000033064669256181/10000000000000000000 : ℝ)^1024 ≤ (10000005995781033/10000000000000000 : ℝ)^5647 := by
      have hnat : (10000033064669256181 : ℕ)^1024*10000000000000000^5647 ≤ 10000005995781033^5647*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000033064669256181 10000000000000000000 10000005995781033 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005995781033/10000000000000000 : ℝ)) (X := (10000033064669256181/10000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008255269288433477/100000000000000000000 : ℝ) ≤ (5000074846025437/5000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (100008255269288433477/100000000000000000000 : ℝ)^1024 ≤ (5000074846025437/5000000000000000 : ℝ)^5647 := by
      have hnat : (100008255269288433477 : ℕ)^1024*5000000000000000^5647 ≤ 5000074846025437^5647*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008255269288433477 100000000000000000000 5000074846025437 5000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000074846025437/5000000000000000 : ℝ)) (X := (100008255269288433477/100000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502022486485538143/12500000000000000000 : ℝ) ≤ (2000058677664143/2000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (12502022486485538143/12500000000000000000 : ℝ)^1024 ≤ (2000058677664143/2000000000000000 : ℝ)^5647 := by
      have hnat : (12502022486485538143 : ℕ)^1024*2000000000000000^5647 ≤ 2000058677664143^5647*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502022486485538143 12500000000000000000 2000058677664143 2000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000058677664143/2000000000000000 : ℝ)) (X := (12502022486485538143/12500000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33064669256181/20000000000000000000 : ℝ) ≤ ((91667484237057274021/91670000000000000000 : ℝ)+2*(143696269841/916700000000000 : ℝ)*(1789/20000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (91667484237057274021/91670000000000000000 : ℝ)+2*(143696269841/916700000000000 : ℝ)*(1789/20000 : ℝ)=(10000005995781033/10000000000000000 : ℝ) by norm_num, show 1+2*(33064669256181/20000000000000000000 : ℝ)=(10000033064669256181/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2022486485538143/25000000000000000000 : ℝ)+(33064669256181/20000000000000000000 : ℝ) ≤ ((91667484237057274021/91670000000000000000 : ℝ)+(143696269841/916700000000000 : ℝ)*((566/3125 : ℝ)+(1789/20000 : ℝ)))^(5647/1024 : ℝ) := by
    rw [show (91667484237057274021/91670000000000000000 : ℝ)+(143696269841/916700000000000 : ℝ)*((566/3125 : ℝ)+(1789/20000 : ℝ))=(5000074846025437/5000000000000000 : ℝ) by norm_num, show 1+(2022486485538143/25000000000000000000 : ℝ)+(33064669256181/20000000000000000000 : ℝ)=(100008255269288433477/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2022486485538143/25000000000000000000 : ℝ) ≤ ((91667484237057274021/91670000000000000000 : ℝ)+2*(143696269841/916700000000000 : ℝ)*(566/3125 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (91667484237057274021/91670000000000000000 : ℝ)+2*(143696269841/916700000000000 : ℝ)*(566/3125 : ℝ)=(2000058677664143/2000000000000000 : ℝ) by norm_num, show 1+2*(2022486485538143/25000000000000000000 : ℝ)=(12502022486485538143/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (91667484237057274021/91670000000000000000 : ℝ)*(X 1 0+X 2 0)+(143696269841/916700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (1789/20000 : ℝ)) (hi := (566/3125 : ℝ)) (c := (91667484237057274021/91670000000000000000 : ℝ)) (alpha := (143696269841/916700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (91667484237057274021/91670000000000000000 : ℝ)*(X 0 1+X 2 1)+(143696269841/916700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (1789/20000 : ℝ)) (hi := (566/3125 : ℝ)) (c := (91667484237057274021/91670000000000000000 : ℝ)) (alpha := (143696269841/916700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (91667484237057274021/91670000000000000000 : ℝ)*(X 0 2+X 1 2)+(143696269841/916700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (1789/20000 : ℝ)) (hi := (566/3125 : ℝ)) (c := (91667484237057274021/91670000000000000000 : ℝ)) (alpha := (143696269841/916700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-863693997/10000000000 : ℝ)*X 0 0+(1086606099/2000000000 : ℝ)*X 0 1+(5433030381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((129874707/250000000 : ℝ)*X 1 0+(-1205558829/10000000000 : ℝ)*X 1 1+(848911/1562500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5194988267/10000000000 : ℝ)*X 2 0+(5433030383/10000000000 : ℝ)*X 2 1+(-120555887/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4563445671/10000000000 : ℝ)*X 0 0+(3812040851/10000000000 : ℝ)*X 0 1+(3812040883/10000000000 : ℝ)*X 0 2+(4563445671/10000000000 : ℝ)*X 1 0+(3812040851/10000000000 : ℝ)*X 1 1+(3812040883/10000000000 : ℝ)*X 1 2+(4563445671/10000000000 : ℝ)*X 2 0+(3812040851/10000000000 : ℝ)*X 2 1+(3812040883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425304157/2500000000 : ℝ)*X 0 0+(5127579331/10000000000 : ℝ)*X 0 1+(5127579187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5400077981/10000000000 : ℝ)*X 1 0+(-1342720943/10000000000 : ℝ)*X 1 1+(2563789651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((675009731/1250000000 : ℝ)*X 2 0+(5127579391/10000000000 : ℝ)*X 2 1+(-268544201/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1736352027/5000000000 : ℝ)*X 0 0+(435524719/1000000000 : ℝ)*X 0 1+(4355247131/10000000000 : ℝ)*X 0 2+(1736352027/5000000000 : ℝ)*X 1 0+(435524719/1000000000 : ℝ)*X 1 1+(4355247131/10000000000 : ℝ)*X 1 2+(1736352027/5000000000 : ℝ)*X 2 0+(435524719/1000000000 : ℝ)*X 2 1+(4355247131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1519299129/10000000000 : ℝ)*X 0 0+(4895759293/10000000000 : ℝ)*X 0 1+(5496220509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152619967/10000000000 : ℝ)*X 1 0+(-47027949/400000000 : ℝ)*X 1 1+(2748110633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152620149/10000000000 : ℝ)*X 2 0+(2748110533/5000000000 : ℝ)*X 2 1+(-235139751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4778436343/10000000000 : ℝ)*X 0 0+(3699245001/10000000000 : ℝ)*X 0 1+(3699244533/10000000000 : ℝ)*X 0 2+(4778436343/10000000000 : ℝ)*X 1 0+(3699245001/10000000000 : ℝ)*X 1 1+(3699244533/10000000000 : ℝ)*X 1 2+(4778436343/10000000000 : ℝ)*X 2 0+(3699245001/10000000000 : ℝ)*X 2 1+(3699244533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-258086793/2500000000 : ℝ)*X 0 0+(1130174219/2000000000 : ℝ)*X 0 1+(5097216431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5420536233/10000000000 : ℝ)*X 1 0+(-338916921/2500000000 : ℝ)*X 1 1+(509721533/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5420535779/10000000000 : ℝ)*X 2 0+(2548608091/5000000000 : ℝ)*X 2 1+(-1355667159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((419882763/1250000000 : ℝ)*X 0 0+(4409027291/10000000000 : ℝ)*X 0 1+(4409028241/10000000000 : ℝ)*X 0 2+(419882763/1250000000 : ℝ)*X 1 0+(4409027291/10000000000 : ℝ)*X 1 1+(4409028241/10000000000 : ℝ)*X 1 2+(419882763/1250000000 : ℝ)*X 2 0+(4409027291/10000000000 : ℝ)*X 2 1+(4409028241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-4299/6250 : ℝ) ≤ (-630524299452257876644835979427911/916700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (739161/25000000000000 : ℝ)*(upper3) + (5819709/50000000000000 : ℝ)*(lower4) + (786441/5000000000000 : ℝ)*(lower5) + (205120449049303/20000000000000 : ℝ)*(major0) + (205120449049303/20000000000000 : ℝ)*(major1) + (205120449049303/20000000000000 : ℝ)*(major2) + (105626647/100000000000000 : ℝ)*(sp3) + (792400075355511/50000000000000 : ℝ)*(sp4) + (792398003068489/50000000000000 : ℝ)*(sp5) + (1584791392493423/100000000000000 : ℝ)*(sp6) + (489331489511333/100000000000000 : ℝ)*(sp7) + (33633461/50000000000000 : ℝ)*(sp8) + (2105920483/50000000000000 : ℝ)*(sp13) + (8825484521/100000000000000 : ℝ)*(sp14) + (24466579756899/5000000000000 : ℝ)*(f.failure) + (198100027247243/12500000000000 : ℝ)*(f.sum) + (1134081651717/2291750000000000000000000000 : ℝ)*base65 + (1936786856239357363/1833400000000000000000000000000000 : ℝ)*base67 + (5545307618530042637/1833400000000000000000000000000000 : ℝ)*base70 + (1924332129648642637/1833400000000000000000000000000000 : ℝ)*base72 + (112224292757/91670000000000000000000000 : ℝ)*base73 + (221769925088357363/1833400000000000000000000000000000 : ℝ)*base75 + (2868107903686442637/1833400000000000000000000000000000 : ℝ)*base78 + (2565075118046442637/1833400000000000000000000000000000 : ℝ)*base80 + (28844337737167/9167000000000000000000000000 : ℝ)*base82 + (636779/125000000000000000000 : ℝ)*base89 + (636779/125000000000000000000 : ℝ)*base91 + (636779/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57763/100000 : ℝ) ≤ (264767109917863120080234470356221/458350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24793/390625000000 : ℝ)*(upper2) + (794479/100000000000000 : ℝ)*(upper3) + (51829/3125000000000 : ℝ)*(lower5) + (114497898343933/10000000000000 : ℝ)*(major0) + (114497898343933/10000000000000 : ℝ)*(major1) + (114497898343933/10000000000000 : ℝ)*(major2) + (53887951738907/3125000000000 : ℝ)*(sp0) + (862207328043979/50000000000000 : ℝ)*(sp1) + (431103469921443/25000000000000 : ℝ)*(sp2) + (27314401843961/5000000000000 : ℝ)*(sp3) + (3296721/10000000000000 : ℝ)*(sp5) + (37829283/25000000000000 : ℝ)*(sp7) + (233410143/100000000000000 : ℝ)*(sp8) + (161873879/20000000000000 : ℝ)*(sp10) + (546288188196353/100000000000000 : ℝ)*(f.failure) + (26943979516487/1562500000000 : ℝ)*(f.sum) + (8206521537803/1833400000000000000000000000 : ℝ)*base65 + (10043745512370135407/916700000000000000000000000000000 : ℝ)*base68 + (5400994473783064593/916700000000000000000000000000000 : ℝ)*base69 + (12587400082564593/916700000000000000000000000000000 : ℝ)*base71 + (4902942456239/916700000000000000000000000 : ℝ)*base74 + (1217500404923235407/916700000000000000000000000000000 : ℝ)*base76 + (8654646727108264593/916700000000000000000000000000000 : ℝ)*base77 + (1154872558880964593/916700000000000000000000000000000 : ℝ)*base79 + (18483847385577/9167000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (26252713/2500000000000000000000 : ℝ)*base89 + (26252713/2500000000000000000000 : ℝ)*base91 + (26252713/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (1623/2000 : ℝ) ≤ (3719606031077735260012138767836121/4583500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18305547/100000000000000 : ℝ)*(upper0) + (4211287/50000000000000 : ℝ)*(upper1) + (1977133/5000000000000 : ℝ)*(upper3) + (15047373/50000000000000 : ℝ)*(upper4) + (1111336977653367/100000000000000 : ℝ)*(major0) + (1111336977653367/100000000000000 : ℝ)*(major1) + (1111336977653367/100000000000000 : ℝ)*(major2) + (3005170117/20000000000000 : ℝ)*(sp1) + (14975107267/100000000000000 : ℝ)*(sp2) + (311165657/25000000000000 : ℝ)*(sp3) + (416346555350069/25000000000000 : ℝ)*(sp8) + (416342798887423/25000000000000 : ℝ)*(sp9) + (166537124629301/10000000000000 : ℝ)*(sp10) + (530235792679497/100000000000000 : ℝ)*(sp11) + (4241896298737/800000000000 : ℝ)*(f.failure) + (416346555350069/25000000000000 : ℝ)*(f.sum) + (75291763605861/22917500000000000000000000000 : ℝ)*base65 + (5127698750505978707/9167000000000000000000000000000000 : ℝ)*base67 + (46589720377866021293/9167000000000000000000000000000000 : ℝ)*base70 + (41435720511504021293/9167000000000000000000000000000000 : ℝ)*base72 + (249098067532547/45835000000000000000000000000 : ℝ)*base73 + (85489642759062021293/9167000000000000000000000000000000 : ℝ)*base76 + (72321642732609021293/9167000000000000000000000000000000 : ℝ)*base78 + (9107303805654978707/9167000000000000000000000000000000 : ℝ)*base79 + (32143249255957/11458750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (73177/20000000000000000000 : ℝ)*base89 + (73177/20000000000000000000 : ℝ)*base91 + (73177/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-92767/100000 : ℝ) ≤ (-4251871481921591074811894079280131/4583500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1744819/2500000000000 : ℝ)*(lower3) + (321567/5000000000000 : ℝ)*(lower4) + (15022463/50000000000000 : ℝ)*(upper5) + (1165722094700879/100000000000000 : ℝ)*(major0) + (1165722094700879/100000000000000 : ℝ)*(major1) + (1165722094700879/100000000000000 : ℝ)*(major2) + (1716340073/100000000000000 : ℝ)*(sp4) + (22111569813/50000000000000 : ℝ)*(sp5) + (7284973881/100000000000000 : ℝ)*(sp6) + (10588443979/100000000000000 : ℝ)*(sp7) + (225772373086581/12500000000000 : ℝ)*(sp12) + (361227295578619/20000000000000 : ℝ)*(sp13) + (45154335401471/2500000000000 : ℝ)*(sp14) + (556174477190759/100000000000000 : ℝ)*(sp15) + (278092532817369/50000000000000 : ℝ)*(f.failure) + (1806180701032721/100000000000000 : ℝ)*(f.sum) + (262630984611069/45835000000000000000000000000 : ℝ)*base65 + (8212614684622464459/9167000000000000000000000000000000 : ℝ)*base67 + (80383071840287464459/9167000000000000000000000000000000 : ℝ)*base69 + (65414140621975464459/9167000000000000000000000000000000 : ℝ)*base71 + (740622794611/716171875000000000000000000 : ℝ)*base73 + (19244613626966464459/9167000000000000000000000000000000 : ℝ)*base75 + (33909561478406464459/9167000000000000000000000000000000 : ℝ)*base77 + (19423904929746464459/9167000000000000000000000000000000 : ℝ)*base79 + (127746533965367/22917500000000000000000000000 : ℝ)*base81 + (15736351/1250000000000000000000 : ℝ)*base90 + (15736351/1250000000000000000000 : ℝ)*base92 + (15736351/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1743_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (566/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1789/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(4299/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(57763/100000 : ℝ) else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (92767/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1743_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1743_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(4299/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(57763/100000 : ℝ) else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (92767/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1743_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1743_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(4299/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(57763/100000 : ℝ) else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (92767/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1743_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

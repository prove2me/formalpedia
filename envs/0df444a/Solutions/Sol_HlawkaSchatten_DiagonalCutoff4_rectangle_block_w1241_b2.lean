-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:19:23.443848+00:00
-- url     : https://prove2.me/submissions/f086732a-ccf1-4709-9814-532cb79b1f2a

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
theorem support_rectangle_w1241_s6_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-212040647/1000000000 : ℝ)*x 0 + (5391413353/10000000000 : ℝ)*x 1 + (1316753667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212040647/1000000000 : ℝ)^4217 ≤ (12894386954759/100000000000000 : ℝ)^3193 := by
    have hnat : (212040647 : ℕ)^4217*100000000000000^3193 ≤ 12894386954759^3193*1000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212040647 1000000000 12894386954759 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391413353/10000000000 : ℝ)^4217 ≤ (4422412527643/10000000000000 : ℝ)^3193 := by
    have hnat : (5391413353 : ℕ)^4217*10000000000000^3193 ≤ 4422412527643^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391413353 10000000000 4422412527643 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316753667/2500000000 : ℝ)^4217 ≤ (42881487754021/100000000000000 : ℝ)^3193 := by
    have hnat : (1316753667 : ℕ)^4217*100000000000000^3193 ≤ 42881487754021^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316753667 2500000000 42881487754021 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212040647/1000000000 : ℝ), (5391413353/10000000000 : ℝ), (1316753667/2500000000 : ℝ)] ![(12894386954759/100000000000000 : ℝ), (4422412527643/10000000000000 : ℝ), (42881487754021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212040647/1000000000 : ℝ)|^4217 ≤ (12894386954759/100000000000000 : ℝ)^3193
        have hw : |(-212040647/1000000000 : ℝ)|=(212040647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391413353/10000000000 : ℝ)|^4217 ≤ (4422412527643/10000000000000 : ℝ)^3193
        have hw : |(5391413353/10000000000 : ℝ)|=(5391413353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316753667/2500000000 : ℝ)|^4217 ≤ (42881487754021/100000000000000 : ℝ)^3193
        have hw : |(1316753667/2500000000 : ℝ)|=(1316753667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344364063/10000000000 : ℝ)*x 0 + (-1091741359/5000000000 : ℝ)*x 1 + (1053402933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344364063/10000000000 : ℝ)^4217 ≤ (10928785057743/25000000000000 : ℝ)^3193 := by
    have hnat : (5344364063 : ℕ)^4217*25000000000000^3193 ≤ 10928785057743^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344364063 10000000000 10928785057743 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091741359/5000000000 : ℝ)^4217 ≤ (6701686017801/50000000000000 : ℝ)^3193 := by
    have hnat : (1091741359 : ℕ)^4217*50000000000000^3193 ≤ 6701686017801^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091741359 5000000000 6701686017801 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053402933/2000000000 : ℝ)^4217 ≤ (42881487721763/100000000000000 : ℝ)^3193 := by
    have hnat : (1053402933 : ℕ)^4217*100000000000000^3193 ≤ 42881487721763^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053402933 2000000000 42881487721763 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344364063/10000000000 : ℝ), (-1091741359/5000000000 : ℝ), (1053402933/2000000000 : ℝ)] ![(10928785057743/25000000000000 : ℝ), (6701686017801/50000000000000 : ℝ), (42881487721763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344364063/10000000000 : ℝ)|^4217 ≤ (10928785057743/25000000000000 : ℝ)^3193
        have hw : |(5344364063/10000000000 : ℝ)|=(5344364063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091741359/5000000000 : ℝ)|^4217 ≤ (6701686017801/50000000000000 : ℝ)^3193
        have hw : |(-1091741359/5000000000 : ℝ)|=(1091741359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053402933/2000000000 : ℝ)|^4217 ≤ (42881487721763/100000000000000 : ℝ)^3193
        have hw : |(1053402933/2000000000 : ℝ)|=(1053402933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344364079/10000000000 : ℝ)*x 0 + (2633507329/5000000000 : ℝ)*x 1 + (-1091741353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344364079/10000000000 : ℝ)^4217 ≤ (21857570201909/50000000000000 : ℝ)^3193 := by
    have hnat : (5344364079 : ℕ)^4217*50000000000000^3193 ≤ 21857570201909^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344364079 10000000000 21857570201909 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633507329/5000000000 : ℝ)^4217 ≤ (1340046488953/3125000000000 : ℝ)^3193 := by
    have hnat : (2633507329 : ℕ)^4217*3125000000000^3193 ≤ 1340046488953^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633507329 5000000000 1340046488953 3125000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091741353/5000000000 : ℝ)^4217 ≤ (3350842984579/25000000000000 : ℝ)^3193 := by
    have hnat : (1091741353 : ℕ)^4217*25000000000000^3193 ≤ 3350842984579^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091741353 5000000000 3350842984579 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344364079/10000000000 : ℝ), (2633507329/5000000000 : ℝ), (-1091741353/5000000000 : ℝ)] ![(21857570201909/50000000000000 : ℝ), (1340046488953/3125000000000 : ℝ), (3350842984579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344364079/10000000000 : ℝ)|^4217 ≤ (21857570201909/50000000000000 : ℝ)^3193
        have hw : |(5344364079/10000000000 : ℝ)|=(5344364079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633507329/5000000000 : ℝ)|^4217 ≤ (1340046488953/3125000000000 : ℝ)^3193
        have hw : |(2633507329/5000000000 : ℝ)|=(2633507329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091741353/5000000000 : ℝ)|^4217 ≤ (3350842984579/25000000000000 : ℝ)^3193
        have hw : |(-1091741353/5000000000 : ℝ)|=(1091741353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350900611/10000000000 : ℝ)*x 0 + (42265277/100000000 : ℝ)*x 1 + (447883049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350900611/10000000000 : ℝ)^4217 ≤ (33317387926771/100000000000000 : ℝ)^3193 := by
    have hnat : (4350900611 : ℕ)^4217*100000000000000^3193 ≤ 33317387926771^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350900611 10000000000 33317387926771 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42265277/100000000 : ℝ)^4217 ≤ (3206536032473/10000000000000 : ℝ)^3193 := by
    have hnat : (42265277 : ℕ)^4217*10000000000000^3193 ≤ 3206536032473^3193*100000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42265277 100000000 3206536032473 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447883049/1000000000 : ℝ)^4217 ≤ (6923450347573/20000000000000 : ℝ)^3193 := by
    have hnat : (447883049 : ℕ)^4217*20000000000000^3193 ≤ 6923450347573^3193*1000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447883049 1000000000 6923450347573 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350900611/10000000000 : ℝ), (42265277/100000000 : ℝ), (447883049/1000000000 : ℝ)] ![(33317387926771/100000000000000 : ℝ), (3206536032473/10000000000000 : ℝ), (6923450347573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350900611/10000000000 : ℝ)|^4217 ≤ (33317387926771/100000000000000 : ℝ)^3193
        have hw : |(4350900611/10000000000 : ℝ)|=(4350900611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42265277/100000000 : ℝ)|^4217 ≤ (3206536032473/10000000000000 : ℝ)^3193
        have hw : |(42265277/100000000 : ℝ)|=(42265277/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447883049/1000000000 : ℝ)|^4217 ≤ (6923450347573/20000000000000 : ℝ)^3193
        have hw : |(447883049/1000000000 : ℝ)|=(447883049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120411029/10000000000 : ℝ)*x 0 + (5267329343/10000000000 : ℝ)*x 1 + (5391097639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120411029/10000000000 : ℝ)^4217 ≤ (12894423569503/100000000000000 : ℝ)^3193 := by
    have hnat : (2120411029 : ℕ)^4217*100000000000000^3193 ≤ 12894423569503^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120411029 10000000000 12894423569503 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267329343/10000000000 : ℝ)^4217 ≤ (21442435666821/50000000000000 : ℝ)^3193 := by
    have hnat : (5267329343 : ℕ)^4217*50000000000000^3193 ≤ 21442435666821^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267329343 10000000000 21442435666821 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391097639/10000000000 : ℝ)^4217 ≤ (44220705079863/100000000000000 : ℝ)^3193 := by
    have hnat : (5391097639 : ℕ)^4217*100000000000000^3193 ≤ 44220705079863^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391097639 10000000000 44220705079863 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120411029/10000000000 : ℝ), (5267329343/10000000000 : ℝ), (5391097639/10000000000 : ℝ)] ![(12894423569503/100000000000000 : ℝ), (21442435666821/50000000000000 : ℝ), (44220705079863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120411029/10000000000 : ℝ)|^4217 ≤ (12894423569503/100000000000000 : ℝ)^3193
        have hw : |(-2120411029/10000000000 : ℝ)|=(2120411029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267329343/10000000000 : ℝ)|^4217 ≤ (21442435666821/50000000000000 : ℝ)^3193
        have hw : |(5267329343/10000000000 : ℝ)|=(5267329343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391097639/10000000000 : ℝ)|^4217 ≤ (44220705079863/100000000000000 : ℝ)^3193
        have hw : |(5391097639/10000000000 : ℝ)|=(5391097639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656312493/5000000000 : ℝ)*x 0 + (-2059400089/10000000000 : ℝ)*x 1 + (53910977/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656312493/5000000000 : ℝ)^4217 ≤ (43372592979809/100000000000000 : ℝ)^3193 := by
    have hnat : (2656312493 : ℕ)^4217*100000000000000^3193 ≤ 43372592979809^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656312493 5000000000 43372592979809 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059400089/10000000000 : ℝ)^4217 ≤ (1550837658323/12500000000000 : ℝ)^3193 := by
    have hnat : (2059400089 : ℕ)^4217*12500000000000^3193 ≤ 1550837658323^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059400089 10000000000 1550837658323 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53910977/100000000 : ℝ)^4217 ≤ (22110352870341/50000000000000 : ℝ)^3193 := by
    have hnat : (53910977 : ℕ)^4217*50000000000000^3193 ≤ 22110352870341^3193*100000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53910977 100000000 22110352870341 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656312493/5000000000 : ℝ), (-2059400089/10000000000 : ℝ), (53910977/100000000 : ℝ)] ![(43372592979809/100000000000000 : ℝ), (1550837658323/12500000000000 : ℝ), (22110352870341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656312493/5000000000 : ℝ)|^4217 ≤ (43372592979809/100000000000000 : ℝ)^3193
        have hw : |(2656312493/5000000000 : ℝ)|=(2656312493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059400089/10000000000 : ℝ)|^4217 ≤ (1550837658323/12500000000000 : ℝ)^3193
        have hw : |(-2059400089/10000000000 : ℝ)|=(2059400089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53910977/100000000 : ℝ)|^4217 ≤ (22110352870341/50000000000000 : ℝ)^3193
        have hw : |(53910977/100000000 : ℝ)|=(53910977/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312624641/10000000000 : ℝ)*x 0 + (1078219593/2000000000 : ℝ)*x 1 + (-411880039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312624641/10000000000 : ℝ)^4217 ≤ (43372589259919/100000000000000 : ℝ)^3193 := by
    have hnat : (5312624641 : ℕ)^4217*100000000000000^3193 ≤ 43372589259919^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312624641 10000000000 43372589259919 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078219593/2000000000 : ℝ)^4217 ≤ (44220708611457/100000000000000 : ℝ)^3193 := by
    have hnat : (1078219593 : ℕ)^4217*100000000000000^3193 ≤ 44220708611457^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078219593 2000000000 44220708611457 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411880039/2000000000 : ℝ)^4217 ≤ (1240670210997/10000000000000 : ℝ)^3193 := by
    have hnat : (411880039 : ℕ)^4217*10000000000000^3193 ≤ 1240670210997^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411880039 2000000000 1240670210997 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312624641/10000000000 : ℝ), (1078219593/2000000000 : ℝ), (-411880039/2000000000 : ℝ)] ![(43372589259919/100000000000000 : ℝ), (44220708611457/100000000000000 : ℝ), (1240670210997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312624641/10000000000 : ℝ)|^4217 ≤ (43372589259919/100000000000000 : ℝ)^3193
        have hw : |(5312624641/10000000000 : ℝ)|=(5312624641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078219593/2000000000 : ℝ)|^4217 ≤ (44220708611457/100000000000000 : ℝ)^3193
        have hw : |(1078219593/2000000000 : ℝ)|=(1078219593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411880039/2000000000 : ℝ)|^4217 ≤ (1240670210997/10000000000000 : ℝ)^3193
        have hw : |(-411880039/2000000000 : ℝ)|=(411880039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s6_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087727509/2500000000 : ℝ)*x 0 + (4478192469/10000000000 : ℝ)*x 1 + (4227168151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087727509/2500000000 : ℝ)^4217 ≤ (33317483245441/100000000000000 : ℝ)^3193 := by
    have hnat : (1087727509 : ℕ)^4217*100000000000000^3193 ≤ 33317483245441^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087727509 2500000000 33317483245441 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478192469/10000000000 : ℝ)^4217 ≤ (865268477213/2500000000000 : ℝ)^3193 := by
    have hnat : (4478192469 : ℕ)^4217*2500000000000^3193 ≤ 865268477213^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478192469 10000000000 865268477213 2500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227168151/10000000000 : ℝ)^4217 ≤ (32071777642537/100000000000000 : ℝ)^3193 := by
    have hnat : (4227168151 : ℕ)^4217*100000000000000^3193 ≤ 32071777642537^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227168151 10000000000 32071777642537 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087727509/2500000000 : ℝ), (4478192469/10000000000 : ℝ), (4227168151/10000000000 : ℝ)] ![(33317483245441/100000000000000 : ℝ), (865268477213/2500000000000 : ℝ), (32071777642537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087727509/2500000000 : ℝ)|^4217 ≤ (33317483245441/100000000000000 : ℝ)^3193
        have hw : |(1087727509/2500000000 : ℝ)|=(1087727509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478192469/10000000000 : ℝ)|^4217 ≤ (865268477213/2500000000000 : ℝ)^3193
        have hw : |(4478192469/10000000000 : ℝ)|=(4478192469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227168151/10000000000 : ℝ)|^4217 ≤ (32071777642537/100000000000000 : ℝ)^3193
        have hw : |(4227168151/10000000000 : ℝ)|=(4227168151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11473/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3527/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1413/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2863/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1413/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2863/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1413/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2863/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1413/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2863/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1413/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2863/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1413/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2863/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2863/25000 : ℝ) ^ (8433/2048 : ℝ) ≤ (13328414296595329/100000000000000000000 : ℝ) := by
    have hpowers : (2863/25000 : ℝ)^8433 ≤ (13328414296595329/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2863 : ℕ)^8433*100000000000000000000^2048 ≤ 13328414296595329^2048*25000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2863 25000 13328414296595329 100000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2863/25000 : ℝ)) (X := (13328414296595329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1413/10000 : ℝ) ^ (8433/2048 : ℝ) ≤ (6332729795910801/20000000000000000000 : ℝ) := by
    have hpowers : (1413/10000 : ℝ)^8433 ≤ (6332729795910801/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1413 : ℕ)^8433*20000000000000000000^2048 ≤ 6332729795910801^2048*10000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1413 10000 6332729795910801 20000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1413/10000 : ℝ)) (X := (6332729795910801/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013328414296595329/50000000000000000000 : ℝ) ≤ (5000323655143649/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50013328414296595329/50000000000000000000 : ℝ)^2048 ≤ (5000323655143649/5000000000000000 : ℝ)^8433 := by
      have hnat : (50013328414296595329 : ℕ)^2048*5000000000000000^8433 ≤ 5000323655143649^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013328414296595329 50000000000000000000 5000323655143649 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000323655143649/5000000000000000 : ℝ)) (X := (50013328414296595329/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022496031638074667/50000000000000000000 : ℝ) ≤ (5000546235355819/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50022496031638074667/50000000000000000000 : ℝ)^2048 ≤ (5000546235355819/5000000000000000 : ℝ)^8433 := by
      have hnat : (50022496031638074667 : ℕ)^2048*5000000000000000^8433 ≤ 5000546235355819^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022496031638074667 50000000000000000000 5000546235355819 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000546235355819/5000000000000000 : ℝ)) (X := (50022496031638074667/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006332729795910801/10000000000000000000 : ℝ) ≤ (5000768815567989/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (10006332729795910801/10000000000000000000 : ℝ)^2048 ≤ (5000768815567989/5000000000000000 : ℝ)^8433 := by
      have hnat : (10006332729795910801 : ℕ)^2048*5000000000000000^8433 ≤ 5000768815567989^8433*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006332729795910801 10000000000000000000 5000768815567989 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000768815567989/5000000000000000 : ℝ)) (X := (10006332729795910801/10000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13328414296595329/100000000000000000000 : ℝ) ≤ ((6692884385647575171/6695000000000000000 : ℝ)+2*(22258021217/13390000000000 : ℝ)*(2863/25000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (6692884385647575171/6695000000000000000 : ℝ)+2*(22258021217/13390000000000 : ℝ)*(2863/25000 : ℝ)=(5000323655143649/5000000000000000 : ℝ) by norm_num, show 1+2*(13328414296595329/100000000000000000000 : ℝ)=(50013328414296595329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6332729795910801/20000000000000000000 : ℝ)+(13328414296595329/100000000000000000000 : ℝ) ≤ ((6692884385647575171/6695000000000000000 : ℝ)+(22258021217/13390000000000 : ℝ)*((1413/10000 : ℝ)+(2863/25000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (6692884385647575171/6695000000000000000 : ℝ)+(22258021217/13390000000000 : ℝ)*((1413/10000 : ℝ)+(2863/25000 : ℝ))=(5000546235355819/5000000000000000 : ℝ) by norm_num, show 1+(6332729795910801/20000000000000000000 : ℝ)+(13328414296595329/100000000000000000000 : ℝ)=(50022496031638074667/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6332729795910801/20000000000000000000 : ℝ) ≤ ((6692884385647575171/6695000000000000000 : ℝ)+2*(22258021217/13390000000000 : ℝ)*(1413/10000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (6692884385647575171/6695000000000000000 : ℝ)+2*(22258021217/13390000000000 : ℝ)*(1413/10000 : ℝ)=(5000768815567989/5000000000000000 : ℝ) by norm_num, show 1+2*(6332729795910801/20000000000000000000 : ℝ)=(10006332729795910801/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6692884385647575171/6695000000000000000 : ℝ)*(X 1 0+X 2 0)+(22258021217/13390000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (2863/25000 : ℝ)) (hi := (1413/10000 : ℝ)) (c := (6692884385647575171/6695000000000000000 : ℝ)) (alpha := (22258021217/13390000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6692884385647575171/6695000000000000000 : ℝ)*(X 0 1+X 2 1)+(22258021217/13390000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (2863/25000 : ℝ)) (hi := (1413/10000 : ℝ)) (c := (6692884385647575171/6695000000000000000 : ℝ)) (alpha := (22258021217/13390000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6692884385647575171/6695000000000000000 : ℝ)*(X 0 2+X 1 2)+(22258021217/13390000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (2863/25000 : ℝ)) (hi := (1413/10000 : ℝ)) (c := (6692884385647575171/6695000000000000000 : ℝ)) (alpha := (22258021217/13390000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212040647/1000000000 : ℝ)*X 0 0+(5391413353/10000000000 : ℝ)*X 0 1+(1316753667/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344364063/10000000000 : ℝ)*X 1 0+(-1091741359/5000000000 : ℝ)*X 1 1+(1053402933/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344364079/10000000000 : ℝ)*X 2 0+(2633507329/5000000000 : ℝ)*X 2 1+(-1091741353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350900611/10000000000 : ℝ)*X 0 0+(42265277/100000000 : ℝ)*X 0 1+(447883049/1000000000 : ℝ)*X 0 2+(4350900611/10000000000 : ℝ)*X 1 0+(42265277/100000000 : ℝ)*X 1 1+(447883049/1000000000 : ℝ)*X 1 2+(4350900611/10000000000 : ℝ)*X 2 0+(42265277/100000000 : ℝ)*X 2 1+(447883049/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120411029/10000000000 : ℝ)*X 0 0+(5267329343/10000000000 : ℝ)*X 0 1+(5391097639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656312493/5000000000 : ℝ)*X 1 0+(-2059400089/10000000000 : ℝ)*X 1 1+(53910977/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312624641/10000000000 : ℝ)*X 2 0+(1078219593/2000000000 : ℝ)*X 2 1+(-411880039/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087727509/2500000000 : ℝ)*X 0 0+(4478192469/10000000000 : ℝ)*X 0 1+(4227168151/10000000000 : ℝ)*X 0 2+(1087727509/2500000000 : ℝ)*X 1 0+(4478192469/10000000000 : ℝ)*X 1 1+(4227168151/10000000000 : ℝ)*X 1 2+(1087727509/2500000000 : ℝ)*X 2 0+(4478192469/10000000000 : ℝ)*X 2 1+(4227168151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113140914977368588222409997/16737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332251819/25000000000000 : ℝ)*(base19) + (25061549/2000000000000 : ℝ)*(base23) + (53441653/100000000000000 : ℝ)*(lower2) + (41217033/25000000000000 : ℝ)*(upper3) + (5775891/5000000000000 : ℝ)*(upper5) + (300056851105731/5000000000000 : ℝ)*(major0) + (300056851105731/5000000000000 : ℝ)*(major1) + (300056851105731/5000000000000 : ℝ)*(major2) + (4019353916489847/50000000000000 : ℝ)*(sp0) + (200968592899089/2500000000000 : ℝ)*(sp1) + (4019371895946693/50000000000000 : ℝ)*(sp2) + (1981754659609577/50000000000000 : ℝ)*(sp3) + (18605995571/50000000000000 : ℝ)*(sp4) + (19454715037/100000000000000 : ℝ)*(sp7) + (247720548370887/6250000000000 : ℝ)*(f.failure) + (1607749008994167/20000000000000 : ℝ)*(f.sum) + (23009498209/41843750000000000000000000 : ℝ)*base65 + (142924470827430001/33475000000000000000000000000000 : ℝ)*base67 + (185662833090169999/33475000000000000000000000000000 : ℝ)*base70 + (127569392421555001/33475000000000000000000000000000 : ℝ)*base71 + (6217263513333/1339000000000000000000000000 : ℝ)*base73 + (666063616116580001/33475000000000000000000000000000 : ℝ)*base75 + (8156240817094999/33475000000000000000000000000000 : ℝ)*base78 + (279732835734930001/33475000000000000000000000000000 : ℝ)*base79 + (3834722623071/1339000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2357559/625000000000000000000 : ℝ)*base90 + (2357559/625000000000000000000 : ℝ)*base92 + (2357559/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360713081982156810408233211/167375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14602047/12500000000000 : ℝ)*(base8) + (594676531/100000000000000 : ℝ)*(base21) + (51505123/25000000000000 : ℝ)*(base29) + (8672247/10000000000000 : ℝ)*(upper3) + (1399337/25000000000000 : ℝ)*(upper5) + (6031658011303761/100000000000000 : ℝ)*(major0) + (6031658217324253/100000000000000 : ℝ)*(major1) + (6031658217324253/100000000000000 : ℝ)*(major2) + (6865170577/100000000000000 : ℝ)*(sp0) + (2197352571/100000000000000 : ℝ)*(sp3) + (8079622487689883/100000000000000 : ℝ)*(sp4) + (8079629263656341/100000000000000 : ℝ)*(sp5) + (2019907167244953/25000000000000 : ℝ)*(sp6) + (1991842347890887/50000000000000 : ℝ)*(sp7) + (1991843446567173/50000000000000 : ℝ)*(f.failure) + (2019907367419209/25000000000000 : ℝ)*(f.sum) + (1566295919343/133900000000000000000000000 : ℝ)*base65 + (8958223433857422263/669500000000000000000000000000000 : ℝ)*base67 + (2207219035127922263/669500000000000000000000000000000 : ℝ)*base69 + (11466651795828518131/669500000000000000000000000000000 : ℝ)*base71 + (1653265235403/267800000000000000000000000 : ℝ)*base73 + (13614633110669422263/669500000000000000000000000000000 : ℝ)*base75 + (10391727346758481869/669500000000000000000000000000000 : ℝ)*base78 + (10149318569890422263/669500000000000000000000000000000 : ℝ)*base79 + (907014002601/669500000000000000000000000 : ℝ)*base81 + (3/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7571861/5000000000000000000000 : ℝ)*base90 + (7571861/5000000000000000000000 : ℝ)*base92 + (7571861/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1241_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1241_s7_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120423553/10000000000 : ℝ)*x 0 + (5391212859/10000000000 : ℝ)*x 1 + (5267203907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120423553/10000000000 : ℝ)^4217 ≤ (2578904830753/20000000000000 : ℝ)^3193 := by
    have hnat : (2120423553 : ℕ)^4217*20000000000000^3193 ≤ 2578904830753^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120423553 10000000000 2578904830753 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391212859/10000000000 : ℝ)^4217 ≤ (2211097663753/5000000000000 : ℝ)^3193 := by
    have hnat : (5391212859 : ℕ)^4217*5000000000000^3193 ≤ 2211097663753^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391212859 10000000000 2211097663753 5000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267203907/10000000000 : ℝ)^4217 ≤ (42883522560659/100000000000000 : ℝ)^3193 := by
    have hnat : (5267203907 : ℕ)^4217*100000000000000^3193 ≤ 42883522560659^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267203907 10000000000 42883522560659 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120423553/10000000000 : ℝ), (5391212859/10000000000 : ℝ), (5267203907/10000000000 : ℝ)] ![(2578904830753/20000000000000 : ℝ), (2211097663753/5000000000000 : ℝ), (42883522560659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120423553/10000000000 : ℝ)|^4217 ≤ (2578904830753/20000000000000 : ℝ)^3193
        have hw : |(-2120423553/10000000000 : ℝ)|=(2120423553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391212859/10000000000 : ℝ)|^4217 ≤ (2211097663753/5000000000000 : ℝ)^3193
        have hw : |(5391212859/10000000000 : ℝ)|=(5391212859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267203907/10000000000 : ℝ)|^4217 ≤ (42883522560659/100000000000000 : ℝ)^3193
        have hw : |(5267203907/10000000000 : ℝ)|=(5267203907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336077877/2500000000 : ℝ)*x 0 + (-2183296777/10000000000 : ℝ)*x 1 + (5267207659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336077877/2500000000 : ℝ)^4217 ≤ (43714572485239/100000000000000 : ℝ)^3193 := by
    have hnat : (1336077877 : ℕ)^4217*100000000000000^3193 ≤ 43714572485239^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336077877 2500000000 43714572485239 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183296777/10000000000 : ℝ)^4217 ≤ (21442983363/160000000000 : ℝ)^3193 := by
    have hnat : (2183296777 : ℕ)^4217*160000000000^3193 ≤ 21442983363^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183296777 10000000000 21442983363 160000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267207659/10000000000 : ℝ)^4217 ≤ (42883562904559/100000000000000 : ℝ)^3193 := by
    have hnat : (5267207659 : ℕ)^4217*100000000000000^3193 ≤ 42883562904559^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267207659 10000000000 42883562904559 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336077877/2500000000 : ℝ), (-2183296777/10000000000 : ℝ), (5267207659/10000000000 : ℝ)] ![(43714572485239/100000000000000 : ℝ), (21442983363/160000000000 : ℝ), (42883562904559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336077877/2500000000 : ℝ)|^4217 ≤ (43714572485239/100000000000000 : ℝ)^3193
        have hw : |(1336077877/2500000000 : ℝ)|=(1336077877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2183296777/10000000000 : ℝ)|^4217 ≤ (21442983363/160000000000 : ℝ)^3193
        have hw : |(-2183296777/10000000000 : ℝ)|=(2183296777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267207659/10000000000 : ℝ)|^4217 ≤ (42883562904559/100000000000000 : ℝ)^3193
        have hw : |(5267207659/10000000000 : ℝ)|=(5267207659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068862933/2000000000 : ℝ)*x 0 + (5267205133/10000000000 : ℝ)*x 1 + (-27291199/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068862933/2000000000 : ℝ)^4217 ≤ (43714606589903/100000000000000 : ℝ)^3193 := by
    have hnat : (1068862933 : ℕ)^4217*100000000000000^3193 ≤ 43714606589903^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068862933 2000000000 43714606589903 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267205133/10000000000 : ℝ)^4217 ≤ (42883535743393/100000000000000 : ℝ)^3193 := by
    have hnat : (5267205133 : ℕ)^4217*100000000000000^3193 ≤ 42883535743393^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267205133 10000000000 42883535743393 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27291199/125000000 : ℝ)^4217 ≤ (536074306169/4000000000000 : ℝ)^3193 := by
    have hnat : (27291199 : ℕ)^4217*4000000000000^3193 ≤ 536074306169^3193*125000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27291199 125000000 536074306169 4000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068862933/2000000000 : ℝ), (5267205133/10000000000 : ℝ), (-27291199/125000000 : ℝ)] ![(43714606589903/100000000000000 : ℝ), (42883535743393/100000000000000 : ℝ), (536074306169/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068862933/2000000000 : ℝ)|^4217 ≤ (43714606589903/100000000000000 : ℝ)^3193
        have hw : |(1068862933/2000000000 : ℝ)|=(1068862933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267205133/10000000000 : ℝ)|^4217 ≤ (42883535743393/100000000000000 : ℝ)^3193
        have hw : |(5267205133/10000000000 : ℝ)|=(5267205133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27291199/125000000 : ℝ)|^4217 ≤ (536074306169/4000000000000 : ℝ)^3193
        have hw : |(-27291199/125000000 : ℝ)|=(27291199/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175457627/5000000000 : ℝ)*x 0 + (2113461079/5000000000 : ℝ)*x 1 + (223921439/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175457627/5000000000 : ℝ)^4217 ≤ (16658768008561/50000000000000 : ℝ)^3193 := by
    have hnat : (2175457627 : ℕ)^4217*50000000000000^3193 ≤ 16658768008561^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175457627 5000000000 16658768008561 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113461079/5000000000 : ℝ)^4217 ≤ (16034656378129/50000000000000 : ℝ)^3193 := by
    have hnat : (2113461079 : ℕ)^4217*50000000000000^3193 ≤ 16034656378129^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113461079 5000000000 16034656378129 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223921439/500000000 : ℝ)^4217 ≤ (34613151216873/100000000000000 : ℝ)^3193 := by
    have hnat : (223921439 : ℕ)^4217*100000000000000^3193 ≤ 34613151216873^3193*500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223921439 500000000 34613151216873 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175457627/5000000000 : ℝ), (2113461079/5000000000 : ℝ), (223921439/500000000 : ℝ)] ![(16658768008561/50000000000000 : ℝ), (16034656378129/50000000000000 : ℝ), (34613151216873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175457627/5000000000 : ℝ)|^4217 ≤ (16658768008561/50000000000000 : ℝ)^3193
        have hw : |(2175457627/5000000000 : ℝ)|=(2175457627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113461079/5000000000 : ℝ)|^4217 ≤ (16034656378129/50000000000000 : ℝ)^3193
        have hw : |(2113461079/5000000000 : ℝ)|=(2113461079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223921439/500000000 : ℝ)|^4217 ≤ (34613151216873/100000000000000 : ℝ)^3193
        have hw : |(223921439/500000000 : ℝ)|=(223921439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120428737/10000000000 : ℝ)*x 0 + (1316879477/2500000000 : ℝ)*x 1 + (5390897343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120428737/10000000000 : ℝ)^4217 ≤ (12894565788187/100000000000000 : ℝ)^3193 := by
    have hnat : (2120428737 : ℕ)^4217*100000000000000^3193 ≤ 12894565788187^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120428737 10000000000 12894565788187 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316879477/2500000000 : ℝ)^4217 ≤ (857737978637/2000000000000 : ℝ)^3193 := by
    have hnat : (1316879477 : ℕ)^4217*2000000000000^3193 ≤ 857737978637^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316879477 2500000000 857737978637 2000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390897343/10000000000 : ℝ)^4217 ≤ (22109267632107/50000000000000 : ℝ)^3193 := by
    have hnat : (5390897343 : ℕ)^4217*50000000000000^3193 ≤ 22109267632107^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390897343 10000000000 22109267632107 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120428737/10000000000 : ℝ), (1316879477/2500000000 : ℝ), (5390897343/10000000000 : ℝ)] ![(12894565788187/100000000000000 : ℝ), (857737978637/2000000000000 : ℝ), (22109267632107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120428737/10000000000 : ℝ)|^4217 ≤ (12894565788187/100000000000000 : ℝ)^3193
        have hw : |(-2120428737/10000000000 : ℝ)|=(2120428737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316879477/2500000000 : ℝ)|^4217 ≤ (857737978637/2000000000000 : ℝ)^3193
        have hw : |(1316879477/2500000000 : ℝ)|=(1316879477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390897343/10000000000 : ℝ)|^4217 ≤ (22109267632107/50000000000000 : ℝ)^3193
        have hw : |(5390897343/10000000000 : ℝ)|=(5390897343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656337213/5000000000 : ℝ)*x 0 + (-411921161/2000000000 : ℝ)*x 1 + (2695448699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656337213/5000000000 : ℝ)^4217 ≤ (43373126056899/100000000000000 : ℝ)^3193 := by
    have hnat : (2656337213 : ℕ)^4217*100000000000000^3193 ≤ 43373126056899^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656337213 5000000000 43373126056899 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411921161/2000000000 : ℝ)^4217 ≤ (6204169032711/50000000000000 : ℝ)^3193 := by
    have hnat : (411921161 : ℕ)^4217*50000000000000^3193 ≤ 6204169032711^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411921161 2000000000 6204169032711 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695448699/5000000000 : ℝ)^4217 ≤ (11054633965007/25000000000000 : ℝ)^3193 := by
    have hnat : (2695448699 : ℕ)^4217*25000000000000^3193 ≤ 11054633965007^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695448699 5000000000 11054633965007 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656337213/5000000000 : ℝ), (-411921161/2000000000 : ℝ), (2695448699/5000000000 : ℝ)] ![(43373126056899/100000000000000 : ℝ), (6204169032711/50000000000000 : ℝ), (11054633965007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656337213/5000000000 : ℝ)|^4217 ≤ (43373126056899/100000000000000 : ℝ)^3193
        have hw : |(2656337213/5000000000 : ℝ)|=(2656337213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411921161/2000000000 : ℝ)|^4217 ≤ (6204169032711/50000000000000 : ℝ)^3193
        have hw : |(-411921161/2000000000 : ℝ)|=(411921161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695448699/5000000000 : ℝ)|^4217 ≤ (11054633965007/25000000000000 : ℝ)^3193
        have hw : |(2695448699/5000000000 : ℝ)|=(2695448699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312675101/10000000000 : ℝ)*x 0 + (2695448011/5000000000 : ℝ)*x 1 + (-2059606763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312675101/10000000000 : ℝ)^4217 ≤ (8674626666993/20000000000000 : ℝ)^3193 := by
    have hnat : (5312675101 : ℕ)^4217*20000000000000^3193 ≤ 8674626666993^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312675101 10000000000 8674626666993 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695448011/5000000000 : ℝ)^4217 ≤ (44218520953847/100000000000000 : ℝ)^3193 := by
    have hnat : (2695448011 : ℕ)^4217*100000000000000^3193 ≤ 44218520953847^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695448011 5000000000 44218520953847 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059606763/10000000000 : ℝ)^4217 ≤ (6204172843981/50000000000000 : ℝ)^3193 := by
    have hnat : (2059606763 : ℕ)^4217*50000000000000^3193 ≤ 6204172843981^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059606763 10000000000 6204172843981 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312675101/10000000000 : ℝ), (2695448011/5000000000 : ℝ), (-2059606763/10000000000 : ℝ)] ![(8674626666993/20000000000000 : ℝ), (44218520953847/100000000000000 : ℝ), (6204172843981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312675101/10000000000 : ℝ)|^4217 ≤ (8674626666993/20000000000000 : ℝ)^3193
        have hw : |(5312675101/10000000000 : ℝ)|=(5312675101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695448011/5000000000 : ℝ)|^4217 ≤ (44218520953847/100000000000000 : ℝ)^3193
        have hw : |(2695448011/5000000000 : ℝ)|=(2695448011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2059606763/10000000000 : ℝ)|^4217 ≤ (6204172843981/50000000000000 : ℝ)^3193
        have hw : |(-2059606763/10000000000 : ℝ)|=(2059606763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175460173/5000000000 : ℝ)*x 0 + (4477795931/10000000000 : ℝ)*x 1 + (4227561677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175460173/5000000000 : ℝ)^4217 ≤ (6663517502907/20000000000000 : ℝ)^3193 := by
    have hnat : (2175460173 : ℕ)^4217*20000000000000^3193 ≤ 6663517502907^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175460173 5000000000 6663517502907 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477795931/10000000000 : ℝ)^4217 ≤ (34606691545757/100000000000000 : ℝ)^3193 := by
    have hnat : (4477795931 : ℕ)^4217*100000000000000^3193 ≤ 34606691545757^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477795931 10000000000 34606691545757 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227561677/10000000000 : ℝ)^4217 ≤ (125295784871/390625000000 : ℝ)^3193 := by
    have hnat : (4227561677 : ℕ)^4217*390625000000^3193 ≤ 125295784871^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227561677 10000000000 125295784871 390625000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175460173/5000000000 : ℝ), (4477795931/10000000000 : ℝ), (4227561677/10000000000 : ℝ)] ![(6663517502907/20000000000000 : ℝ), (34606691545757/100000000000000 : ℝ), (125295784871/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175460173/5000000000 : ℝ)|^4217 ≤ (6663517502907/20000000000000 : ℝ)^3193
        have hw : |(2175460173/5000000000 : ℝ)|=(2175460173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477795931/10000000000 : ℝ)|^4217 ≤ (34606691545757/100000000000000 : ℝ)^3193
        have hw : |(4477795931/10000000000 : ℝ)|=(4477795931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227561677/10000000000 : ℝ)|^4217 ≤ (125295784871/390625000000 : ℝ)^3193
        have hw : |(4227561677/10000000000 : ℝ)|=(4227561677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s7_8 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2479251/400000000 : ℝ)*x 0 + (1182216259/2000000000 : ℝ)*x 1 + (5911127951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2479251/400000000 : ℝ)^4217 ≤ (121404577507/100000000000000 : ℝ)^3193 := by
    have hnat : (2479251 : ℕ)^4217*100000000000000^3193 ≤ 121404577507^3193*400000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479251 400000000 121404577507 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182216259/2000000000 : ℝ)^4217 ≤ (9987807483419/20000000000000 : ℝ)^3193 := by
    have hnat : (1182216259 : ℕ)^4217*20000000000000^3193 ≤ 9987807483419^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182216259 2000000000 9987807483419 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911127951/10000000000 : ℝ)^4217 ≤ (9987911599057/20000000000000 : ℝ)^3193 := by
    have hnat : (5911127951 : ℕ)^4217*20000000000000^3193 ≤ 9987911599057^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911127951 10000000000 9987911599057 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2479251/400000000 : ℝ), (1182216259/2000000000 : ℝ), (5911127951/10000000000 : ℝ)] ![(121404577507/100000000000000 : ℝ), (9987807483419/20000000000000 : ℝ), (9987911599057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2479251/400000000 : ℝ)|^4217 ≤ (121404577507/100000000000000 : ℝ)^3193
        have hw : |(-2479251/400000000 : ℝ)|=(2479251/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1182216259/2000000000 : ℝ)|^4217 ≤ (9987807483419/20000000000000 : ℝ)^3193
        have hw : |(1182216259/2000000000 : ℝ)|=(1182216259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5911127951/10000000000 : ℝ)|^4217 ≤ (9987911599057/20000000000000 : ℝ)^3193
        have hw : |(5911127951/10000000000 : ℝ)|=(5911127951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11473/100000 : ℝ) ^ (8433/2048 : ℝ) ≤ (839333867173399/6250000000000000000 : ℝ) := by
    have hpowers : (11473/100000 : ℝ)^8433 ≤ (839333867173399/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11473 : ℕ)^8433*6250000000000000000^2048 ≤ 839333867173399^2048*100000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11473 100000 839333867173399 6250000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11473/100000 : ℝ)) (X := (839333867173399/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3527/25000 : ℝ) ^ (8433/2048 : ℝ) ≤ (6292228451131531/20000000000000000000 : ℝ) := by
    have hpowers : (3527/25000 : ℝ)^8433 ≤ (6292228451131531/20000000000000000000 : ℝ)^2048 := by
      have hnat : (3527 : ℕ)^8433*20000000000000000000^2048 ≤ 6292228451131531^2048*25000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3527 25000 6292228451131531 20000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3527/25000 : ℝ)) (X := (6292228451131531/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125839333867173399/3125000000000000000 : ℝ) ≤ (5000326105728419/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (3125839333867173399/3125000000000000000 : ℝ)^2048 ≤ (5000326105728419/5000000000000000 : ℝ)^8433 := by
      have hnat : (3125839333867173399 : ℕ)^2048*5000000000000000^8433 ≤ 5000326105728419^8433*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125839333867173399 3125000000000000000 5000326105728419 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000326105728419/5000000000000000 : ℝ)) (X := (3125839333867173399/3125000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044890484130432039/100000000000000000000 : ℝ) ≤ (10001090004645819/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (100044890484130432039/100000000000000000000 : ℝ)^2048 ≤ (10001090004645819/10000000000000000 : ℝ)^8433 := by
      have hnat : (100044890484130432039 : ℕ)^2048*10000000000000000^8433 ≤ 10001090004645819^8433*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044890484130432039 100000000000000000000 10001090004645819 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001090004645819/10000000000000000 : ℝ)) (X := (100044890484130432039/100000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006292228451131531/10000000000000000000 : ℝ) ≤ (25003819494587/25000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (10006292228451131531/10000000000000000000 : ℝ)^2048 ≤ (25003819494587/25000000000000 : ℝ)^8433 := by
      have hnat : (10006292228451131531 : ℕ)^2048*25000000000000^8433 ≤ 25003819494587^8433*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006292228451131531 10000000000000000000 25003819494587 25000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25003819494587/25000000000000 : ℝ)) (X := (10006292228451131531/10000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(839333867173399/6250000000000000000 : ℝ) ≤ ((3292709121834301263/3293750000000000000 : ℝ)+2*(437793188981/263500000000000 : ℝ)*(11473/100000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (3292709121834301263/3293750000000000000 : ℝ)+2*(437793188981/263500000000000 : ℝ)*(11473/100000 : ℝ)=(5000326105728419/5000000000000000 : ℝ) by norm_num, show 1+2*(839333867173399/6250000000000000000 : ℝ)=(3125839333867173399/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6292228451131531/20000000000000000000 : ℝ)+(839333867173399/6250000000000000000 : ℝ) ≤ ((3292709121834301263/3293750000000000000 : ℝ)+(437793188981/263500000000000 : ℝ)*((3527/25000 : ℝ)+(11473/100000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (3292709121834301263/3293750000000000000 : ℝ)+(437793188981/263500000000000 : ℝ)*((3527/25000 : ℝ)+(11473/100000 : ℝ))=(10001090004645819/10000000000000000 : ℝ) by norm_num, show 1+(6292228451131531/20000000000000000000 : ℝ)+(839333867173399/6250000000000000000 : ℝ)=(100044890484130432039/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6292228451131531/20000000000000000000 : ℝ) ≤ ((3292709121834301263/3293750000000000000 : ℝ)+2*(437793188981/263500000000000 : ℝ)*(3527/25000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (3292709121834301263/3293750000000000000 : ℝ)+2*(437793188981/263500000000000 : ℝ)*(3527/25000 : ℝ)=(25003819494587/25000000000000 : ℝ) by norm_num, show 1+2*(6292228451131531/20000000000000000000 : ℝ)=(10006292228451131531/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3292709121834301263/3293750000000000000 : ℝ)*(X 1 0+X 2 0)+(437793188981/263500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (3292709121834301263/3293750000000000000 : ℝ)) (alpha := (437793188981/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3292709121834301263/3293750000000000000 : ℝ)*(X 0 1+X 2 1)+(437793188981/263500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (3292709121834301263/3293750000000000000 : ℝ)) (alpha := (437793188981/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3292709121834301263/3293750000000000000 : ℝ)*(X 0 2+X 1 2)+(437793188981/263500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (11473/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (3292709121834301263/3293750000000000000 : ℝ)) (alpha := (437793188981/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2120423553/10000000000 : ℝ)*X 0 0+(5391212859/10000000000 : ℝ)*X 0 1+(5267203907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336077877/2500000000 : ℝ)*X 1 0+(-2183296777/10000000000 : ℝ)*X 1 1+(5267207659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068862933/2000000000 : ℝ)*X 2 0+(5267205133/10000000000 : ℝ)*X 2 1+(-27291199/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175457627/5000000000 : ℝ)*X 0 0+(2113461079/5000000000 : ℝ)*X 0 1+(223921439/500000000 : ℝ)*X 0 2+(2175457627/5000000000 : ℝ)*X 1 0+(2113461079/5000000000 : ℝ)*X 1 1+(223921439/500000000 : ℝ)*X 1 2+(2175457627/5000000000 : ℝ)*X 2 0+(2113461079/5000000000 : ℝ)*X 2 1+(223921439/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120428737/10000000000 : ℝ)*X 0 0+(1316879477/2500000000 : ℝ)*X 0 1+(5390897343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656337213/5000000000 : ℝ)*X 1 0+(-411921161/2000000000 : ℝ)*X 1 1+(2695448699/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312675101/10000000000 : ℝ)*X 2 0+(2695448011/5000000000 : ℝ)*X 2 1+(-2059606763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175460173/5000000000 : ℝ)*X 0 0+(4477795931/10000000000 : ℝ)*X 0 1+(4227561677/10000000000 : ℝ)*X 0 2+(2175460173/5000000000 : ℝ)*X 1 0+(4477795931/10000000000 : ℝ)*X 1 1+(4227561677/10000000000 : ℝ)*X 1 2+(2175460173/5000000000 : ℝ)*X 2 0+(4477795931/10000000000 : ℝ)*X 2 1+(4227561677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2479251/400000000 : ℝ)*X 0 0+(1182216259/2000000000 : ℝ)*X 0 1+(5911127951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (526964044837922263769811891/82343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4063443909/100000000000000 : ℝ)*(lower2) + (783960263/50000000000000 : ℝ)*(lower4) + (18808789/2500000000000 : ℝ)*(lower5) + (6020120576982131/100000000000000 : ℝ)*(major0) + (6020120576982131/100000000000000 : ℝ)*(major1) + (6020120576982131/100000000000000 : ℝ)*(major2) + (4032000659707169/50000000000000 : ℝ)*(sp0) + (4032087115852341/50000000000000 : ℝ)*(sp1) + (4032079161188589/50000000000000 : ℝ)*(sp2) + (1988009926902797/50000000000000 : ℝ)*(sp3) + (77932361433/50000000000000 : ℝ)*(sp4) + (3181865501/20000000000000 : ℝ)*(sp6) + (46855135191/100000000000000 : ℝ)*(sp7) + (8523783739/50000000000000 : ℝ)*(sp8) + (1988033354470393/50000000000000 : ℝ)*(f.failure) + (4032087115852341/50000000000000 : ℝ)*(f.sum) + (98455624666789/13175000000000000000000000000 : ℝ)*base66 + (1253979108416256047/329375000000000000000000000000000 : ℝ)*base68 + (8194975605763743953/329375000000000000000000000000000 : ℝ)*base69 + (12875692239549368953/329375000000000000000000000000000 : ℝ)*base71 + (35045413761843/6587500000000000000000000000 : ℝ)*base73 + (6852437092693743953/329375000000000000000000000000000 : ℝ)*base75 + (15381093728743953/329375000000000000000000000000000 : ℝ)*base77 + (2639049236703743953/329375000000000000000000000000000 : ℝ)*base79 + (68502043825911/13175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (21075401/5000000000000000000000 : ℝ)*base90 + (21075401/5000000000000000000000 : ℝ)*base92 + (21075401/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3451954702948465182369/658750000000000000000000000 : ℝ) := by norm_num
    linear_combination (206503013/20000000000000 : ℝ)*(lower2) + (159127567/25000000000000 : ℝ)*(lower4) + (75100407/10000000000000 : ℝ)*(lower5) + (1210153512683339/20000000000000 : ℝ)*(major0) + (1210153512683339/20000000000000 : ℝ)*(major1) + (1210153512683339/20000000000000 : ℝ)*(major2) + (79116789649/100000000000000 : ℝ)*(sp0) + (47759786251/100000000000000 : ℝ)*(sp1) + (14899268319/100000000000000 : ℝ)*(sp3) + (4052569806947733/50000000000000 : ℝ)*(sp4) + (202629482094709/2500000000000 : ℝ)*(sp5) + (8105227043574611/100000000000000 : ℝ)*(sp6) + (3996293009318491/100000000000000 : ℝ)*(sp7) + (1039111187/12500000000000 : ℝ)*(sp8) + (399630790858681/10000000000000 : ℝ)*(f.failure) + (8105227043574611/100000000000000 : ℝ)*(f.sum) + (409102958331/164687500000000000000000000 : ℝ)*base66 + (15455198718005343/65875000000000000000000000000000 : ℝ)*base68 + (41274703522255343/65875000000000000000000000000000 : ℝ)*base70 + (125875508583744657/65875000000000000000000000000000 : ℝ)*base71 + (23218795661401/2635000000000000000000000000 : ℝ)*base74 + (515515584624744657/65875000000000000000000000000000 : ℝ)*base75 + (564988741198880343/65875000000000000000000000000000 : ℝ)*base78 + (471320307396869657/65875000000000000000000000000000 : ℝ)*base79 + (6601079462031/2635000000000000000000000000 : ℝ)*base82 + (2584183/1000000000000000000000 : ℝ)*base89 + (2584183/1000000000000000000000 : ℝ)*base91 + (2584183/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1241_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1241_s8_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120426419/10000000000 : ℝ)*x 0 + (1347793463/2500000000 : ℝ)*x 1 + (1053448213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120426419/10000000000 : ℝ)^4217 ≤ (12894547171557/100000000000000 : ℝ)^3193 := by
    have hnat : (2120426419 : ℕ)^4217*100000000000000^3193 ≤ 12894547171557^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120426419 10000000000 12894547171557 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347793463/2500000000 : ℝ)^4217 ≤ (44221530705537/100000000000000 : ℝ)^3193 := by
    have hnat : (1347793463 : ℕ)^4217*100000000000000^3193 ≤ 44221530705537^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347793463 2500000000 44221530705537 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053448213/2000000000 : ℝ)^4217 ≤ (21441961053807/50000000000000 : ℝ)^3193 := by
    have hnat : (1053448213 : ℕ)^4217*50000000000000^3193 ≤ 21441961053807^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053448213 2000000000 21441961053807 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120426419/10000000000 : ℝ), (1347793463/2500000000 : ℝ), (1053448213/2000000000 : ℝ)] ![(12894547171557/100000000000000 : ℝ), (44221530705537/100000000000000 : ℝ), (21441961053807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120426419/10000000000 : ℝ)|^4217 ≤ (12894547171557/100000000000000 : ℝ)^3193
        have hw : |(-2120426419/10000000000 : ℝ)|=(2120426419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347793463/2500000000 : ℝ)|^4217 ≤ (44221530705537/100000000000000 : ℝ)^3193
        have hw : |(1347793463/2500000000 : ℝ)|=(1347793463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053448213/2000000000 : ℝ)|^4217 ≤ (21441961053807/50000000000000 : ℝ)^3193
        have hw : |(1053448213/2000000000 : ℝ)|=(1053448213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344303511/10000000000 : ℝ)*x 0 + (-1091631539/5000000000 : ℝ)*x 1 + (52672411/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344303511/10000000000 : ℝ)^4217 ≤ (43714486094707/100000000000000 : ℝ)^3193 := by
    have hnat : (5344303511 : ℕ)^4217*100000000000000^3193 ≤ 43714486094707^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344303511 10000000000 43714486094707 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091631539/5000000000 : ℝ)^4217 ≤ (13401591406669/100000000000000 : ℝ)^3193 := by
    have hnat : (1091631539 : ℕ)^4217*100000000000000^3193 ≤ 13401591406669^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091631539 5000000000 13401591406669 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52672411/100000000 : ℝ)^4217 ≤ (42883922483957/100000000000000 : ℝ)^3193 := by
    have hnat : (52672411 : ℕ)^4217*100000000000000^3193 ≤ 42883922483957^3193*100000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52672411 100000000 42883922483957 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344303511/10000000000 : ℝ), (-1091631539/5000000000 : ℝ), (52672411/100000000 : ℝ)] ![(43714486094707/100000000000000 : ℝ), (13401591406669/100000000000000 : ℝ), (42883922483957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344303511/10000000000 : ℝ)|^4217 ≤ (43714486094707/100000000000000 : ℝ)^3193
        have hw : |(5344303511/10000000000 : ℝ)|=(5344303511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091631539/5000000000 : ℝ)|^4217 ≤ (13401591406669/100000000000000 : ℝ)^3193
        have hw : |(-1091631539/5000000000 : ℝ)|=(1091631539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52672411/100000000 : ℝ)|^4217 ≤ (42883922483957/100000000000000 : ℝ)^3193
        have hw : |(52672411/100000000 : ℝ)|=(52672411/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672151737/5000000000 : ℝ)*x 0 + (5267241033/10000000000 : ℝ)*x 1 + (-2183263217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672151737/5000000000 : ℝ)^4217 ≤ (43714485695001/100000000000000 : ℝ)^3193 := by
    have hnat : (2672151737 : ℕ)^4217*100000000000000^3193 ≤ 43714485695001^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672151737 5000000000 43714485695001 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267241033/10000000000 : ℝ)^4217 ≤ (42883921763529/100000000000000 : ℝ)^3193 := by
    have hnat : (5267241033 : ℕ)^4217*100000000000000^3193 ≤ 42883921763529^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267241033 10000000000 42883921763529 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183263217/10000000000 : ℝ)^4217 ≤ (13401592533529/100000000000000 : ℝ)^3193 := by
    have hnat : (2183263217 : ℕ)^4217*100000000000000^3193 ≤ 13401592533529^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183263217 10000000000 13401592533529 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672151737/5000000000 : ℝ), (5267241033/10000000000 : ℝ), (-2183263217/10000000000 : ℝ)] ![(43714485695001/100000000000000 : ℝ), (42883921763529/100000000000000 : ℝ), (13401592533529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672151737/5000000000 : ℝ)|^4217 ≤ (43714485695001/100000000000000 : ℝ)^3193
        have hw : |(2672151737/5000000000 : ℝ)|=(2672151737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267241033/10000000000 : ℝ)|^4217 ≤ (42883921763529/100000000000000 : ℝ)^3193
        have hw : |(5267241033/10000000000 : ℝ)|=(5267241033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183263217/10000000000 : ℝ)|^4217 ≤ (13401592533529/100000000000000 : ℝ)^3193
        have hw : |(-2183263217/10000000000 : ℝ)|=(2183263217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175456217/5000000000 : ℝ)*x 0 + (1056749667/2500000000 : ℝ)*x 1 + (4478356469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175456217/5000000000 : ℝ)^4217 ≤ (33317507497353/100000000000000 : ℝ)^3193 := by
    have hnat : (2175456217 : ℕ)^4217*100000000000000^3193 ≤ 33317507497353^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175456217 5000000000 33317507497353 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056749667/2500000000 : ℝ)^4217 ≤ (32070079392857/100000000000000 : ℝ)^3193 := by
    have hnat : (1056749667 : ℕ)^4217*100000000000000^3193 ≤ 32070079392857^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056749667 2500000000 32070079392857 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478356469/10000000000 : ℝ)^4217 ≤ (34612413102957/100000000000000 : ℝ)^3193 := by
    have hnat : (4478356469 : ℕ)^4217*100000000000000^3193 ≤ 34612413102957^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478356469 10000000000 34612413102957 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175456217/5000000000 : ℝ), (1056749667/2500000000 : ℝ), (4478356469/10000000000 : ℝ)] ![(33317507497353/100000000000000 : ℝ), (32070079392857/100000000000000 : ℝ), (34612413102957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175456217/5000000000 : ℝ)|^4217 ≤ (33317507497353/100000000000000 : ℝ)^3193
        have hw : |(2175456217/5000000000 : ℝ)|=(2175456217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056749667/2500000000 : ℝ)|^4217 ≤ (32070079392857/100000000000000 : ℝ)^3193
        have hw : |(1056749667/2500000000 : ℝ)|=(1056749667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478356469/10000000000 : ℝ)|^4217 ≤ (34612413102957/100000000000000 : ℝ)^3193
        have hw : |(4478356469/10000000000 : ℝ)|=(4478356469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060215677/5000000000 : ℝ)*x 0 + (5267553157/10000000000 : ℝ)*x 1 + (1078172083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060215677/5000000000 : ℝ)^4217 ≤ (6447293403097/50000000000000 : ℝ)^3193 := by
    have hnat : (1060215677 : ℕ)^4217*50000000000000^3193 ≤ 6447293403097^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060215677 5000000000 6447293403097 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267553157/10000000000 : ℝ)^4217 ≤ (2144363897961/5000000000000 : ℝ)^3193 := by
    have hnat : (5267553157 : ℕ)^4217*5000000000000^3193 ≤ 2144363897961^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267553157 10000000000 2144363897961 5000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078172083/2000000000 : ℝ)^4217 ≤ (44218135224339/100000000000000 : ℝ)^3193 := by
    have hnat : (1078172083 : ℕ)^4217*100000000000000^3193 ≤ 44218135224339^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078172083 2000000000 44218135224339 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060215677/5000000000 : ℝ), (5267553157/10000000000 : ℝ), (1078172083/2000000000 : ℝ)] ![(6447293403097/50000000000000 : ℝ), (2144363897961/5000000000000 : ℝ), (44218135224339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060215677/5000000000 : ℝ)|^4217 ≤ (6447293403097/50000000000000 : ℝ)^3193
        have hw : |(-1060215677/5000000000 : ℝ)|=(1060215677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267553157/10000000000 : ℝ)|^4217 ≤ (2144363897961/5000000000000 : ℝ)^3193
        have hw : |(5267553157/10000000000 : ℝ)|=(5267553157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078172083/2000000000 : ℝ)|^4217 ≤ (44218135224339/100000000000000 : ℝ)^3193
        have hw : |(1078172083/2000000000 : ℝ)|=(1078172083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062536737/2000000000 : ℝ)*x 0 + (-514910947/2500000000 : ℝ)*x 1 + (1347715071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062536737/2000000000 : ℝ)^4217 ≤ (1734929035617/4000000000000 : ℝ)^3193 := by
    have hnat : (1062536737 : ℕ)^4217*4000000000000^3193 ≤ 1734929035617^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062536737 2000000000 1734929035617 4000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514910947/2500000000 : ℝ)^4217 ≤ (12408640286493/100000000000000 : ℝ)^3193 := by
    have hnat : (514910947 : ℕ)^4217*100000000000000^3193 ≤ 12408640286493^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514910947 2500000000 12408640286493 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347715071/2500000000 : ℝ)^4217 ≤ (22109066902611/50000000000000 : ℝ)^3193 := by
    have hnat : (1347715071 : ℕ)^4217*50000000000000^3193 ≤ 22109066902611^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347715071 2500000000 22109066902611 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062536737/2000000000 : ℝ), (-514910947/2500000000 : ℝ), (1347715071/2500000000 : ℝ)] ![(1734929035617/4000000000000 : ℝ), (12408640286493/100000000000000 : ℝ), (22109066902611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062536737/2000000000 : ℝ)|^4217 ≤ (1734929035617/4000000000000 : ℝ)^3193
        have hw : |(1062536737/2000000000 : ℝ)|=(1062536737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514910947/2500000000 : ℝ)|^4217 ≤ (12408640286493/100000000000000 : ℝ)^3193
        have hw : |(-514910947/2500000000 : ℝ)|=(514910947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347715071/2500000000 : ℝ)|^4217 ≤ (22109066902611/50000000000000 : ℝ)^3193
        have hw : |(1347715071/2500000000 : ℝ)|=(1347715071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312683711/10000000000 : ℝ)*x 0 + (5390860159/10000000000 : ℝ)*x 1 + (-1029821961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312683711/10000000000 : ℝ)^4217 ≤ (21686613085383/50000000000000 : ℝ)^3193 := by
    have hnat : (5312683711 : ℕ)^4217*50000000000000^3193 ≤ 21686613085383^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312683711 10000000000 21686613085383 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390860159/10000000000 : ℝ)^4217 ≤ (22109066225551/50000000000000 : ℝ)^3193 := by
    have hnat : (5390860159 : ℕ)^4217*50000000000000^3193 ≤ 22109066225551^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390860159 10000000000 22109066225551 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029821961/5000000000 : ℝ)^4217 ≤ (124086413527/1000000000000 : ℝ)^3193 := by
    have hnat : (1029821961 : ℕ)^4217*1000000000000^3193 ≤ 124086413527^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029821961 5000000000 124086413527 1000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312683711/10000000000 : ℝ), (5390860159/10000000000 : ℝ), (-1029821961/5000000000 : ℝ)] ![(21686613085383/50000000000000 : ℝ), (22109066225551/50000000000000 : ℝ), (124086413527/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312683711/10000000000 : ℝ)|^4217 ≤ (21686613085383/50000000000000 : ℝ)^3193
        have hw : |(5312683711/10000000000 : ℝ)|=(5312683711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390860159/10000000000 : ℝ)|^4217 ≤ (22109066225551/50000000000000 : ℝ)^3193
        have hw : |(5390860159/10000000000 : ℝ)|=(5390860159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029821961/5000000000 : ℝ)|^4217 ≤ (124086413527/1000000000000 : ℝ)^3193
        have hw : |(-1029821961/5000000000 : ℝ)|=(1029821961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s8_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350921813/10000000000 : ℝ)*x 0 + (2238861539/5000000000 : ℝ)*x 1 + (845526881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350921813/10000000000 : ℝ)^4217 ≤ (3331760235089/10000000000000 : ℝ)^3193 := by
    have hnat : (4350921813 : ℕ)^4217*10000000000000^3193 ≤ 3331760235089^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350921813 10000000000 3331760235089 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238861539/5000000000 : ℝ)^4217 ≤ (34605947933099/100000000000000 : ℝ)^3193 := by
    have hnat : (2238861539 : ℕ)^4217*100000000000000^3193 ≤ 34605947933099^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238861539 5000000000 34605947933099 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845526881/2000000000 : ℝ)^4217 ≤ (3207644970287/10000000000000 : ℝ)^3193 := by
    have hnat : (845526881 : ℕ)^4217*10000000000000^3193 ≤ 3207644970287^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845526881 2000000000 3207644970287 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350921813/10000000000 : ℝ), (2238861539/5000000000 : ℝ), (845526881/2000000000 : ℝ)] ![(3331760235089/10000000000000 : ℝ), (34605947933099/100000000000000 : ℝ), (3207644970287/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350921813/10000000000 : ℝ)|^4217 ≤ (3331760235089/10000000000000 : ℝ)^3193
        have hw : |(4350921813/10000000000 : ℝ)|=(4350921813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238861539/5000000000 : ℝ)|^4217 ≤ (34605947933099/100000000000000 : ℝ)^3193
        have hw : |(2238861539/5000000000 : ℝ)|=(2238861539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845526881/2000000000 : ℝ)|^4217 ≤ (3207644970287/10000000000000 : ℝ)^3193
        have hw : |(845526881/2000000000 : ℝ)|=(845526881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5739/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11477/100000 : ℝ) ^ (8433/2048 : ℝ) ≤ (13448631593732049/100000000000000000000 : ℝ) := by
    have hpowers : (11477/100000 : ℝ)^8433 ≤ (13448631593732049/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11477 : ℕ)^8433*100000000000000000000^2048 ≤ 13448631593732049^2048*100000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11477 100000 13448631593732049 100000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11477/100000 : ℝ)) (X := (13448631593732049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (8433/2048 : ℝ) ≤ (31424428465233307/100000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^8433 ≤ (31424428465233307/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1763 : ℕ)^8433*100000000000000000000^2048 ≤ 31424428465233307^2048*12500^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 31424428465233307 100000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (31424428465233307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013448631593732049/50000000000000000000 : ℝ) ≤ (5000326574094443/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50013448631593732049/50000000000000000000 : ℝ)^2048 ≤ (5000326574094443/5000000000000000 : ℝ)^8433 := by
      have hnat : (50013448631593732049 : ℕ)^2048*5000000000000000^8433 ≤ 5000326574094443^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013448631593732049 50000000000000000000 5000326574094443 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000326574094443/5000000000000000 : ℝ)) (X := (50013448631593732049/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011218265014741339/25000000000000000000 : ℝ) ≤ (10001089581636489/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (25011218265014741339/25000000000000000000 : ℝ)^2048 ≤ (10001089581636489/10000000000000000 : ℝ)^8433 := by
      have hnat : (25011218265014741339 : ℕ)^2048*10000000000000000^8433 ≤ 10001089581636489^8433*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011218265014741339 25000000000000000000 10001089581636489 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089581636489/10000000000000000 : ℝ)) (X := (25011218265014741339/25000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031424428465233307/50000000000000000000 : ℝ) ≤ (2500381503771023/2500000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50031424428465233307/50000000000000000000 : ℝ)^2048 ≤ (2500381503771023/2500000000000000 : ℝ)^8433 := by
      have hnat : (50031424428465233307 : ℕ)^2048*2500000000000000^8433 ≤ 2500381503771023^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031424428465233307 50000000000000000000 2500381503771023 2500000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500381503771023/2500000000000000 : ℝ)) (X := (50031424428465233307/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13448631593732049/100000000000000000000 : ℝ) ≤ ((1313084896346796213/1313500000000000000 : ℝ)+2*(436433447603/262700000000000 : ℝ)*(11477/100000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (1313084896346796213/1313500000000000000 : ℝ)+2*(436433447603/262700000000000 : ℝ)*(11477/100000 : ℝ)=(5000326574094443/5000000000000000 : ℝ) by norm_num, show 1+2*(13448631593732049/100000000000000000000 : ℝ)=(50013448631593732049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31424428465233307/100000000000000000000 : ℝ)+(13448631593732049/100000000000000000000 : ℝ) ≤ ((1313084896346796213/1313500000000000000 : ℝ)+(436433447603/262700000000000 : ℝ)*((1763/12500 : ℝ)+(11477/100000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (1313084896346796213/1313500000000000000 : ℝ)+(436433447603/262700000000000 : ℝ)*((1763/12500 : ℝ)+(11477/100000 : ℝ))=(10001089581636489/10000000000000000 : ℝ) by norm_num, show 1+(31424428465233307/100000000000000000000 : ℝ)+(13448631593732049/100000000000000000000 : ℝ)=(25011218265014741339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31424428465233307/100000000000000000000 : ℝ) ≤ ((1313084896346796213/1313500000000000000 : ℝ)+2*(436433447603/262700000000000 : ℝ)*(1763/12500 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (1313084896346796213/1313500000000000000 : ℝ)+2*(436433447603/262700000000000 : ℝ)*(1763/12500 : ℝ)=(2500381503771023/2500000000000000 : ℝ) by norm_num, show 1+2*(31424428465233307/100000000000000000000 : ℝ)=(50031424428465233307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1313084896346796213/1313500000000000000 : ℝ)*(X 1 0+X 2 0)+(436433447603/262700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (1313084896346796213/1313500000000000000 : ℝ)) (alpha := (436433447603/262700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1313084896346796213/1313500000000000000 : ℝ)*(X 0 1+X 2 1)+(436433447603/262700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (1313084896346796213/1313500000000000000 : ℝ)) (alpha := (436433447603/262700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1313084896346796213/1313500000000000000 : ℝ)*(X 0 2+X 1 2)+(436433447603/262700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (1313084896346796213/1313500000000000000 : ℝ)) (alpha := (436433447603/262700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2120426419/10000000000 : ℝ)*X 0 0+(1347793463/2500000000 : ℝ)*X 0 1+(1053448213/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344303511/10000000000 : ℝ)*X 1 0+(-1091631539/5000000000 : ℝ)*X 1 1+(52672411/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672151737/5000000000 : ℝ)*X 2 0+(5267241033/10000000000 : ℝ)*X 2 1+(-2183263217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175456217/5000000000 : ℝ)*X 0 0+(1056749667/2500000000 : ℝ)*X 0 1+(4478356469/10000000000 : ℝ)*X 0 2+(2175456217/5000000000 : ℝ)*X 1 0+(1056749667/2500000000 : ℝ)*X 1 1+(4478356469/10000000000 : ℝ)*X 1 2+(2175456217/5000000000 : ℝ)*X 2 0+(1056749667/2500000000 : ℝ)*X 2 1+(4478356469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060215677/5000000000 : ℝ)*X 0 0+(5267553157/10000000000 : ℝ)*X 0 1+(1078172083/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062536737/2000000000 : ℝ)*X 1 0+(-514910947/2500000000 : ℝ)*X 1 1+(1347715071/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312683711/10000000000 : ℝ)*X 2 0+(5390860159/10000000000 : ℝ)*X 2 1+(-1029821961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350921813/10000000000 : ℝ)*X 0 0+(2238861539/5000000000 : ℝ)*X 0 1+(845526881/2000000000 : ℝ)*X 0 2+(4350921813/10000000000 : ℝ)*X 1 0+(2238861539/5000000000 : ℝ)*X 1 1+(845526881/2000000000 : ℝ)*X 1 2+(4350921813/10000000000 : ℝ)*X 2 0+(2238861539/5000000000 : ℝ)*X 2 1+(845526881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (325766197211425009938185817/65675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1010935809/100000000000000 : ℝ)*(base19) + (1005874277/100000000000000 : ℝ)*(base23) + (13503329/50000000000000 : ℝ)*(lower2) + (50304131/25000000000000 : ℝ)*(upper3) + (27078369/50000000000000 : ℝ)*(lower4) + (6023686354324103/100000000000000 : ℝ)*(major0) + (6023686354324103/100000000000000 : ℝ)*(major1) + (6023686354324103/100000000000000 : ℝ)*(major2) + (161378521188581/2000000000000 : ℝ)*(sp0) + (4034474879769799/50000000000000 : ℝ)*(sp1) + (8068949764601129/100000000000000 : ℝ)*(sp2) + (1989202682349349/50000000000000 : ℝ)*(sp3) + (6177761589/25000000000000 : ℝ)*(sp4) + (656325261/4000000000000 : ℝ)*(sp7) + (248651360801889/6250000000000 : ℝ)*(f.failure) + (4034475385237703/50000000000000 : ℝ)*(f.sum) + (17204393163649/3283750000000000000000000000 : ℝ)*base66 + (582650391162533061/131350000000000000000000000000000 : ℝ)*base68 + (477533123358383061/131350000000000000000000000000000 : ℝ)*base70 + (581678089568316939/131350000000000000000000000000000 : ℝ)*base71 + (29746960686841/13135000000000000000000000000 : ℝ)*base74 + (642868860101883061/131350000000000000000000000000000 : ℝ)*base76 + (1599269600588483061/131350000000000000000000000000000 : ℝ)*base78 + (754941856704716939/131350000000000000000000000000000 : ℝ)*base79 + (6635446948919/13135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2143327/625000000000000000000 : ℝ)*base89 + (2143327/625000000000000000000 : ℝ)*base91 + (2143327/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7315079275371901423273917/13135000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247302287/25000000000000 : ℝ)*(base19) + (274189617/20000000000000 : ℝ)*(base23) + (251439607/100000000000000 : ℝ)*(lower1) + (201664411/100000000000000 : ℝ)*(upper2) + (10144973/50000000000000 : ℝ)*(upper3) + (220568681/100000000000000 : ℝ)*(upper5) + (1210837178712997/20000000000000 : ℝ)*(major0) + (1210837178712997/20000000000000 : ℝ)*(major1) + (1210837178712997/20000000000000 : ℝ)*(major2) + (6307459997/100000000000000 : ℝ)*(sp1) + (1621961235900231/20000000000000 : ℝ)*(sp4) + (810979888283201/10000000000000 : ℝ)*(sp5) + (8109804808553069/100000000000000 : ℝ)*(sp6) + (3998565589064963/100000000000000 : ℝ)*(sp7) + (3998565589064963/100000000000000 : ℝ)*(f.failure) + (1621961235900231/20000000000000 : ℝ)*(f.sum) + (2883281270133/656750000000000000000000000 : ℝ)*base66 + (39012826519205361/26270000000000000000000000000000 : ℝ)*base67 + (768889995747364639/26270000000000000000000000000000 : ℝ)*base70 + (552128139474715361/26270000000000000000000000000000 : ℝ)*base71 + (1917250829951/525400000000000000000000000 : ℝ)*base73 + (86418729155414639/26270000000000000000000000000000 : ℝ)*base76 + (37933535942375361/26270000000000000000000000000000 : ℝ)*base77 + (448722855941485361/26270000000000000000000000000000 : ℝ)*base79 + (4774694348017/164187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (93835891/10000000000000000000000 : ℝ)*base90 + (93835891/10000000000000000000000 : ℝ)*base92 + (93835891/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1241_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1241_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1241_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1241_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1241_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

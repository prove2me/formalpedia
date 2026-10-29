-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1519_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:09.408432+00:00
-- url     : https://prove2.me/submissions/24e0d370-4e09-4b1a-bc7a-461bb2a17119

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
theorem support_rectangle_w1519_s6_0 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1857724901/10000000000 : ℝ)*x 0 + (2716162543/5000000000 : ℝ)*x 1 + (130449549/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1857724901/10000000000 : ℝ)^4535 ≤ (11370415109707/100000000000000 : ℝ)^3511 := by
    have hnat : (1857724901 : ℕ)^4535*100000000000000^3511 ≤ 11370415109707^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857724901 10000000000 11370415109707 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716162543/5000000000 : ℝ)^4535 ≤ (45466662316449/100000000000000 : ℝ)^3511 := by
    have hnat : (2716162543 : ℕ)^4535*100000000000000^3511 ≤ 45466662316449^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716162543 5000000000 45466662316449 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130449549/250000000 : ℝ)^4535 ≤ (5395365319483/12500000000000 : ℝ)^3511 := by
    have hnat : (130449549 : ℕ)^4535*12500000000000^3511 ≤ 5395365319483^3511*250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130449549 250000000 5395365319483 12500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1857724901/10000000000 : ℝ), (2716162543/5000000000 : ℝ), (130449549/250000000 : ℝ)] ![(11370415109707/100000000000000 : ℝ), (45466662316449/100000000000000 : ℝ), (5395365319483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1857724901/10000000000 : ℝ)|^4535 ≤ (11370415109707/100000000000000 : ℝ)^3511
        have hw : |(-1857724901/10000000000 : ℝ)|=(1857724901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716162543/5000000000 : ℝ)|^4535 ≤ (45466662316449/100000000000000 : ℝ)^3511
        have hw : |(2716162543/5000000000 : ℝ)|=(2716162543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130449549/250000000 : ℝ)|^4535 ≤ (5395365319483/12500000000000 : ℝ)^3511
        have hw : |(130449549/250000000 : ℝ)|=(130449549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_1 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351198597/10000000000 : ℝ)*x 0 + (-983742759/5000000000 : ℝ)*x 1 + (2608991263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351198597/10000000000 : ℝ)^4535 ≤ (8918309003883/20000000000000 : ℝ)^3511 := by
    have hnat : (5351198597 : ℕ)^4535*20000000000000^3511 ≤ 8918309003883^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351198597 10000000000 8918309003883 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983742759/5000000000 : ℝ)^4535 ≤ (6122763181113/50000000000000 : ℝ)^3511 := by
    have hnat : (983742759 : ℕ)^4535*50000000000000^3511 ≤ 6122763181113^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983742759 5000000000 6122763181113 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608991263/5000000000 : ℝ)^4535 ≤ (21581464301649/50000000000000 : ℝ)^3511 := by
    have hnat : (2608991263 : ℕ)^4535*50000000000000^3511 ≤ 21581464301649^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608991263 5000000000 21581464301649 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351198597/10000000000 : ℝ), (-983742759/5000000000 : ℝ), (2608991263/5000000000 : ℝ)] ![(8918309003883/20000000000000 : ℝ), (6122763181113/50000000000000 : ℝ), (21581464301649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351198597/10000000000 : ℝ)|^4535 ≤ (8918309003883/20000000000000 : ℝ)^3511
        have hw : |(5351198597/10000000000 : ℝ)|=(5351198597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983742759/5000000000 : ℝ)|^4535 ≤ (6122763181113/50000000000000 : ℝ)^3511
        have hw : |(-983742759/5000000000 : ℝ)|=(983742759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608991263/5000000000 : ℝ)|^4535 ≤ (21581464301649/50000000000000 : ℝ)^3511
        have hw : |(2608991263/5000000000 : ℝ)|=(2608991263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_2 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351198951/10000000000 : ℝ)*x 0 + (81530963/156250000 : ℝ)*x 1 + (-245935779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351198951/10000000000 : ℝ)^4535 ≤ (8918309765929/20000000000000 : ℝ)^3511 := by
    have hnat : (5351198951 : ℕ)^4535*20000000000000^3511 ≤ 8918309765929^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351198951 10000000000 8918309765929 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81530963/156250000 : ℝ)^4535 ≤ (2697682440709/6250000000000 : ℝ)^3511 := by
    have hnat : (81530963 : ℕ)^4535*6250000000000^3511 ≤ 2697682440709^3511*156250000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81530963 156250000 2697682440709 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245935779/1250000000 : ℝ)^4535 ≤ (12245532102209/100000000000000 : ℝ)^3511 := by
    have hnat : (245935779 : ℕ)^4535*100000000000000^3511 ≤ 12245532102209^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245935779 1250000000 12245532102209 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351198951/10000000000 : ℝ), (81530963/156250000 : ℝ), (-245935779/1250000000 : ℝ)] ![(8918309765929/20000000000000 : ℝ), (2697682440709/6250000000000 : ℝ), (12245532102209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351198951/10000000000 : ℝ)|^4535 ≤ (8918309765929/20000000000000 : ℝ)^3511
        have hw : |(5351198951/10000000000 : ℝ)|=(5351198951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81530963/156250000 : ℝ)|^4535 ≤ (2697682440709/6250000000000 : ℝ)^3511
        have hw : |(81530963/156250000 : ℝ)|=(81530963/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245935779/1250000000 : ℝ)|^4535 ≤ (12245532102209/100000000000000 : ℝ)^3511
        have hw : |(-245935779/1250000000 : ℝ)|=(245935779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_3 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133261591/5000000000 : ℝ)*x 0 + (251762751/625000000 : ℝ)*x 1 + (1129160747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133261591/5000000000 : ℝ)^4535 ≤ (16640005012529/50000000000000 : ℝ)^3511 := by
    have hnat : (2133261591 : ℕ)^4535*50000000000000^3511 ≤ 16640005012529^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133261591 5000000000 16640005012529 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251762751/625000000 : ℝ)^4535 ≤ (3862338495673/12500000000000 : ℝ)^3511 := by
    have hnat : (251762751 : ℕ)^4535*12500000000000^3511 ≤ 3862338495673^3511*625000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251762751 625000000 3862338495673 12500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129160747/2500000000 : ℝ)^4535 ≤ (35821281991969/100000000000000 : ℝ)^3511 := by
    have hnat : (1129160747 : ℕ)^4535*100000000000000^3511 ≤ 35821281991969^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129160747 2500000000 35821281991969 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133261591/5000000000 : ℝ), (251762751/625000000 : ℝ), (1129160747/2500000000 : ℝ)] ![(16640005012529/50000000000000 : ℝ), (3862338495673/12500000000000 : ℝ), (35821281991969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133261591/5000000000 : ℝ)|^4535 ≤ (16640005012529/50000000000000 : ℝ)^3511
        have hw : |(2133261591/5000000000 : ℝ)|=(2133261591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251762751/625000000 : ℝ)|^4535 ≤ (3862338495673/12500000000000 : ℝ)^3511
        have hw : |(251762751/625000000 : ℝ)|=(251762751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129160747/2500000000 : ℝ)|^4535 ≤ (35821281991969/100000000000000 : ℝ)^3511
        have hw : |(1129160747/2500000000 : ℝ)|=(1129160747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_4 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464438411/2500000000 : ℝ)*x 0 + (5219086641/10000000000 : ℝ)*x 1 + (5431212213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464438411/2500000000 : ℝ)^4535 ≤ (710665146519/6250000000000 : ℝ)^3511 := by
    have hnat : (464438411 : ℕ)^4535*6250000000000^3511 ≤ 710665146519^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464438411 2500000000 710665146519 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219086641/10000000000 : ℝ)^4535 ≤ (2698420368671/6250000000000 : ℝ)^3511 := by
    have hnat : (5219086641 : ℕ)^4535*6250000000000^3511 ≤ 2698420368671^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219086641 10000000000 2698420368671 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431212213/10000000000 : ℝ)^4535 ≤ (45454631740607/100000000000000 : ℝ)^3511 := by
    have hnat : (5431212213 : ℕ)^4535*100000000000000^3511 ≤ 45454631740607^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431212213 10000000000 45454631740607 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464438411/2500000000 : ℝ), (5219086641/10000000000 : ℝ), (5431212213/10000000000 : ℝ)] ![(710665146519/6250000000000 : ℝ), (2698420368671/6250000000000 : ℝ), (45454631740607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464438411/2500000000 : ℝ)|^4535 ≤ (710665146519/6250000000000 : ℝ)^3511
        have hw : |(-464438411/2500000000 : ℝ)|=(464438411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219086641/10000000000 : ℝ)|^4535 ≤ (2698420368671/6250000000000 : ℝ)^3511
        have hw : |(5219086641/10000000000 : ℝ)|=(5219086641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431212213/10000000000 : ℝ)|^4535 ≤ (45454631740607/100000000000000 : ℝ)^3511
        have hw : |(5431212213/10000000000 : ℝ)|=(5431212213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_5 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058974477/2000000000 : ℝ)*x 0 + (-877127847/5000000000 : ℝ)*x 1 + (5431212181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058974477/2000000000 : ℝ)^4535 ≤ (21993109283721/50000000000000 : ℝ)^3511 := by
    have hnat : (1058974477 : ℕ)^4535*50000000000000^3511 ≤ 21993109283721^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058974477 2000000000 21993109283721 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877127847/5000000000 : ℝ)^4535 ≤ (1055915001217/10000000000000 : ℝ)^3511 := by
    have hnat : (877127847 : ℕ)^4535*10000000000000^3511 ≤ 1055915001217^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877127847 5000000000 1055915001217 10000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431212181/10000000000 : ℝ)^4535 ≤ (9090926278937/20000000000000 : ℝ)^3511 := by
    have hnat : (5431212181 : ℕ)^4535*20000000000000^3511 ≤ 9090926278937^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431212181 10000000000 9090926278937 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058974477/2000000000 : ℝ), (-877127847/5000000000 : ℝ), (5431212181/10000000000 : ℝ)] ![(21993109283721/50000000000000 : ℝ), (1055915001217/10000000000000 : ℝ), (9090926278937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058974477/2000000000 : ℝ)|^4535 ≤ (21993109283721/50000000000000 : ℝ)^3511
        have hw : |(1058974477/2000000000 : ℝ)|=(1058974477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877127847/5000000000 : ℝ)|^4535 ≤ (1055915001217/10000000000000 : ℝ)^3511
        have hw : |(-877127847/5000000000 : ℝ)|=(877127847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431212181/10000000000 : ℝ)|^4535 ≤ (9090926278937/20000000000000 : ℝ)^3511
        have hw : |(5431212181/10000000000 : ℝ)|=(5431212181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_6 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647436077/5000000000 : ℝ)*x 0 + (5431212263/10000000000 : ℝ)*x 1 + (-17542559/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647436077/5000000000 : ℝ)^4535 ≤ (43986216088767/100000000000000 : ℝ)^3511 := by
    have hnat : (2647436077 : ℕ)^4535*100000000000000^3511 ≤ 43986216088767^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647436077 5000000000 43986216088767 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431212263/10000000000 : ℝ)^4535 ≤ (4545463228111/10000000000000 : ℝ)^3511 := by
    have hnat : (5431212263 : ℕ)^4535*10000000000000^3511 ≤ 4545463228111^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431212263 10000000000 4545463228111 10000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17542559/100000000 : ℝ)^4535 ≤ (5279575806877/50000000000000 : ℝ)^3511 := by
    have hnat : (17542559 : ℕ)^4535*50000000000000^3511 ≤ 5279575806877^3511*100000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17542559 100000000 5279575806877 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647436077/5000000000 : ℝ), (5431212263/10000000000 : ℝ), (-17542559/100000000 : ℝ)] ![(43986216088767/100000000000000 : ℝ), (4545463228111/10000000000000 : ℝ), (5279575806877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647436077/5000000000 : ℝ)|^4535 ≤ (43986216088767/100000000000000 : ℝ)^3511
        have hw : |(2647436077/5000000000 : ℝ)|=(2647436077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431212263/10000000000 : ℝ)|^4535 ≤ (4545463228111/10000000000000 : ℝ)^3511
        have hw : |(5431212263/10000000000 : ℝ)|=(5431212263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17542559/100000000 : ℝ)|^4535 ≤ (5279575806877/50000000000000 : ℝ)^3511
        have hw : |(-17542559/100000000 : ℝ)|=(17542559/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s6_7 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170663549/400000000 : ℝ)*x 0 + (4514125703/10000000000 : ℝ)*x 1 + (80614793/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170663549/400000000 : ℝ)^4535 ≤ (33280670388601/100000000000000 : ℝ)^3511 := by
    have hnat : (170663549 : ℕ)^4535*100000000000000^3511 ≤ 33280670388601^3511*400000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170663549 400000000 33280670388601 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514125703/10000000000 : ℝ)^4535 ≤ (35795496886777/100000000000000 : ℝ)^3511 := by
    have hnat : (4514125703 : ℕ)^4535*100000000000000^3511 ≤ 35795496886777^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514125703 10000000000 35795496886777 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80614793/200000000 : ℝ)^4535 ≤ (30923832715319/100000000000000 : ℝ)^3511 := by
    have hnat : (80614793 : ℕ)^4535*100000000000000^3511 ≤ 30923832715319^3511*200000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80614793 200000000 30923832715319 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170663549/400000000 : ℝ), (4514125703/10000000000 : ℝ), (80614793/200000000 : ℝ)] ![(33280670388601/100000000000000 : ℝ), (35795496886777/100000000000000 : ℝ), (30923832715319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170663549/400000000 : ℝ)|^4535 ≤ (33280670388601/100000000000000 : ℝ)^3511
        have hw : |(170663549/400000000 : ℝ)|=(170663549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514125703/10000000000 : ℝ)|^4535 ≤ (35795496886777/100000000000000 : ℝ)^3511
        have hw : |(4514125703/10000000000 : ℝ)|=(4514125703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80614793/200000000 : ℝ)|^4535 ≤ (30923832715319/100000000000000 : ℝ)^3511
        have hw : |(80614793/200000000 : ℝ)|=(80614793/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1519_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10943/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5471/50000 : ℝ) ^ (4533/1024 : ℝ) ≤ (139397140351023/2500000000000000000 : ℝ) := by
    have hpowers : (5471/50000 : ℝ)^4533 ≤ (139397140351023/2500000000000000000 : ℝ)^1024 := by
      have hnat : (5471 : ℕ)^4533*2500000000000000000^1024 ≤ 139397140351023^1024*50000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5471 50000 139397140351023 2500000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5471/50000 : ℝ)) (X := (139397140351023/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4533/1024 : ℝ) ≤ (12965192387399043/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4533 ≤ (12965192387399043/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4533*50000000000000000000^1024 ≤ 12965192387399043^1024*25000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 12965192387399043 50000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (12965192387399043/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250139397140351023/1250000000000000000 : ℝ) ≤ (10000251906482993/10000000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (1250139397140351023/1250000000000000000 : ℝ)^1024 ≤ (10000251906482993/10000000000000000 : ℝ)^4533 := by
      have hnat : (1250139397140351023 : ℕ)^1024*10000000000000000^4533 ≤ 10000251906482993^4533*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250139397140351023 1250000000000000000 10000251906482993 10000000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000251906482993/10000000000000000 : ℝ)) (X := (1250139397140351023/1250000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015753135194419503/50000000000000000000 : ℝ) ≤ (2000142327321263/2000000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (50015753135194419503/50000000000000000000 : ℝ)^1024 ≤ (2000142327321263/2000000000000000 : ℝ)^4533 := by
      have hnat : (50015753135194419503 : ℕ)^1024*2000000000000000^4533 ≤ 2000142327321263^4533*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015753135194419503 50000000000000000000 2000142327321263 2000000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000142327321263/2000000000000000 : ℝ)) (X := (50015753135194419503/50000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012965192387399043/25000000000000000000 : ℝ) ≤ (10001171366729637/10000000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (25012965192387399043/25000000000000000000 : ℝ)^1024 ≤ (10001171366729637/10000000000000000 : ℝ)^4533 := by
      have hnat : (25012965192387399043 : ℕ)^1024*10000000000000000^4533 ≤ 10001171366729637^4533*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012965192387399043 25000000000000000000 10001171366729637 10000000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001171366729637/10000000000000000 : ℝ)) (X := (25012965192387399043/25000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(139397140351023/2500000000000000000 : ℝ) ≤ ((22705541712613487779/22710000000000000000 : ℝ)+2*(229865061661/227100000000000 : ℝ)*(5471/50000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (22705541712613487779/22710000000000000000 : ℝ)+2*(229865061661/227100000000000 : ℝ)*(5471/50000 : ℝ)=(10000251906482993/10000000000000000 : ℝ) by norm_num, show 1+2*(139397140351023/2500000000000000000 : ℝ)=(1250139397140351023/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12965192387399043/50000000000000000000 : ℝ)+(139397140351023/2500000000000000000 : ℝ) ≤ ((22705541712613487779/22710000000000000000 : ℝ)+(229865061661/227100000000000 : ℝ)*((3871/25000 : ℝ)+(5471/50000 : ℝ)))^(4533/1024 : ℝ) := by
    rw [show (22705541712613487779/22710000000000000000 : ℝ)+(229865061661/227100000000000 : ℝ)*((3871/25000 : ℝ)+(5471/50000 : ℝ))=(2000142327321263/2000000000000000 : ℝ) by norm_num, show 1+(12965192387399043/50000000000000000000 : ℝ)+(139397140351023/2500000000000000000 : ℝ)=(50015753135194419503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12965192387399043/50000000000000000000 : ℝ) ≤ ((22705541712613487779/22710000000000000000 : ℝ)+2*(229865061661/227100000000000 : ℝ)*(3871/25000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (22705541712613487779/22710000000000000000 : ℝ)+2*(229865061661/227100000000000 : ℝ)*(3871/25000 : ℝ)=(10001171366729637/10000000000000000 : ℝ) by norm_num, show 1+2*(12965192387399043/50000000000000000000 : ℝ)=(25012965192387399043/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22705541712613487779/22710000000000000000 : ℝ)*(X 1 0+X 2 0)+(229865061661/227100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22705541712613487779/22710000000000000000 : ℝ)) (alpha := (229865061661/227100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22705541712613487779/22710000000000000000 : ℝ)*(X 0 1+X 2 1)+(229865061661/227100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22705541712613487779/22710000000000000000 : ℝ)) (alpha := (229865061661/227100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22705541712613487779/22710000000000000000 : ℝ)*(X 0 2+X 1 2)+(229865061661/227100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22705541712613487779/22710000000000000000 : ℝ)) (alpha := (229865061661/227100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1857724901/10000000000 : ℝ)*X 0 0+(2716162543/5000000000 : ℝ)*X 0 1+(130449549/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351198597/10000000000 : ℝ)*X 1 0+(-983742759/5000000000 : ℝ)*X 1 1+(2608991263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351198951/10000000000 : ℝ)*X 2 0+(81530963/156250000 : ℝ)*X 2 1+(-245935779/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133261591/5000000000 : ℝ)*X 0 0+(251762751/625000000 : ℝ)*X 0 1+(1129160747/2500000000 : ℝ)*X 0 2+(2133261591/5000000000 : ℝ)*X 1 0+(251762751/625000000 : ℝ)*X 1 1+(1129160747/2500000000 : ℝ)*X 1 2+(2133261591/5000000000 : ℝ)*X 2 0+(251762751/625000000 : ℝ)*X 2 1+(1129160747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-464438411/2500000000 : ℝ)*X 0 0+(5219086641/10000000000 : ℝ)*X 0 1+(5431212213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058974477/2000000000 : ℝ)*X 1 0+(-877127847/5000000000 : ℝ)*X 1 1+(5431212181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647436077/5000000000 : ℝ)*X 2 0+(5431212263/10000000000 : ℝ)*X 2 1+(-17542559/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170663549/400000000 : ℝ)*X 0 0+(4514125703/10000000000 : ℝ)*X 0 1+(80614793/200000000 : ℝ)*X 0 2+(170663549/400000000 : ℝ)*X 1 0+(4514125703/10000000000 : ℝ)*X 1 1+(80614793/200000000 : ℝ)*X 1 2+(170663549/400000000 : ℝ)*X 2 0+(4514125703/10000000000 : ℝ)*X 2 1+(80614793/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (966046877156986962156514833/189250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113420101/100000000000000 : ℝ)*(base19) + (186316091/50000000000000 : ℝ)*(base23) + (25089963/100000000000000 : ℝ)*(upper2) + (4471031/2000000000000 : ℝ)*(upper3) + (1678193438030409/50000000000000 : ℝ)*(major0) + (1678193438030409/50000000000000 : ℝ)*(major1) + (1678193438030409/50000000000000 : ℝ)*(major2) + (4665426955356681/100000000000000 : ℝ)*(sp0) + (2332715642734563/50000000000000 : ℝ)*(sp1) + (466542187667073/10000000000000 : ℝ)*(sp2) + (409467803456859/20000000000000 : ℝ)*(sp3) + (2221766273/50000000000000 : ℝ)*(sp4) + (1829917263/20000000000000 : ℝ)*(sp6) + (395724317/12500000000000 : ℝ)*(sp7) + (2047342183078831/100000000000000 : ℝ)*(f.failure) + (1166357849722307/25000000000000 : ℝ)*(f.sum) + (8398349392159/3785000000000000000000000000 : ℝ)*base66 + (2750590601884409463/378500000000000000000000000000000 : ℝ)*base68 + (560998320567409463/378500000000000000000000000000000 : ℝ)*base70 + (3763019219396409463/378500000000000000000000000000000 : ℝ)*base72 + (7216667867267/1892500000000000000000000000 : ℝ)*base74 + (3459866693580409463/378500000000000000000000000000000 : ℝ)*base76 + (3052711175459409463/378500000000000000000000000000000 : ℝ)*base78 + (4228896028044909463/378500000000000000000000000000000 : ℝ)*base80 + (93785640217/1892500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31883757/2000000000000000000000 : ℝ)*base89 + (31883757/2000000000000000000000 : ℝ)*base91 + (31883757/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2052116749499956014974475669/189250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1361941747/100000000000000 : ℝ)*(base19) + (225731747/20000000000000 : ℝ)*(base23) + (239580293/100000000000000 : ℝ)*(lower1) + (30042731/12500000000000 : ℝ)*(upper3) + (9493557/50000000000000 : ℝ)*(lower4) + (295278713/100000000000000 : ℝ)*(upper5) + (1695727808528089/50000000000000 : ℝ)*(major0) + (1695727808528089/50000000000000 : ℝ)*(major1) + (1695727808528089/50000000000000 : ℝ)*(major2) + (5967030187/100000000000000 : ℝ)*(sp1) + (147318041244349/3125000000000 : ℝ)*(sp4) + (2357084995423617/50000000000000 : ℝ)*(sp5) + (4714176191160433/100000000000000 : ℝ)*(sp6) + (517183388211483/25000000000000 : ℝ)*(sp7) + (517183388211483/25000000000000 : ℝ)*(f.failure) + (147318041244349/3125000000000 : ℝ)*(f.sum) + (36704211041659/5677500000000000000000000000 : ℝ)*base65 + (6665402846380624331/1135500000000000000000000000000000 : ℝ)*base67 + (9611737231969375669/1135500000000000000000000000000000 : ℝ)*base70 + (4980692671533124331/1135500000000000000000000000000000 : ℝ)*base71 + (1740478434409/354843750000000000000000000 : ℝ)*base73 + (41862574744624331/1135500000000000000000000000000000 : ℝ)*base75 + (7108978046098375669/1135500000000000000000000000000000 : ℝ)*base78 + (16129278477000124331/1135500000000000000000000000000000 : ℝ)*base79 + (12443241394421/5677500000000000000000000000 : ℝ)*base82 + (2901199/500000000000000000000 : ℝ)*base90 + (2901199/500000000000000000000 : ℝ)*base92 + (2901199/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1519_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1519_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1519_box_0 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-329068309/2000000000 : ℝ)*x 0 + (675259549/1250000000 : ℝ)*x 1 + (54020767/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329068309/2000000000 : ℝ)^4535 ≤ (9720159322527/100000000000000 : ℝ)^3511 := by
    have hnat : (329068309 : ℕ)^4535*100000000000000^3511 ≤ 9720159322527^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329068309 2000000000 9720159322527 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675259549/1250000000 : ℝ)^4535 ≤ (45139918667853/100000000000000 : ℝ)^3511 := by
    have hnat : (675259549 : ℕ)^4535*100000000000000^3511 ≤ 45139918667853^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675259549 1250000000 45139918667853 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54020767/100000000 : ℝ)^4535 ≤ (45139921992131/100000000000000 : ℝ)^3511 := by
    have hnat : (54020767 : ℕ)^4535*100000000000000^3511 ≤ 45139921992131^3511*100000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54020767 100000000 45139921992131 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-329068309/2000000000 : ℝ), (675259549/1250000000 : ℝ), (54020767/100000000 : ℝ)] ![(9720159322527/100000000000000 : ℝ), (45139918667853/100000000000000 : ℝ), (45139921992131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-329068309/2000000000 : ℝ)|^4535 ≤ (9720159322527/100000000000000 : ℝ)^3511
        have hw : |(-329068309/2000000000 : ℝ)|=(329068309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675259549/1250000000 : ℝ)|^4535 ≤ (45139918667853/100000000000000 : ℝ)^3511
        have hw : |(675259549/1250000000 : ℝ)|=(675259549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54020767/100000000 : ℝ)|^4535 ≤ (45139921992131/100000000000000 : ℝ)^3511
        have hw : |(54020767/100000000 : ℝ)|=(54020767/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_1 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131771553/250000000 : ℝ)*x 0 + (-913704697/5000000000 : ℝ)*x 1 + (5402076877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131771553/250000000 : ℝ)^4535 ≤ (1093218857617/2500000000000 : ℝ)^3511 := by
    have hnat : (131771553 : ℕ)^4535*2500000000000^3511 ≤ 1093218857617^3511*250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131771553 250000000 1093218857617 2500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (913704697/5000000000 : ℝ)^4535 ≤ (5565660886567/50000000000000 : ℝ)^3511 := by
    have hnat : (913704697 : ℕ)^4535*50000000000000^3511 ≤ 5565660886567^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913704697 5000000000 5565660886567 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402076877/10000000000 : ℝ)^4535 ≤ (45139923902511/100000000000000 : ℝ)^3511 := by
    have hnat : (5402076877 : ℕ)^4535*100000000000000^3511 ≤ 45139923902511^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402076877 10000000000 45139923902511 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131771553/250000000 : ℝ), (-913704697/5000000000 : ℝ), (5402076877/10000000000 : ℝ)] ![(1093218857617/2500000000000 : ℝ), (5565660886567/50000000000000 : ℝ), (45139923902511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131771553/250000000 : ℝ)|^4535 ≤ (1093218857617/2500000000000 : ℝ)^3511
        have hw : |(131771553/250000000 : ℝ)|=(131771553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-913704697/5000000000 : ℝ)|^4535 ≤ (5565660886567/50000000000000 : ℝ)^3511
        have hw : |(-913704697/5000000000 : ℝ)|=(913704697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402076877/10000000000 : ℝ)|^4535 ≤ (45139923902511/100000000000000 : ℝ)^3511
        have hw : |(5402076877/10000000000 : ℝ)|=(5402076877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_2 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317715313/2500000000 : ℝ)*x 0 + (5402077159/10000000000 : ℝ)*x 1 + (-182741019/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317715313/2500000000 : ℝ)^4535 ≤ (43728745003209/100000000000000 : ℝ)^3511 := by
    have hnat : (1317715313 : ℕ)^4535*100000000000000^3511 ≤ 43728745003209^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317715313 2500000000 43728745003209 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402077159/10000000000 : ℝ)^4535 ≤ (45139926946167/100000000000000 : ℝ)^3511 := by
    have hnat : (5402077159 : ℕ)^4535*100000000000000^3511 ≤ 45139926946167^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402077159 10000000000 45139926946167 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182741019/1000000000 : ℝ)^4535 ≤ (11131328035961/100000000000000 : ℝ)^3511 := by
    have hnat : (182741019 : ℕ)^4535*100000000000000^3511 ≤ 11131328035961^3511*1000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182741019 1000000000 11131328035961 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317715313/2500000000 : ℝ), (5402077159/10000000000 : ℝ), (-182741019/1000000000 : ℝ)] ![(43728745003209/100000000000000 : ℝ), (45139926946167/100000000000000 : ℝ), (11131328035961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317715313/2500000000 : ℝ)|^4535 ≤ (43728745003209/100000000000000 : ℝ)^3511
        have hw : |(1317715313/2500000000 : ℝ)|=(1317715313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402077159/10000000000 : ℝ)|^4535 ≤ (45139926946167/100000000000000 : ℝ)^3511
        have hw : |(5402077159/10000000000 : ℝ)|=(5402077159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182741019/1000000000 : ℝ)|^4535 ≤ (11131328035961/100000000000000 : ℝ)^3511
        have hw : |(-182741019/1000000000 : ℝ)|=(182741019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_3 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (139664797/312500000 : ℝ)*x 0 + (32594423/78125000 : ℝ)*x 1 + (2086042477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139664797/312500000 : ℝ)^4535 ≤ (17668385238981/50000000000000 : ℝ)^3511 := by
    have hnat : (139664797 : ℕ)^4535*50000000000000^3511 ≤ 17668385238981^3511*312500000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139664797 312500000 17668385238981 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32594423/78125000 : ℝ)^4535 ≤ (8082905177787/25000000000000 : ℝ)^3511 := by
    have hnat : (32594423 : ℕ)^4535*25000000000000^3511 ≤ 8082905177787^3511*78125000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32594423 78125000 8082905177787 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086042477/5000000000 : ℝ)^4535 ≤ (32331608799617/100000000000000 : ℝ)^3511 := by
    have hnat : (2086042477 : ℕ)^4535*100000000000000^3511 ≤ 32331608799617^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086042477 5000000000 32331608799617 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139664797/312500000 : ℝ), (32594423/78125000 : ℝ), (2086042477/5000000000 : ℝ)] ![(17668385238981/50000000000000 : ℝ), (8082905177787/25000000000000 : ℝ), (32331608799617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139664797/312500000 : ℝ)|^4535 ≤ (17668385238981/50000000000000 : ℝ)^3511
        have hw : |(139664797/312500000 : ℝ)|=(139664797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32594423/78125000 : ℝ)|^4535 ≤ (8082905177787/25000000000000 : ℝ)^3511
        have hw : |(32594423/78125000 : ℝ)|=(32594423/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086042477/5000000000 : ℝ)|^4535 ≤ (32331608799617/100000000000000 : ℝ)^3511
        have hw : |(2086042477/5000000000 : ℝ)|=(2086042477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_4 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075542183/10000000000 : ℝ)*x 0 + (819351/1562500 : ℝ)*x 1 + (5243843987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075542183/10000000000 : ℝ)^4535 ≤ (13121083759479/100000000000000 : ℝ)^3511 := by
    have hnat : (2075542183 : ℕ)^4535*100000000000000^3511 ≤ 13121083759479^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075542183 10000000000 13121083759479 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819351/1562500 : ℝ)^4535 ≤ (108598677557/250000000000 : ℝ)^3511 := by
    have hnat : (819351 : ℕ)^4535*250000000000^3511 ≤ 108598677557^3511*1562500^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819351 1562500 108598677557 250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243843987/10000000000 : ℝ)^4535 ≤ (8687889040773/20000000000000 : ℝ)^3511 := by
    have hnat : (5243843987 : ℕ)^4535*20000000000000^3511 ≤ 8687889040773^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243843987 10000000000 8687889040773 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075542183/10000000000 : ℝ), (819351/1562500 : ℝ), (5243843987/10000000000 : ℝ)] ![(13121083759479/100000000000000 : ℝ), (108598677557/250000000000 : ℝ), (8687889040773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075542183/10000000000 : ℝ)|^4535 ≤ (13121083759479/100000000000000 : ℝ)^3511
        have hw : |(-2075542183/10000000000 : ℝ)|=(2075542183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(819351/1562500 : ℝ)|^4535 ≤ (108598677557/250000000000 : ℝ)^3511
        have hw : |(819351/1562500 : ℝ)|=(819351/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243843987/10000000000 : ℝ)|^4535 ≤ (8687889040773/20000000000000 : ℝ)^3511
        have hw : |(5243843987/10000000000 : ℝ)|=(5243843987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_5 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380965811/10000000000 : ℝ)*x 0 + (-946391493/5000000000 : ℝ)*x 1 + (5243845957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380965811/10000000000 : ℝ)^4535 ≤ (44912199857443/100000000000000 : ℝ)^3511 := by
    have hnat : (5380965811 : ℕ)^4535*100000000000000^3511 ≤ 44912199857443^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380965811 10000000000 44912199857443 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946391493/5000000000 : ℝ)^4535 ≤ (11648333848799/100000000000000 : ℝ)^3511 := by
    have hnat : (946391493 : ℕ)^4535*100000000000000^3511 ≤ 11648333848799^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946391493 5000000000 11648333848799 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243845957/10000000000 : ℝ)^4535 ≤ (4343946628273/10000000000000 : ℝ)^3511 := by
    have hnat : (5243845957 : ℕ)^4535*10000000000000^3511 ≤ 4343946628273^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243845957 10000000000 4343946628273 10000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380965811/10000000000 : ℝ), (-946391493/5000000000 : ℝ), (5243845957/10000000000 : ℝ)] ![(44912199857443/100000000000000 : ℝ), (11648333848799/100000000000000 : ℝ), (4343946628273/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380965811/10000000000 : ℝ)|^4535 ≤ (44912199857443/100000000000000 : ℝ)^3511
        have hw : |(5380965811/10000000000 : ℝ)|=(5380965811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946391493/5000000000 : ℝ)|^4535 ≤ (11648333848799/100000000000000 : ℝ)^3511
        have hw : |(-946391493/5000000000 : ℝ)|=(946391493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243845957/10000000000 : ℝ)|^4535 ≤ (4343946628273/10000000000000 : ℝ)^3511
        have hw : |(5243845957/10000000000 : ℝ)|=(5243845957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_6 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380967579/10000000000 : ℝ)*x 0 + (1310960997/2500000000 : ℝ)*x 1 + (-1892783239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380967579/10000000000 : ℝ)^4535 ≤ (44912218917879/100000000000000 : ℝ)^3511 := by
    have hnat : (5380967579 : ℕ)^4535*100000000000000^3511 ≤ 44912218917879^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380967579 10000000000 44912218917879 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310960997/2500000000 : ℝ)^4535 ≤ (8687889042913/20000000000000 : ℝ)^3511 := by
    have hnat : (1310960997 : ℕ)^4535*20000000000000^3511 ≤ 8687889042913^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310960997 2500000000 8687889042913 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892783239/10000000000 : ℝ)^4535 ≤ (5824167929941/50000000000000 : ℝ)^3511 := by
    have hnat : (1892783239 : ℕ)^4535*50000000000000^3511 ≤ 5824167929941^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892783239 10000000000 5824167929941 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380967579/10000000000 : ℝ), (1310960997/2500000000 : ℝ), (-1892783239/10000000000 : ℝ)] ![(44912218917879/100000000000000 : ℝ), (8687889042913/20000000000000 : ℝ), (5824167929941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380967579/10000000000 : ℝ)|^4535 ≤ (44912218917879/100000000000000 : ℝ)^3511
        have hw : |(5380967579/10000000000 : ℝ)|=(5380967579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310960997/2500000000 : ℝ)|^4535 ≤ (8687889042913/20000000000000 : ℝ)^3511
        have hw : |(1310960997/2500000000 : ℝ)|=(1310960997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892783239/10000000000 : ℝ)|^4535 ≤ (5824167929941/50000000000000 : ℝ)^3511
        have hw : |(-1892783239/10000000000 : ℝ)|=(1892783239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_7 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (203066029/500000000 : ℝ)*x 0 + (218796433/500000000 : ℝ)*x 1 + (2187964287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203066029/500000000 : ℝ)^4535 ≤ (31227211418993/100000000000000 : ℝ)^3511 := by
    have hnat : (203066029 : ℕ)^4535*100000000000000^3511 ≤ 31227211418993^3511*500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203066029 500000000 31227211418993 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218796433/500000000 : ℝ)^4535 ≤ (6877278943383/20000000000000 : ℝ)^3511 := by
    have hnat : (218796433 : ℕ)^4535*20000000000000^3511 ≤ 6877278943383^3511*500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218796433 500000000 6877278943383 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187964287/5000000000 : ℝ)^4535 ≤ (34386393844021/100000000000000 : ℝ)^3511 := by
    have hnat : (2187964287 : ℕ)^4535*100000000000000^3511 ≤ 34386393844021^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187964287 5000000000 34386393844021 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203066029/500000000 : ℝ), (218796433/500000000 : ℝ), (2187964287/5000000000 : ℝ)] ![(31227211418993/100000000000000 : ℝ), (6877278943383/20000000000000 : ℝ), (34386393844021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203066029/500000000 : ℝ)|^4535 ≤ (31227211418993/100000000000000 : ℝ)^3511
        have hw : |(203066029/500000000 : ℝ)|=(203066029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218796433/500000000 : ℝ)|^4535 ≤ (6877278943383/20000000000000 : ℝ)^3511
        have hw : |(218796433/500000000 : ℝ)|=(218796433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2187964287/5000000000 : ℝ)|^4535 ≤ (34386393844021/100000000000000 : ℝ)^3511
        have hw : |(2187964287/5000000000 : ℝ)|=(2187964287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_8 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99229703/500000000 : ℝ)*x 0 + (5132914961/10000000000 : ℝ)*x 1 + (1084501743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99229703/500000000 : ℝ)^4535 ≤ (193488113423/1562500000000 : ℝ)^3511 := by
    have hnat : (99229703 : ℕ)^4535*1562500000000^3511 ≤ 193488113423^3511*500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99229703 500000000 193488113423 1562500000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132914961/10000000000 : ℝ)^4535 ≤ (10564048067551/25000000000000 : ℝ)^3511 := by
    have hnat : (5132914961 : ℕ)^4535*25000000000000^3511 ≤ 10564048067551^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132914961 10000000000 10564048067551 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084501743/2000000000 : ℝ)^4535 ≤ (45360568458681/100000000000000 : ℝ)^3511 := by
    have hnat : (1084501743 : ℕ)^4535*100000000000000^3511 ≤ 45360568458681^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084501743 2000000000 45360568458681 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99229703/500000000 : ℝ), (5132914961/10000000000 : ℝ), (1084501743/2000000000 : ℝ)] ![(193488113423/1562500000000 : ℝ), (10564048067551/25000000000000 : ℝ), (45360568458681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99229703/500000000 : ℝ)|^4535 ≤ (193488113423/1562500000000 : ℝ)^3511
        have hw : |(-99229703/500000000 : ℝ)|=(99229703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132914961/10000000000 : ℝ)|^4535 ≤ (10564048067551/25000000000000 : ℝ)^3511
        have hw : |(5132914961/10000000000 : ℝ)|=(5132914961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084501743/2000000000 : ℝ)|^4535 ≤ (45360568458681/100000000000000 : ℝ)^3511
        have hw : |(1084501743/2000000000 : ℝ)|=(1084501743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_9 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256638979/10000000000 : ℝ)*x 0 + (-14208783/78125000 : ℝ)*x 1 + (5422508413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256638979/10000000000 : ℝ)^4535 ≤ (43576399418641/100000000000000 : ℝ)^3511 := by
    have hnat : (5256638979 : ℕ)^4535*100000000000000^3511 ≤ 43576399418641^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256638979 10000000000 43576399418641 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14208783/78125000 : ℝ)^4535 ≤ (110630353717/1000000000000 : ℝ)^3511 := by
    have hnat : (14208783 : ℕ)^4535*1000000000000^3511 ≤ 110630353717^3511*78125000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14208783 78125000 110630353717 1000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422508413/10000000000 : ℝ)^4535 ≤ (11340141298893/25000000000000 : ℝ)^3511 := by
    have hnat : (5422508413 : ℕ)^4535*25000000000000^3511 ≤ 11340141298893^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422508413 10000000000 11340141298893 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256638979/10000000000 : ℝ), (-14208783/78125000 : ℝ), (5422508413/10000000000 : ℝ)] ![(43576399418641/100000000000000 : ℝ), (110630353717/1000000000000 : ℝ), (11340141298893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256638979/10000000000 : ℝ)|^4535 ≤ (43576399418641/100000000000000 : ℝ)^3511
        have hw : |(5256638979/10000000000 : ℝ)|=(5256638979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14208783/78125000 : ℝ)|^4535 ≤ (110630353717/1000000000000 : ℝ)^3511
        have hw : |(-14208783/78125000 : ℝ)|=(14208783/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422508413/10000000000 : ℝ)|^4535 ≤ (11340141298893/25000000000000 : ℝ)^3511
        have hw : |(5422508413/10000000000 : ℝ)|=(5422508413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_10 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657079809/1250000000 : ℝ)*x 0 + (677813591/1250000000 : ℝ)*x 1 + (-909362241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657079809/1250000000 : ℝ)^4535 ≤ (43576393989919/100000000000000 : ℝ)^3511 := by
    have hnat : (657079809 : ℕ)^4535*100000000000000^3511 ≤ 43576393989919^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657079809 1250000000 43576393989919 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677813591/1250000000 : ℝ)^4535 ≤ (22680284299573/50000000000000 : ℝ)^3511 := by
    have hnat : (677813591 : ℕ)^4535*50000000000000^3511 ≤ 22680284299573^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677813591 1250000000 22680284299573 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909362241/5000000000 : ℝ)^4535 ≤ (11063037398793/100000000000000 : ℝ)^3511 := by
    have hnat : (909362241 : ℕ)^4535*100000000000000^3511 ≤ 11063037398793^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909362241 5000000000 11063037398793 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657079809/1250000000 : ℝ), (677813591/1250000000 : ℝ), (-909362241/5000000000 : ℝ)] ![(43576393989919/100000000000000 : ℝ), (22680284299573/50000000000000 : ℝ), (11063037398793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657079809/1250000000 : ℝ)|^4535 ≤ (43576393989919/100000000000000 : ℝ)^3511
        have hw : |(657079809/1250000000 : ℝ)|=(657079809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677813591/1250000000 : ℝ)|^4535 ≤ (22680284299573/50000000000000 : ℝ)^3511
        have hw : |(677813591/1250000000 : ℝ)|=(677813591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-909362241/5000000000 : ℝ)|^4535 ≤ (11063037398793/100000000000000 : ℝ)^3511
        have hw : |(-909362241/5000000000 : ℝ)|=(909362241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_11 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4520800803/10000000000 : ℝ)*x 0 + (1036432677/2500000000 : ℝ)*x 1 + (4145731783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4520800803/10000000000 : ℝ)^4535 ≤ (35863880586301/100000000000000 : ℝ)^3511 := by
    have hnat : (4520800803 : ℕ)^4535*100000000000000^3511 ≤ 35863880586301^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520800803 10000000000 35863880586301 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036432677/2500000000 : ℝ)^4535 ≤ (16034027163639/50000000000000 : ℝ)^3511 := by
    have hnat : (1036432677 : ℕ)^4535*50000000000000^3511 ≤ 16034027163639^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036432677 2500000000 16034027163639 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145731783/10000000000 : ℝ)^4535 ≤ (16034032533913/50000000000000 : ℝ)^3511 := by
    have hnat : (4145731783 : ℕ)^4535*50000000000000^3511 ≤ 16034032533913^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145731783 10000000000 16034032533913 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4520800803/10000000000 : ℝ), (1036432677/2500000000 : ℝ), (4145731783/10000000000 : ℝ)] ![(35863880586301/100000000000000 : ℝ), (16034027163639/50000000000000 : ℝ), (16034032533913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4520800803/10000000000 : ℝ)|^4535 ≤ (35863880586301/100000000000000 : ℝ)^3511
        have hw : |(4520800803/10000000000 : ℝ)|=(4520800803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036432677/2500000000 : ℝ)|^4535 ≤ (16034027163639/50000000000000 : ℝ)^3511
        have hw : |(1036432677/2500000000 : ℝ)|=(1036432677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145731783/10000000000 : ℝ)|^4535 ≤ (16034032533913/50000000000000 : ℝ)^3511
        have hw : |(4145731783/10000000000 : ℝ)|=(4145731783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_12 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-434050441/2500000000 : ℝ)*x 0 + (2754732339/5000000000 : ℝ)*x 1 + (41830507/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434050441/2500000000 : ℝ)^4535 ≤ (1302374706467/12500000000000 : ℝ)^3511 := by
    have hnat : (434050441 : ℕ)^4535*12500000000000^3511 ≤ 1302374706467^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434050441 2500000000 1302374706467 12500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754732339/5000000000 : ℝ)^4535 ≤ (11575579091829/25000000000000 : ℝ)^3511 := by
    have hnat : (2754732339 : ℕ)^4535*25000000000000^3511 ≤ 11575579091829^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754732339 5000000000 11575579091829 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41830507/80000000 : ℝ)^4535 ≤ (8655737192957/20000000000000 : ℝ)^3511 := by
    have hnat : (41830507 : ℕ)^4535*20000000000000^3511 ≤ 8655737192957^3511*80000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41830507 80000000 8655737192957 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434050441/2500000000 : ℝ), (2754732339/5000000000 : ℝ), (41830507/80000000 : ℝ)] ![(1302374706467/12500000000000 : ℝ), (11575579091829/25000000000000 : ℝ), (8655737192957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434050441/2500000000 : ℝ)|^4535 ≤ (1302374706467/12500000000000 : ℝ)^3511
        have hw : |(-434050441/2500000000 : ℝ)|=(434050441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754732339/5000000000 : ℝ)|^4535 ≤ (11575579091829/25000000000000 : ℝ)^3511
        have hw : |(2754732339/5000000000 : ℝ)|=(2754732339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41830507/80000000 : ℝ)|^4535 ≤ (8655737192957/20000000000000 : ℝ)^3511
        have hw : |(41830507/80000000 : ℝ)|=(41830507/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_13 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391426743/10000000000 : ℝ)*x 0 + (-949407723/5000000000 : ℝ)*x 1 + (2614406561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391426743/10000000000 : ℝ)^4535 ≤ (45025008918291/100000000000000 : ℝ)^3511 := by
    have hnat : (5391426743 : ℕ)^4535*100000000000000^3511 ≤ 45025008918291^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391426743 10000000000 45025008918291 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949407723/5000000000 : ℝ)^4535 ≤ (2924076951537/25000000000000 : ℝ)^3511 := by
    have hnat : (949407723 : ℕ)^4535*25000000000000^3511 ≤ 2924076951537^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949407723 5000000000 2924076951537 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614406561/5000000000 : ℝ)^4535 ≤ (43278683259967/100000000000000 : ℝ)^3511 := by
    have hnat : (2614406561 : ℕ)^4535*100000000000000^3511 ≤ 43278683259967^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614406561 5000000000 43278683259967 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391426743/10000000000 : ℝ), (-949407723/5000000000 : ℝ), (2614406561/5000000000 : ℝ)] ![(45025008918291/100000000000000 : ℝ), (2924076951537/25000000000000 : ℝ), (43278683259967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391426743/10000000000 : ℝ)|^4535 ≤ (45025008918291/100000000000000 : ℝ)^3511
        have hw : |(5391426743/10000000000 : ℝ)|=(5391426743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-949407723/5000000000 : ℝ)|^4535 ≤ (2924076951537/25000000000000 : ℝ)^3511
        have hw : |(-949407723/5000000000 : ℝ)|=(949407723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614406561/5000000000 : ℝ)|^4535 ≤ (43278683259967/100000000000000 : ℝ)^3511
        have hw : |(2614406561/5000000000 : ℝ)|=(2614406561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_14 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391426713/10000000000 : ℝ)*x 0 + (5228813409/10000000000 : ℝ)*x 1 + (-1898815101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391426713/10000000000 : ℝ)^4535 ≤ (11256252148671/25000000000000 : ℝ)^3511 := by
    have hnat : (5391426713 : ℕ)^4535*25000000000000^3511 ≤ 11256252148671^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391426713 10000000000 11256252148671 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228813409/10000000000 : ℝ)^4535 ≤ (21639343164139/50000000000000 : ℝ)^3511 := by
    have hnat : (5228813409 : ℕ)^4535*50000000000000^3511 ≤ 21639343164139^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228813409 10000000000 21639343164139 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1898815101/10000000000 : ℝ)^4535 ≤ (11696305061217/100000000000000 : ℝ)^3511 := by
    have hnat : (1898815101 : ℕ)^4535*100000000000000^3511 ≤ 11696305061217^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898815101 10000000000 11696305061217 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391426713/10000000000 : ℝ), (5228813409/10000000000 : ℝ), (-1898815101/10000000000 : ℝ)] ![(11256252148671/25000000000000 : ℝ), (21639343164139/50000000000000 : ℝ), (11696305061217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391426713/10000000000 : ℝ)|^4535 ≤ (11256252148671/25000000000000 : ℝ)^3511
        have hw : |(5391426713/10000000000 : ℝ)|=(5391426713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228813409/10000000000 : ℝ)|^4535 ≤ (21639343164139/50000000000000 : ℝ)^3511
        have hw : |(5228813409/10000000000 : ℝ)|=(5228813409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1898815101/10000000000 : ℝ)|^4535 ≤ (11696305061217/100000000000000 : ℝ)^3511
        have hw : |(-1898815101/10000000000 : ℝ)|=(1898815101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_box_15 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4021704337/10000000000 : ℝ)*x 0 + (2197635237/5000000000 : ℝ)*x 1 + (4395270069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4021704337/10000000000 : ℝ)^4535 ≤ (15417162943517/50000000000000 : ℝ)^3511 := by
    have hnat : (4021704337 : ℕ)^4535*50000000000000^3511 ≤ 15417162943517^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021704337 10000000000 15417162943517 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197635237/5000000000 : ℝ)^4535 ≤ (1383313564161/4000000000000 : ℝ)^3511 := by
    have hnat : (2197635237 : ℕ)^4535*4000000000000^3511 ≤ 1383313564161^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197635237 5000000000 1383313564161 4000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4395270069/10000000000 : ℝ)^4535 ≤ (17291417494007/50000000000000 : ℝ)^3511 := by
    have hnat : (4395270069 : ℕ)^4535*50000000000000^3511 ≤ 17291417494007^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395270069 10000000000 17291417494007 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4021704337/10000000000 : ℝ), (2197635237/5000000000 : ℝ), (4395270069/10000000000 : ℝ)] ![(15417162943517/50000000000000 : ℝ), (1383313564161/4000000000000 : ℝ), (17291417494007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4021704337/10000000000 : ℝ)|^4535 ≤ (15417162943517/50000000000000 : ℝ)^3511
        have hw : |(4021704337/10000000000 : ℝ)|=(4021704337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197635237/5000000000 : ℝ)|^4535 ≤ (1383313564161/4000000000000 : ℝ)^3511
        have hw : |(2197635237/5000000000 : ℝ)|=(2197635237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4395270069/10000000000 : ℝ)|^4535 ≤ (17291417494007/50000000000000 : ℝ)^3511
        have hw : |(4395270069/10000000000 : ℝ)|=(4395270069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1519_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63749/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58661/100000 : ℝ) ∧ (40197/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86047/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10943/100000 : ℝ) ^ (4533/1024 : ℝ) ≤ (1115628355865213/20000000000000000000 : ℝ) := by
    have hpowers : (10943/100000 : ℝ)^4533 ≤ (1115628355865213/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10943 : ℕ)^4533*20000000000000000000^1024 ≤ 1115628355865213^1024*100000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10943 100000 1115628355865213 20000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10943/100000 : ℝ)) (X := (1115628355865213/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4533/1024 : ℝ) ≤ (1296148614765947/5000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4533 ≤ (1296148614765947/5000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4533*5000000000000000000^1024 ≤ 1296148614765947^1024*100000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 1296148614765947 5000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (1296148614765947/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001115628355865213/10000000000000000000 : ℝ) ≤ (1250031501050909/1250000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (10001115628355865213/10000000000000000000 : ℝ)^1024 ≤ (1250031501050909/1250000000000000 : ℝ)^4533 := by
      have hnat : (10001115628355865213 : ℕ)^1024*1250000000000000^4533 ≤ 1250031501050909^4533*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001115628355865213 10000000000000000000 1250031501050909 1250000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250031501050909/1250000000000000 : ℝ)) (X := (10001115628355865213/10000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006300222814929001/20000000000000000000 : ℝ) ≤ (1000071152015411/1000000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (20006300222814929001/20000000000000000000 : ℝ)^1024 ≤ (1000071152015411/1000000000000000 : ℝ)^4533 := by
      have hnat : (20006300222814929001 : ℕ)^1024*1000000000000000^4533 ≤ 1000071152015411^4533*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006300222814929001 20000000000000000000 1000071152015411 1000000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000071152015411/1000000000000000 : ℝ)) (X := (20006300222814929001/20000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501296148614765947/2500000000000000000 : ℝ) ≤ (2500292757975237/2500000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (2501296148614765947/2500000000000000000 : ℝ)^1024 ≤ (2500292757975237/2500000000000000 : ℝ)^4533 := by
      have hnat : (2501296148614765947 : ℕ)^1024*2500000000000000^4533 ≤ 2500292757975237^4533*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501296148614765947 2500000000000000000 2500292757975237 2500000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500292757975237/2500000000000000 : ℝ)) (X := (2501296148614765947/2500000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1115628355865213/20000000000000000000 : ℝ) ≤ ((11347771811019429603/11350000000000000000 : ℝ)+2*(229755873419/227000000000000 : ℝ)*(10943/100000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (11347771811019429603/11350000000000000000 : ℝ)+2*(229755873419/227000000000000 : ℝ)*(10943/100000 : ℝ)=(1250031501050909/1250000000000000 : ℝ) by norm_num, show 1+2*(1115628355865213/20000000000000000000 : ℝ)=(10001115628355865213/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1296148614765947/5000000000000000000 : ℝ)+(1115628355865213/20000000000000000000 : ℝ) ≤ ((11347771811019429603/11350000000000000000 : ℝ)+(229755873419/227000000000000 : ℝ)*((15483/100000 : ℝ)+(10943/100000 : ℝ)))^(4533/1024 : ℝ) := by
    rw [show (11347771811019429603/11350000000000000000 : ℝ)+(229755873419/227000000000000 : ℝ)*((15483/100000 : ℝ)+(10943/100000 : ℝ))=(1000071152015411/1000000000000000 : ℝ) by norm_num, show 1+(1296148614765947/5000000000000000000 : ℝ)+(1115628355865213/20000000000000000000 : ℝ)=(20006300222814929001/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1296148614765947/5000000000000000000 : ℝ) ≤ ((11347771811019429603/11350000000000000000 : ℝ)+2*(229755873419/227000000000000 : ℝ)*(15483/100000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (11347771811019429603/11350000000000000000 : ℝ)+2*(229755873419/227000000000000 : ℝ)*(15483/100000 : ℝ)=(2500292757975237/2500000000000000 : ℝ) by norm_num, show 1+2*(1296148614765947/5000000000000000000 : ℝ)=(2501296148614765947/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11347771811019429603/11350000000000000000 : ℝ)*(X 1 0+X 2 0)+(229755873419/227000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (11347771811019429603/11350000000000000000 : ℝ)) (alpha := (229755873419/227000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11347771811019429603/11350000000000000000 : ℝ)*(X 0 1+X 2 1)+(229755873419/227000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (11347771811019429603/11350000000000000000 : ℝ)) (alpha := (229755873419/227000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11347771811019429603/11350000000000000000 : ℝ)*(X 0 2+X 1 2)+(229755873419/227000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (11347771811019429603/11350000000000000000 : ℝ)) (alpha := (229755873419/227000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-329068309/2000000000 : ℝ)*X 0 0+(675259549/1250000000 : ℝ)*X 0 1+(54020767/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((131771553/250000000 : ℝ)*X 1 0+(-913704697/5000000000 : ℝ)*X 1 1+(5402076877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317715313/2500000000 : ℝ)*X 2 0+(5402077159/10000000000 : ℝ)*X 2 1+(-182741019/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((139664797/312500000 : ℝ)*X 0 0+(32594423/78125000 : ℝ)*X 0 1+(2086042477/5000000000 : ℝ)*X 0 2+(139664797/312500000 : ℝ)*X 1 0+(32594423/78125000 : ℝ)*X 1 1+(2086042477/5000000000 : ℝ)*X 1 2+(139664797/312500000 : ℝ)*X 2 0+(32594423/78125000 : ℝ)*X 2 1+(2086042477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2075542183/10000000000 : ℝ)*X 0 0+(819351/1562500 : ℝ)*X 0 1+(5243843987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380965811/10000000000 : ℝ)*X 1 0+(-946391493/5000000000 : ℝ)*X 1 1+(5243845957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380967579/10000000000 : ℝ)*X 2 0+(1310960997/2500000000 : ℝ)*X 2 1+(-1892783239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((203066029/500000000 : ℝ)*X 0 0+(218796433/500000000 : ℝ)*X 0 1+(2187964287/5000000000 : ℝ)*X 0 2+(203066029/500000000 : ℝ)*X 1 0+(218796433/500000000 : ℝ)*X 1 1+(2187964287/5000000000 : ℝ)*X 1 2+(203066029/500000000 : ℝ)*X 2 0+(218796433/500000000 : ℝ)*X 2 1+(2187964287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-99229703/500000000 : ℝ)*X 0 0+(5132914961/10000000000 : ℝ)*X 0 1+(1084501743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256638979/10000000000 : ℝ)*X 1 0+(-14208783/78125000 : ℝ)*X 1 1+(5422508413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((657079809/1250000000 : ℝ)*X 2 0+(677813591/1250000000 : ℝ)*X 2 1+(-909362241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4520800803/10000000000 : ℝ)*X 0 0+(1036432677/2500000000 : ℝ)*X 0 1+(4145731783/10000000000 : ℝ)*X 0 2+(4520800803/10000000000 : ℝ)*X 1 0+(1036432677/2500000000 : ℝ)*X 1 1+(4145731783/10000000000 : ℝ)*X 1 2+(4520800803/10000000000 : ℝ)*X 2 0+(1036432677/2500000000 : ℝ)*X 2 1+(4145731783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-434050441/2500000000 : ℝ)*X 0 0+(2754732339/5000000000 : ℝ)*X 0 1+(41830507/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5391426743/10000000000 : ℝ)*X 1 0+(-949407723/5000000000 : ℝ)*X 1 1+(2614406561/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391426713/10000000000 : ℝ)*X 2 0+(5228813409/10000000000 : ℝ)*X 2 1+(-1898815101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4021704337/10000000000 : ℝ)*X 0 0+(2197635237/5000000000 : ℝ)*X 0 1+(4395270069/10000000000 : ℝ)*X 0 2+(4021704337/10000000000 : ℝ)*X 1 0+(2197635237/5000000000 : ℝ)*X 1 1+(4395270069/10000000000 : ℝ)*X 1 2+(4021704337/10000000000 : ℝ)*X 2 0+(2197635237/5000000000 : ℝ)*X 2 1+(4395270069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63749/100000 : ℝ) ≤ (-180879716854939419043477010838507/283750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116085517/100000000000000 : ℝ)*(upper1) + (93897253/100000000000000 : ℝ)*(upper4) + (29722497/10000000000000 : ℝ)*(upper5) + (2233740409860123/100000000000000 : ℝ)*(major0) + (2233740409860123/100000000000000 : ℝ)*(major1) + (2233740409860123/100000000000000 : ℝ)*(major2) + (39230943817/100000000000000 : ℝ)*(sp2) + (8338792057/100000000000000 : ℝ)*(sp3) + (3126144893285473/100000000000000 : ℝ)*(sp4) + (195384876844383/6250000000000 : ℝ)*(sp5) + (1563072234904269/50000000000000 : ℝ)*(sp6) + (1362537498749097/100000000000000 : ℝ)*(sp7) + (19403733441/50000000000000 : ℝ)*(sp8) + (12835621113/50000000000000 : ℝ)*(sp13) + (681272918770577/50000000000000 : ℝ)*(f.failure) + (1563091850376177/50000000000000 : ℝ)*(f.sum) + (63951672243387/11350000000000000000000000000 : ℝ)*base65 + (1023129701952271169/1135000000000000000000000000000000 : ℝ)*base67 + (3704529503492728831/1135000000000000000000000000000000 : ℝ)*base70 + (15245689075612271169/1135000000000000000000000000000000 : ℝ)*base71 + (6501497321863/11350000000000000000000000000 : ℝ)*base74 + (5638490190262271169/1135000000000000000000000000000000 : ℝ)*base75 + (3219019486512271169/1135000000000000000000000000000000 : ℝ)*base77 + (526934209877271169/1135000000000000000000000000000000 : ℝ)*base79 + (15000566701137/11350000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (279981/1000000000000000000000 : ℝ)*base90 + (279981/1000000000000000000000 : ℝ)*base92 + (279981/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58661/100000 : ℝ) ≤ (166456486883792736552677555763333/283750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (176034251/100000000000000 : ℝ)*(lower0) + (21021711/100000000000000 : ℝ)*(upper1) + (2894361/1000000000000 : ℝ)*(upper2) + (54295787/25000000000000 : ℝ)*(upper3) + (1155221627587121/50000000000000 : ℝ)*(major0) + (1155221627587121/50000000000000 : ℝ)*(major1) + (1155221627587121/50000000000000 : ℝ)*(major2) + (3191990746472631/100000000000000 : ℝ)*(sp0) + (1595999403606227/50000000000000 : ℝ)*(sp1) + (319199010947327/10000000000000 : ℝ)*(sp2) + (704666398067653/50000000000000 : ℝ)*(sp3) + (547308049/100000000000000 : ℝ)*(sp7) + (8697739183/100000000000000 : ℝ)*(sp10) + (4030369911/50000000000000 : ℝ)*(sp12) + (281866668688671/20000000000000 : ℝ)*(f.failure) + (1595999403606227/50000000000000 : ℝ)*(f.sum) + (273730473369/1418750000000000000000000000 : ℝ)*base66 + (9562255371083892963/567500000000000000000000000000000 : ℝ)*base67 + (7897110531943892963/567500000000000000000000000000000 : ℝ)*base69 + (7144986821573892963/567500000000000000000000000000000 : ℝ)*base71 + (8865766284701/5675000000000000000000000000 : ℝ)*base74 + (3471570056403892963/567500000000000000000000000000000 : ℝ)*base75 + (7615137907893892963/567500000000000000000000000000000 : ℝ)*base77 + (9552667750278892963/567500000000000000000000000000000 : ℝ)*base79 + (6712030100501/5675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1485763/400000000000000000000 : ℝ)*base90 + (1485763/400000000000000000000 : ℝ)*base92 + (1485763/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40197/50000 : ℝ) ≤ (114062772851448535158771141957759/141875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91275029/50000000000000 : ℝ)*(upper0) + (840697/800000000000 : ℝ)*(upper1) + (178998991/100000000000000 : ℝ)*(upper2) + (1251752026488449/50000000000000 : ℝ)*(major0) + (1251752026488449/50000000000000 : ℝ)*(major1) + (1251752026488449/50000000000000 : ℝ)*(major2) + (2362160231/5000000000000 : ℝ)*(sp1) + (278024309/625000000000 : ℝ)*(sp2) + (17057467229/100000000000000 : ℝ)*(sp3) + (5357631481/100000000000000 : ℝ)*(sp4) + (1726553262053079/50000000000000 : ℝ)*(sp8) + (1726532319266509/50000000000000 : ℝ)*(sp9) + (3453067397848199/100000000000000 : ℝ)*(sp10) + (763540138692939/50000000000000 : ℝ)*(sp11) + (1527097334853107/100000000000000 : ℝ)*(f.failure) + (3453111881737639/100000000000000 : ℝ)*(f.sum) + (519446931047/2837500000000000000000000000 : ℝ)*base66 + (3448291691339705747/567500000000000000000000000000000 : ℝ)*base67 + (1522145719057205747/567500000000000000000000000000000 : ℝ)*base69 + (5685434216544705747/567500000000000000000000000000000 : ℝ)*base71 + (41681611397269/5675000000000000000000000000 : ℝ)*base74 + (6277267684709705747/567500000000000000000000000000000 : ℝ)*base75 + (3606688647989705747/567500000000000000000000000000000 : ℝ)*base77 + (5111273123255294253/567500000000000000000000000000000 : ℝ)*base80 + (6067026317281/5675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5520071/2000000000000000000000 : ℝ)*base90 + (5520071/2000000000000000000000 : ℝ)*base92 + (5520071/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-86047/100000 : ℝ) ≤ (-244150488340337789735357080736997/283750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12509887/20000000000000 : ℝ)*(lower0) + (9281289/12500000000000 : ℝ)*(lower2) + (894527/5000000000000 : ℝ)*(upper3) + (91569599/100000000000000 : ℝ)*(upper5) + (1271371758686911/50000000000000 : ℝ)*(major0) + (1271371758686911/50000000000000 : ℝ)*(major1) + (1271371758686911/50000000000000 : ℝ)*(major2) + (161884997/20000000000000 : ℝ)*(sp0) + (8119708537/10000000000000 : ℝ)*(sp5) + (276136883/10000000000000 : ℝ)*(sp7) + (3563134854616591/100000000000000 : ℝ)*(sp12) + (1781527233478103/50000000000000 : ℝ)*(sp13) + (445391958005197/12500000000000 : ℝ)*(sp14) + (775515008829577/50000000000000 : ℝ)*(sp15) + (96939548689249/6250000000000 : ℝ)*(f.failure) + (445391958005197/12500000000000 : ℝ)*(f.sum) + (5818225895933/2837500000000000000000000000 : ℝ)*base66 + (1062988199472476333/567500000000000000000000000000000 : ℝ)*base67 + (1419179258374976333/567500000000000000000000000000000 : ℝ)*base69 + (2535048688662476333/567500000000000000000000000000000 : ℝ)*base71 + (13089876898791/5675000000000000000000000000 : ℝ)*base74 + (1642530178327476333/567500000000000000000000000000000 : ℝ)*base75 + (3254344973362476333/567500000000000000000000000000000 : ℝ)*base77 + (3439924627267476333/567500000000000000000000000000000 : ℝ)*base79 + (12258811568541/5675000000000000000000000000 : ℝ)*base82 + (332003/125000000000000000000 : ℝ)*base89 + (332003/125000000000000000000 : ℝ)*base91 + (332003/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1519_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58661/100000 : ℝ) else (40197/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86047/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1519_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1519_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58661/100000 : ℝ) else (40197/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86047/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1519_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1519_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58661/100000 : ℝ) else (40197/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86047/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1519_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

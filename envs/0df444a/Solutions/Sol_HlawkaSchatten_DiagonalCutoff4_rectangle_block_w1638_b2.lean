-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1638_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:39.673168+00:00
-- url     : https://prove2.me/submissions/6742a499-03a2-4935-85df-2f85f34e23f2

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
theorem support_rectangle_w1638_box_0 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-686953937/5000000000 : ℝ)*x 0 + (2705516797/5000000000 : ℝ)*x 1 + (2705516797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686953937/5000000000 : ℝ)^4871 ≤ (8100240778507/100000000000000 : ℝ)^3847 := by
    have hnat : (686953937 : ℕ)^4871*100000000000000^3847 ≤ 8100240778507^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686953937 5000000000 8100240778507 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705516797/5000000000 : ℝ)^4871 ≤ (11487469901157/25000000000000 : ℝ)^3847 := by
    have hnat : (2705516797 : ℕ)^4871*25000000000000^3847 ≤ 11487469901157^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705516797 5000000000 11487469901157 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705516797/5000000000 : ℝ)^4871 ≤ (11487469901157/25000000000000 : ℝ)^3847 := by
    have hnat : (2705516797 : ℕ)^4871*25000000000000^3847 ≤ 11487469901157^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705516797 5000000000 11487469901157 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-686953937/5000000000 : ℝ), (2705516797/5000000000 : ℝ), (2705516797/5000000000 : ℝ)] ![(8100240778507/100000000000000 : ℝ), (11487469901157/25000000000000 : ℝ), (11487469901157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-686953937/5000000000 : ℝ)|^4871 ≤ (8100240778507/100000000000000 : ℝ)^3847
        have hw : |(-686953937/5000000000 : ℝ)|=(686953937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705516797/5000000000 : ℝ)|^4871 ≤ (11487469901157/25000000000000 : ℝ)^3847
        have hw : |(2705516797/5000000000 : ℝ)|=(2705516797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705516797/5000000000 : ℝ)|^4871 ≤ (11487469901157/25000000000000 : ℝ)^3847
        have hw : |(2705516797/5000000000 : ℝ)|=(2705516797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_1 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312803077/2500000000 : ℝ)*x 0 + (-1598489797/10000000000 : ℝ)*x 1 + (5411033389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312803077/2500000000 : ℝ)^4871 ≤ (11059560720927/25000000000000 : ℝ)^3847 := by
    have hnat : (1312803077 : ℕ)^4871*25000000000000^3847 ≤ 11059560720927^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312803077 2500000000 11059560720927 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1598489797/10000000000 : ℝ)^4871 ≤ (1226484961969/12500000000000 : ℝ)^3847 := by
    have hnat : (1598489797 : ℕ)^4871*12500000000000^3847 ≤ 1226484961969^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598489797 10000000000 1226484961969 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411033389/10000000000 : ℝ)^4871 ≤ (45949877400413/100000000000000 : ℝ)^3847 := by
    have hnat : (5411033389 : ℕ)^4871*100000000000000^3847 ≤ 45949877400413^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411033389 10000000000 45949877400413 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312803077/2500000000 : ℝ), (-1598489797/10000000000 : ℝ), (5411033389/10000000000 : ℝ)] ![(11059560720927/25000000000000 : ℝ), (1226484961969/12500000000000 : ℝ), (45949877400413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312803077/2500000000 : ℝ)|^4871 ≤ (11059560720927/25000000000000 : ℝ)^3847
        have hw : |(1312803077/2500000000 : ℝ)|=(1312803077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1598489797/10000000000 : ℝ)|^4871 ≤ (1226484961969/12500000000000 : ℝ)^3847
        have hw : |(-1598489797/10000000000 : ℝ)|=(1598489797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411033389/10000000000 : ℝ)|^4871 ≤ (45949877400413/100000000000000 : ℝ)^3847
        have hw : |(5411033389/10000000000 : ℝ)|=(5411033389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_2 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251212339/10000000000 : ℝ)*x 0 + (5411033323/10000000000 : ℝ)*x 1 + (-1598489847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251212339/10000000000 : ℝ)^4871 ≤ (44238243214379/100000000000000 : ℝ)^3847 := by
    have hnat : (5251212339 : ℕ)^4871*100000000000000^3847 ≤ 44238243214379^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251212339 10000000000 44238243214379 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411033323/10000000000 : ℝ)^4871 ≤ (45949876690763/100000000000000 : ℝ)^3847 := by
    have hnat : (5411033323 : ℕ)^4871*100000000000000^3847 ≤ 45949876690763^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411033323 10000000000 45949876690763 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1598489847/10000000000 : ℝ)^4871 ≤ (9811880084357/100000000000000 : ℝ)^3847 := by
    have hnat : (1598489847 : ℕ)^4871*100000000000000^3847 ≤ 9811880084357^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598489847 10000000000 9811880084357 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251212339/10000000000 : ℝ), (5411033323/10000000000 : ℝ), (-1598489847/10000000000 : ℝ)] ![(44238243214379/100000000000000 : ℝ), (45949876690763/100000000000000 : ℝ), (9811880084357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251212339/10000000000 : ℝ)|^4871 ≤ (44238243214379/100000000000000 : ℝ)^3847
        have hw : |(5251212339/10000000000 : ℝ)|=(5251212339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411033323/10000000000 : ℝ)|^4871 ≤ (45949876690763/100000000000000 : ℝ)^3847
        have hw : |(5411033323/10000000000 : ℝ)|=(5411033323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1598489847/10000000000 : ℝ)|^4871 ≤ (9811880084357/100000000000000 : ℝ)^3847
        have hw : |(-1598489847/10000000000 : ℝ)|=(1598489847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_3 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4467680863/10000000000 : ℝ)*x 0 + (2031727483/5000000000 : ℝ)*x 1 + (4063455119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4467680863/10000000000 : ℝ)^4871 ≤ (36052924886879/100000000000000 : ℝ)^3847 := by
    have hnat : (4467680863 : ℕ)^4871*100000000000000^3847 ≤ 36052924886879^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467680863 10000000000 36052924886879 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2031727483/5000000000 : ℝ)^4871 ≤ (31973536787199/100000000000000 : ℝ)^3847 := by
    have hnat : (2031727483 : ℕ)^4871*100000000000000^3847 ≤ 31973536787199^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031727483 5000000000 31973536787199 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4063455119/10000000000 : ℝ)^4871 ≤ (15986769155771/50000000000000 : ℝ)^3847 := by
    have hnat : (4063455119 : ℕ)^4871*50000000000000^3847 ≤ 15986769155771^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4063455119 10000000000 15986769155771 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4467680863/10000000000 : ℝ), (2031727483/5000000000 : ℝ), (4063455119/10000000000 : ℝ)] ![(36052924886879/100000000000000 : ℝ), (31973536787199/100000000000000 : ℝ), (15986769155771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4467680863/10000000000 : ℝ)|^4871 ≤ (36052924886879/100000000000000 : ℝ)^3847
        have hw : |(4467680863/10000000000 : ℝ)|=(4467680863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2031727483/5000000000 : ℝ)|^4871 ≤ (31973536787199/100000000000000 : ℝ)^3847
        have hw : |(2031727483/5000000000 : ℝ)|=(2031727483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4063455119/10000000000 : ℝ)|^4871 ≤ (15986769155771/50000000000000 : ℝ)^3847
        have hw : |(4063455119/10000000000 : ℝ)|=(4063455119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_4 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909288701/10000000000 : ℝ)*x 0 + (1303845527/2500000000 : ℝ)*x 1 + (2607691289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909288701/10000000000 : ℝ)^4871 ≤ (6143600602589/50000000000000 : ℝ)^3847 := by
    have hnat : (1909288701 : ℕ)^4871*50000000000000^3847 ≤ 6143600602589^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909288701 10000000000 6143600602589 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303845527/2500000000 : ℝ)^4871 ≤ (43856396887827/100000000000000 : ℝ)^3847 := by
    have hnat : (1303845527 : ℕ)^4871*100000000000000^3847 ≤ 43856396887827^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303845527 2500000000 43856396887827 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607691289/5000000000 : ℝ)^4871 ≤ (171314069891/390625000000 : ℝ)^3847 := by
    have hnat : (2607691289 : ℕ)^4871*390625000000^3847 ≤ 171314069891^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607691289 5000000000 171314069891 390625000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909288701/10000000000 : ℝ), (1303845527/2500000000 : ℝ), (2607691289/5000000000 : ℝ)] ![(6143600602589/50000000000000 : ℝ), (43856396887827/100000000000000 : ℝ), (171314069891/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909288701/10000000000 : ℝ)|^4871 ≤ (6143600602589/50000000000000 : ℝ)^3847
        have hw : |(-1909288701/10000000000 : ℝ)|=(1909288701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303845527/2500000000 : ℝ)|^4871 ≤ (43856396887827/100000000000000 : ℝ)^3847
        have hw : |(1303845527/2500000000 : ℝ)|=(1303845527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607691289/5000000000 : ℝ)|^4871 ≤ (171314069891/390625000000 : ℝ)^3847
        have hw : |(2607691289/5000000000 : ℝ)|=(2607691289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_5 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692860589/5000000000 : ℝ)*x 0 + (-336408339/2000000000 : ℝ)*x 1 + (5215382629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692860589/5000000000 : ℝ)^4871 ≤ (11419470839829/25000000000000 : ℝ)^3847 := by
    have hnat : (2692860589 : ℕ)^4871*25000000000000^3847 ≤ 11419470839829^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692860589 5000000000 11419470839829 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336408339/2000000000 : ℝ)^4871 ≤ (5232857092749/50000000000000 : ℝ)^3847 := by
    have hnat : (336408339 : ℕ)^4871*50000000000000^3847 ≤ 5232857092749^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336408339 2000000000 5232857092749 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215382629/10000000000 : ℝ)^4871 ≤ (5482050304389/12500000000000 : ℝ)^3847 := by
    have hnat : (5215382629 : ℕ)^4871*12500000000000^3847 ≤ 5482050304389^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215382629 10000000000 5482050304389 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692860589/5000000000 : ℝ), (-336408339/2000000000 : ℝ), (5215382629/10000000000 : ℝ)] ![(11419470839829/25000000000000 : ℝ), (5232857092749/50000000000000 : ℝ), (5482050304389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692860589/5000000000 : ℝ)|^4871 ≤ (11419470839829/25000000000000 : ℝ)^3847
        have hw : |(2692860589/5000000000 : ℝ)|=(2692860589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336408339/2000000000 : ℝ)|^4871 ≤ (5232857092749/50000000000000 : ℝ)^3847
        have hw : |(-336408339/2000000000 : ℝ)|=(336408339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215382629/10000000000 : ℝ)|^4871 ≤ (5482050304389/12500000000000 : ℝ)^3847
        have hw : |(5215382629/10000000000 : ℝ)|=(5215382629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_6 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692860721/5000000000 : ℝ)*x 0 + (5215382029/10000000000 : ℝ)*x 1 + (-1682042147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692860721/5000000000 : ℝ)^4871 ≤ (22838943097187/50000000000000 : ℝ)^3847 := by
    have hnat : (2692860721 : ℕ)^4871*50000000000000^3847 ≤ 22838943097187^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692860721 5000000000 22838943097187 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215382029/10000000000 : ℝ)^4871 ≤ (10964099011671/25000000000000 : ℝ)^3847 := by
    have hnat : (5215382029 : ℕ)^4871*25000000000000^3847 ≤ 10964099011671^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215382029 10000000000 10964099011671 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1682042147/10000000000 : ℝ)^4871 ≤ (5232858873227/50000000000000 : ℝ)^3847 := by
    have hnat : (1682042147 : ℕ)^4871*50000000000000^3847 ≤ 5232858873227^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682042147 10000000000 5232858873227 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692860721/5000000000 : ℝ), (5215382029/10000000000 : ℝ), (-1682042147/10000000000 : ℝ)] ![(22838943097187/50000000000000 : ℝ), (10964099011671/25000000000000 : ℝ), (5232858873227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692860721/5000000000 : ℝ)|^4871 ≤ (22838943097187/50000000000000 : ℝ)^3847
        have hw : |(2692860721/5000000000 : ℝ)|=(2692860721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215382029/10000000000 : ℝ)|^4871 ≤ (10964099011671/25000000000000 : ℝ)^3847
        have hw : |(5215382029/10000000000 : ℝ)|=(5215382029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1682042147/10000000000 : ℝ)|^4871 ≤ (5232858873227/50000000000000 : ℝ)^3847
        have hw : |(-1682042147/10000000000 : ℝ)|=(1682042147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_7 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (78121859/200000000 : ℝ)*x 0 + (542989887/1250000000 : ℝ)*x 1 + (2171959353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78121859/200000000 : ℝ)^4871 ≤ (30413893716319/100000000000000 : ℝ)^3847 := by
    have hnat : (78121859 : ℕ)^4871*100000000000000^3847 ≤ 30413893716319^3847*200000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78121859 200000000 30413893716319 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542989887/1250000000 : ℝ)^4871 ≤ (34793055109887/100000000000000 : ℝ)^3847 := by
    have hnat : (542989887 : ℕ)^4871*100000000000000^3847 ≤ 34793055109887^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542989887 1250000000 34793055109887 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171959353/5000000000 : ℝ)^4871 ≤ (34793051154661/100000000000000 : ℝ)^3847 := by
    have hnat : (2171959353 : ℕ)^4871*100000000000000^3847 ≤ 34793051154661^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171959353 5000000000 34793051154661 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(78121859/200000000 : ℝ), (542989887/1250000000 : ℝ), (2171959353/5000000000 : ℝ)] ![(30413893716319/100000000000000 : ℝ), (34793055109887/100000000000000 : ℝ), (34793051154661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(78121859/200000000 : ℝ)|^4871 ≤ (30413893716319/100000000000000 : ℝ)^3847
        have hw : |(78121859/200000000 : ℝ)|=(78121859/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542989887/1250000000 : ℝ)|^4871 ≤ (34793055109887/100000000000000 : ℝ)^3847
        have hw : |(542989887/1250000000 : ℝ)|=(542989887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2171959353/5000000000 : ℝ)|^4871 ≤ (34793051154661/100000000000000 : ℝ)^3847
        have hw : |(2171959353/5000000000 : ℝ)|=(2171959353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_8 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-448796987/2500000000 : ℝ)*x 0 + (5074955933/10000000000 : ℝ)*x 1 + (5440637707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448796987/2500000000 : ℝ)^4871 ≤ (11364957849873/100000000000000 : ℝ)^3847 := by
    have hnat : (448796987 : ℕ)^4871*100000000000000^3847 ≤ 11364957849873^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448796987 2500000000 11364957849873 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074955933/10000000000 : ℝ)^4871 ≤ (42366619703389/100000000000000 : ℝ)^3847 := by
    have hnat : (5074955933 : ℕ)^4871*100000000000000^3847 ≤ 42366619703389^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074955933 10000000000 42366619703389 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440637707/10000000000 : ℝ)^4871 ≤ (9253684487461/20000000000000 : ℝ)^3847 := by
    have hnat : (5440637707 : ℕ)^4871*20000000000000^3847 ≤ 9253684487461^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440637707 10000000000 9253684487461 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448796987/2500000000 : ℝ), (5074955933/10000000000 : ℝ), (5440637707/10000000000 : ℝ)] ![(11364957849873/100000000000000 : ℝ), (42366619703389/100000000000000 : ℝ), (9253684487461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448796987/2500000000 : ℝ)|^4871 ≤ (11364957849873/100000000000000 : ℝ)^3847
        have hw : |(-448796987/2500000000 : ℝ)|=(448796987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074955933/10000000000 : ℝ)|^4871 ≤ (42366619703389/100000000000000 : ℝ)^3847
        have hw : |(5074955933/10000000000 : ℝ)|=(5074955933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440637707/10000000000 : ℝ)|^4871 ≤ (9253684487461/20000000000000 : ℝ)^3847
        have hw : |(5440637707/10000000000 : ℝ)|=(5440637707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_9 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615429533/5000000000 : ℝ)*x 0 + (-1585409061/10000000000 : ℝ)*x 1 + (1360159443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615429533/5000000000 : ℝ)^4871 ≤ (44021250979757/100000000000000 : ℝ)^3847 := by
    have hnat : (2615429533 : ℕ)^4871*100000000000000^3847 ≤ 44021250979757^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615429533 5000000000 44021250979757 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1585409061/10000000000 : ℝ)^4871 ≤ (4855162937389/50000000000000 : ℝ)^3847 := by
    have hnat : (1585409061 : ℕ)^4871*50000000000000^3847 ≤ 4855162937389^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585409061 10000000000 4855162937389 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360159443/2500000000 : ℝ)^4871 ≤ (23134211568609/50000000000000 : ℝ)^3847 := by
    have hnat : (1360159443 : ℕ)^4871*50000000000000^3847 ≤ 23134211568609^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360159443 2500000000 23134211568609 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615429533/5000000000 : ℝ), (-1585409061/10000000000 : ℝ), (1360159443/2500000000 : ℝ)] ![(44021250979757/100000000000000 : ℝ), (4855162937389/50000000000000 : ℝ), (23134211568609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615429533/5000000000 : ℝ)|^4871 ≤ (44021250979757/100000000000000 : ℝ)^3847
        have hw : |(2615429533/5000000000 : ℝ)|=(2615429533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1585409061/10000000000 : ℝ)|^4871 ≤ (4855162937389/50000000000000 : ℝ)^3847
        have hw : |(-1585409061/10000000000 : ℝ)|=(1585409061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360159443/2500000000 : ℝ)|^4871 ≤ (23134211568609/50000000000000 : ℝ)^3847
        have hw : |(1360159443/2500000000 : ℝ)|=(1360159443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_10 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326928683/625000000 : ℝ)*x 0 + (5440637891/10000000000 : ℝ)*x 1 + (-317081817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326928683/625000000 : ℝ)^4871 ≤ (44021249509259/100000000000000 : ℝ)^3847 := by
    have hnat : (326928683 : ℕ)^4871*100000000000000^3847 ≤ 44021249509259^3847*625000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326928683 625000000 44021249509259 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440637891/10000000000 : ℝ)^4871 ≤ (23134212209299/50000000000000 : ℝ)^3847 := by
    have hnat : (5440637891 : ℕ)^4871*50000000000000^3847 ≤ 23134212209299^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440637891 10000000000 23134212209299 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317081817/2000000000 : ℝ)^4871 ≤ (9710326060901/100000000000000 : ℝ)^3847 := by
    have hnat : (317081817 : ℕ)^4871*100000000000000^3847 ≤ 9710326060901^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317081817 2000000000 9710326060901 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326928683/625000000 : ℝ), (5440637891/10000000000 : ℝ), (-317081817/2000000000 : ℝ)] ![(44021249509259/100000000000000 : ℝ), (23134212209299/50000000000000 : ℝ), (9710326060901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326928683/625000000 : ℝ)|^4871 ≤ (44021249509259/100000000000000 : ℝ)^3847
        have hw : |(326928683/625000000 : ℝ)|=(326928683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440637891/10000000000 : ℝ)|^4871 ≤ (23134212209299/50000000000000 : ℝ)^3847
        have hw : |(5440637891/10000000000 : ℝ)|=(5440637891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-317081817/2000000000 : ℝ)|^4871 ≤ (9710326060901/100000000000000 : ℝ)^3847
        have hw : |(-317081817/2000000000 : ℝ)|=(317081817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_11 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2275135177/5000000000 : ℝ)*x 0 + (4020941603/10000000000 : ℝ)*x 1 + (4020941447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2275135177/5000000000 : ℝ)^4871 ≤ (36898868664843/100000000000000 : ℝ)^3847 := by
    have hnat : (2275135177 : ℕ)^4871*100000000000000^3847 ≤ 36898868664843^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275135177 5000000000 36898868664843 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4020941603/10000000000 : ℝ)^4871 ≤ (7887641609669/25000000000000 : ℝ)^3847 := by
    have hnat : (4020941603 : ℕ)^4871*25000000000000^3847 ≤ 7887641609669^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020941603 10000000000 7887641609669 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020941447/10000000000 : ℝ)^4871 ≤ (31550564888789/100000000000000 : ℝ)^3847 := by
    have hnat : (4020941447 : ℕ)^4871*100000000000000^3847 ≤ 31550564888789^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020941447 10000000000 31550564888789 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2275135177/5000000000 : ℝ), (4020941603/10000000000 : ℝ), (4020941447/10000000000 : ℝ)] ![(36898868664843/100000000000000 : ℝ), (7887641609669/25000000000000 : ℝ), (31550564888789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2275135177/5000000000 : ℝ)|^4871 ≤ (36898868664843/100000000000000 : ℝ)^3847
        have hw : |(2275135177/5000000000 : ℝ)|=(2275135177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4020941603/10000000000 : ℝ)|^4871 ≤ (7887641609669/25000000000000 : ℝ)^3847
        have hw : |(4020941603/10000000000 : ℝ)|=(4020941603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020941447/10000000000 : ℝ)|^4871 ≤ (31550564888789/100000000000000 : ℝ)^3847
        have hw : |(4020941447/10000000000 : ℝ)|=(4020941447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_12 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-743197509/5000000000 : ℝ)*x 0 + (554599677/1000000000 : ℝ)*x 1 + (2597769599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (743197509/5000000000 : ℝ)^4871 ≤ (4474471492003/50000000000000 : ℝ)^3847 := by
    have hnat : (743197509 : ℕ)^4871*50000000000000^3847 ≤ 4474471492003^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743197509 5000000000 4474471492003 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554599677/1000000000 : ℝ)^4871 ≤ (4740582803991/10000000000000 : ℝ)^3847 := by
    have hnat : (554599677 : ℕ)^4871*10000000000000^3847 ≤ 4740582803991^3847*1000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554599677 1000000000 4740582803991 10000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597769599/5000000000 : ℝ)^4871 ≤ (43645228965211/100000000000000 : ℝ)^3847 := by
    have hnat : (2597769599 : ℕ)^4871*100000000000000^3847 ≤ 43645228965211^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597769599 5000000000 43645228965211 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-743197509/5000000000 : ℝ), (554599677/1000000000 : ℝ), (2597769599/5000000000 : ℝ)] ![(4474471492003/50000000000000 : ℝ), (4740582803991/10000000000000 : ℝ), (43645228965211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-743197509/5000000000 : ℝ)|^4871 ≤ (4474471492003/50000000000000 : ℝ)^3847
        have hw : |(-743197509/5000000000 : ℝ)|=(743197509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554599677/1000000000 : ℝ)|^4871 ≤ (4740582803991/10000000000000 : ℝ)^3847
        have hw : |(554599677/1000000000 : ℝ)|=(554599677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597769599/5000000000 : ℝ)|^4871 ≤ (43645228965211/100000000000000 : ℝ)^3847
        have hw : |(2597769599/5000000000 : ℝ)|=(2597769599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_13 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399371751/10000000000 : ℝ)*x 0 + (-169022697/1000000000 : ℝ)*x 1 + (2597769853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399371751/10000000000 : ℝ)^4871 ≤ (22912262163081/50000000000000 : ℝ)^3847 := by
    have hnat : (5399371751 : ℕ)^4871*50000000000000^3847 ≤ 22912262163081^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399371751 10000000000 22912262163081 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169022697/1000000000 : ℝ)^4871 ≤ (10530241290319/100000000000000 : ℝ)^3847 := by
    have hnat : (169022697 : ℕ)^4871*100000000000000^3847 ≤ 10530241290319^3847*1000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169022697 1000000000 10530241290319 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597769853/5000000000 : ℝ)^4871 ≤ (21822617184297/50000000000000 : ℝ)^3847 := by
    have hnat : (2597769853 : ℕ)^4871*50000000000000^3847 ≤ 21822617184297^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597769853 5000000000 21822617184297 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399371751/10000000000 : ℝ), (-169022697/1000000000 : ℝ), (2597769853/5000000000 : ℝ)] ![(22912262163081/50000000000000 : ℝ), (10530241290319/100000000000000 : ℝ), (21822617184297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399371751/10000000000 : ℝ)|^4871 ≤ (22912262163081/50000000000000 : ℝ)^3847
        have hw : |(5399371751/10000000000 : ℝ)|=(5399371751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169022697/1000000000 : ℝ)|^4871 ≤ (10530241290319/100000000000000 : ℝ)^3847
        have hw : |(-169022697/1000000000 : ℝ)|=(169022697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597769853/5000000000 : ℝ)|^4871 ≤ (21822617184297/50000000000000 : ℝ)^3847
        have hw : |(2597769853/5000000000 : ℝ)|=(2597769853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_14 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699686341/5000000000 : ℝ)*x 0 + (64944229/125000000 : ℝ)*x 1 + (-1690227571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699686341/5000000000 : ℝ)^4871 ≤ (45824534330777/100000000000000 : ℝ)^3847 := by
    have hnat : (2699686341 : ℕ)^4871*100000000000000^3847 ≤ 45824534330777^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699686341 5000000000 45824534330777 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64944229/125000000 : ℝ)^4871 ≤ (10911304906573/25000000000000 : ℝ)^3847 := by
    have hnat : (64944229 : ℕ)^4871*25000000000000^3847 ≤ 10911304906573^3847*125000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64944229 125000000 10911304906573 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690227571/10000000000 : ℝ)^4871 ≤ (10530246031251/100000000000000 : ℝ)^3847 := by
    have hnat : (1690227571 : ℕ)^4871*100000000000000^3847 ≤ 10530246031251^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690227571 10000000000 10530246031251 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699686341/5000000000 : ℝ), (64944229/125000000 : ℝ), (-1690227571/10000000000 : ℝ)] ![(45824534330777/100000000000000 : ℝ), (10911304906573/25000000000000 : ℝ), (10530246031251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699686341/5000000000 : ℝ)|^4871 ≤ (45824534330777/100000000000000 : ℝ)^3847
        have hw : |(2699686341/5000000000 : ℝ)|=(2699686341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64944229/125000000 : ℝ)|^4871 ≤ (10911304906573/25000000000000 : ℝ)^3847
        have hw : |(64944229/125000000 : ℝ)|=(64944229/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1690227571/10000000000 : ℝ)|^4871 ≤ (10530246031251/100000000000000 : ℝ)^3847
        have hw : |(-1690227571/10000000000 : ℝ)|=(1690227571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_box_15 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3847509517/10000000000 : ℝ)*x 0 + (4372312091/10000000000 : ℝ)*x 1 + (2186156127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3847509517/10000000000 : ℝ)^4871 ≤ (932421459863/3125000000000 : ℝ)^3847 := by
    have hnat : (3847509517 : ℕ)^4871*3125000000000^3847 ≤ 932421459863^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3847509517 10000000000 932421459863 3125000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4372312091/10000000000 : ℝ)^4871 ≤ (1096289243819/3125000000000 : ℝ)^3847 := by
    have hnat : (4372312091 : ℕ)^4871*3125000000000^3847 ≤ 1096289243819^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372312091 10000000000 1096289243819 3125000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186156127/5000000000 : ℝ)^4871 ≤ (35081257458159/100000000000000 : ℝ)^3847 := by
    have hnat : (2186156127 : ℕ)^4871*100000000000000^3847 ≤ 35081257458159^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186156127 5000000000 35081257458159 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3847509517/10000000000 : ℝ), (4372312091/10000000000 : ℝ), (2186156127/5000000000 : ℝ)] ![(932421459863/3125000000000 : ℝ), (1096289243819/3125000000000 : ℝ), (35081257458159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3847509517/10000000000 : ℝ)|^4871 ≤ (932421459863/3125000000000 : ℝ)^3847
        have hw : |(3847509517/10000000000 : ℝ)|=(3847509517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4372312091/10000000000 : ℝ)|^4871 ≤ (1096289243819/3125000000000 : ℝ)^3847
        have hw : |(4372312091/10000000000 : ℝ)|=(4372312091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2186156127/5000000000 : ℝ)|^4871 ≤ (35081257458159/100000000000000 : ℝ)^3847
        have hw : |(2186156127/5000000000 : ℝ)|=(2186156127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1638_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5303/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65019/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1828/3125 : ℝ) ∧ (3239/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44053/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5303/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5303/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5303/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5303/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5303/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5303/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5303/50000 : ℝ) ^ (4867/1024 : ℝ) ≤ (2336228829948749/100000000000000000000 : ℝ) := by
    have hpowers : (5303/50000 : ℝ)^4867 ≤ (2336228829948749/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5303 : ℕ)^4867*100000000000000000000^1024 ≤ 2336228829948749^1024*50000^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5303 50000 2336228829948749 100000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5303/50000 : ℝ)) (X := (2336228829948749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16291/100000 : ℝ) ^ (4867/1024 : ℝ) ≤ (17965654176708031/100000000000000000000 : ℝ) := by
    have hpowers : (16291/100000 : ℝ)^4867 ≤ (17965654176708031/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16291 : ℕ)^4867*100000000000000000000^1024 ≤ 17965654176708031^1024*100000^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16291 100000 17965654176708031 100000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16291/100000 : ℝ)) (X := (17965654176708031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002336228829948749/50000000000000000000 : ℝ) ≤ (5000049152541453/5000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (50002336228829948749/50000000000000000000 : ℝ)^1024 ≤ (5000049152541453/5000000000000000 : ℝ)^4867 := by
      have hnat : (50002336228829948749 : ℕ)^1024*5000000000000000^4867 ≤ 5000049152541453^4867*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002336228829948749 50000000000000000000 5000049152541453 5000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000049152541453/5000000000000000 : ℝ)) (X := (50002336228829948749/50000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001015094150332839/5000000000000000000 : ℝ) ≤ (10000427110378191/10000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (5001015094150332839/5000000000000000000 : ℝ)^1024 ≤ (10000427110378191/10000000000000000 : ℝ)^4867 := by
      have hnat : (5001015094150332839 : ℕ)^1024*10000000000000000^4867 ≤ 10000427110378191^4867*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001015094150332839 5000000000000000000 10000427110378191 10000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000427110378191/10000000000000000 : ℝ)) (X := (5001015094150332839/5000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017965654176708031/50000000000000000000 : ℝ) ≤ (2500188978918369/2500000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (50017965654176708031/50000000000000000000 : ℝ)^1024 ≤ (2500188978918369/2500000000000000 : ℝ)^4867 := by
      have hnat : (50017965654176708031 : ℕ)^1024*2500000000000000^4867 ≤ 2500188978918369^4867*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017965654176708031 50000000000000000000 2500188978918369 2500000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500188978918369/2500000000000000 : ℝ)) (X := (50017965654176708031/50000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2336228829948749/100000000000000000000 : ℝ) ≤ ((1894786141549091173/1895000000000000000 : ℝ)+2*(21920353019/37900000000000 : ℝ)*(5303/50000 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (1894786141549091173/1895000000000000000 : ℝ)+2*(21920353019/37900000000000 : ℝ)*(5303/50000 : ℝ)=(5000049152541453/5000000000000000 : ℝ) by norm_num, show 1+2*(2336228829948749/100000000000000000000 : ℝ)=(50002336228829948749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17965654176708031/100000000000000000000 : ℝ)+(2336228829948749/100000000000000000000 : ℝ) ≤ ((1894786141549091173/1895000000000000000 : ℝ)+(21920353019/37900000000000 : ℝ)*((16291/100000 : ℝ)+(5303/50000 : ℝ)))^(4867/1024 : ℝ) := by
    rw [show (1894786141549091173/1895000000000000000 : ℝ)+(21920353019/37900000000000 : ℝ)*((16291/100000 : ℝ)+(5303/50000 : ℝ))=(10000427110378191/10000000000000000 : ℝ) by norm_num, show 1+(17965654176708031/100000000000000000000 : ℝ)+(2336228829948749/100000000000000000000 : ℝ)=(5001015094150332839/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17965654176708031/100000000000000000000 : ℝ) ≤ ((1894786141549091173/1895000000000000000 : ℝ)+2*(21920353019/37900000000000 : ℝ)*(16291/100000 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (1894786141549091173/1895000000000000000 : ℝ)+2*(21920353019/37900000000000 : ℝ)*(16291/100000 : ℝ)=(2500188978918369/2500000000000000 : ℝ) by norm_num, show 1+2*(17965654176708031/100000000000000000000 : ℝ)=(50017965654176708031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1894786141549091173/1895000000000000000 : ℝ)*(X 1 0+X 2 0)+(21920353019/37900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (5303/50000 : ℝ)) (hi := (16291/100000 : ℝ)) (c := (1894786141549091173/1895000000000000000 : ℝ)) (alpha := (21920353019/37900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1894786141549091173/1895000000000000000 : ℝ)*(X 0 1+X 2 1)+(21920353019/37900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (5303/50000 : ℝ)) (hi := (16291/100000 : ℝ)) (c := (1894786141549091173/1895000000000000000 : ℝ)) (alpha := (21920353019/37900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1894786141549091173/1895000000000000000 : ℝ)*(X 0 2+X 1 2)+(21920353019/37900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (5303/50000 : ℝ)) (hi := (16291/100000 : ℝ)) (c := (1894786141549091173/1895000000000000000 : ℝ)) (alpha := (21920353019/37900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-686953937/5000000000 : ℝ)*X 0 0+(2705516797/5000000000 : ℝ)*X 0 1+(2705516797/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1312803077/2500000000 : ℝ)*X 1 0+(-1598489797/10000000000 : ℝ)*X 1 1+(5411033389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251212339/10000000000 : ℝ)*X 2 0+(5411033323/10000000000 : ℝ)*X 2 1+(-1598489847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4467680863/10000000000 : ℝ)*X 0 0+(2031727483/5000000000 : ℝ)*X 0 1+(4063455119/10000000000 : ℝ)*X 0 2+(4467680863/10000000000 : ℝ)*X 1 0+(2031727483/5000000000 : ℝ)*X 1 1+(4063455119/10000000000 : ℝ)*X 1 2+(4467680863/10000000000 : ℝ)*X 2 0+(2031727483/5000000000 : ℝ)*X 2 1+(4063455119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1909288701/10000000000 : ℝ)*X 0 0+(1303845527/2500000000 : ℝ)*X 0 1+(2607691289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692860589/5000000000 : ℝ)*X 1 0+(-336408339/2000000000 : ℝ)*X 1 1+(5215382629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2692860721/5000000000 : ℝ)*X 2 0+(5215382029/10000000000 : ℝ)*X 2 1+(-1682042147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((78121859/200000000 : ℝ)*X 0 0+(542989887/1250000000 : ℝ)*X 0 1+(2171959353/5000000000 : ℝ)*X 0 2+(78121859/200000000 : ℝ)*X 1 0+(542989887/1250000000 : ℝ)*X 1 1+(2171959353/5000000000 : ℝ)*X 1 2+(78121859/200000000 : ℝ)*X 2 0+(542989887/1250000000 : ℝ)*X 2 1+(2171959353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-448796987/2500000000 : ℝ)*X 0 0+(5074955933/10000000000 : ℝ)*X 0 1+(5440637707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615429533/5000000000 : ℝ)*X 1 0+(-1585409061/10000000000 : ℝ)*X 1 1+(1360159443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((326928683/625000000 : ℝ)*X 2 0+(5440637891/10000000000 : ℝ)*X 2 1+(-317081817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2275135177/5000000000 : ℝ)*X 0 0+(4020941603/10000000000 : ℝ)*X 0 1+(4020941447/10000000000 : ℝ)*X 0 2+(2275135177/5000000000 : ℝ)*X 1 0+(4020941603/10000000000 : ℝ)*X 1 1+(4020941447/10000000000 : ℝ)*X 1 2+(2275135177/5000000000 : ℝ)*X 2 0+(4020941603/10000000000 : ℝ)*X 2 1+(4020941447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-743197509/5000000000 : ℝ)*X 0 0+(554599677/1000000000 : ℝ)*X 0 1+(2597769599/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5399371751/10000000000 : ℝ)*X 1 0+(-169022697/1000000000 : ℝ)*X 1 1+(2597769853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2699686341/5000000000 : ℝ)*X 2 0+(64944229/125000000 : ℝ)*X 2 1+(-1690227571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3847509517/10000000000 : ℝ)*X 0 0+(4372312091/10000000000 : ℝ)*X 0 1+(2186156127/5000000000 : ℝ)*X 0 2+(3847509517/10000000000 : ℝ)*X 1 0+(4372312091/10000000000 : ℝ)*X 1 1+(2186156127/5000000000 : ℝ)*X 1 2+(3847509517/10000000000 : ℝ)*X 2 0+(4372312091/10000000000 : ℝ)*X 2 1+(2186156127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65019/100000 : ℝ) ≤ (-616031683320587602552414249179/947500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15695941/25000000000000 : ℝ)*(lower0) + (8098779/100000000000000 : ℝ)*(upper1) + (16140707/25000000000000 : ℝ)*(lower4) + (34720591057859/2000000000000 : ℝ)*(major0) + (34720591057859/2000000000000 : ℝ)*(major1) + (34720591057859/2000000000000 : ℝ)*(major2) + (8414529741/100000000000000 : ℝ)*(sp2) + (425333167/100000000000000 : ℝ)*(sp3) + (1257591055304413/50000000000000 : ℝ)*(sp4) + (2515171564615219/100000000000000 : ℝ)*(sp5) + (1257588087815793/50000000000000 : ℝ)*(sp6) + (489273134562069/50000000000000 : ℝ)*(sp7) + (1239776251/50000000000000 : ℝ)*(sp12) + (13025546109/100000000000000 : ℝ)*(sp13) + (195709338891461/20000000000000 : ℝ)*(f.failure) + (157199036885083/6250000000000 : ℝ)*(f.sum) + (1324873997051/379000000000000000000000000 : ℝ)*base66 + (21531251779991393/3790000000000000000000000000000 : ℝ)*base68 + (13887063608521393/3790000000000000000000000000000 : ℝ)*base70 + (49861822959751393/3790000000000000000000000000000 : ℝ)*base72 + (391704820509/75800000000000000000000000 : ℝ)*base73 + (6881354277511393/3790000000000000000000000000000 : ℝ)*base76 + (14851191502051393/3790000000000000000000000000000 : ℝ)*base78 + (8674958817698607/3790000000000000000000000000000 : ℝ)*base79 + (395178018209/189500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1114101/500000000000000000000 : ℝ)*base89 + (1114101/500000000000000000000 : ℝ)*base91 + (1114101/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1828/3125 : ℝ) ≤ (6928460525554282464307889735979/11843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22749947/100000000000000 : ℝ)*(lower1) + (21930523/100000000000000 : ℝ)*(lower3) + (7353639/20000000000000 : ℝ)*(lower5) + (228092892458947/12500000000000 : ℝ)*(major0) + (228092892458947/12500000000000 : ℝ)*(major1) + (228092892458947/12500000000000 : ℝ)*(major2) + (650358477608793/25000000000000 : ℝ)*(sp0) + (650355803550469/25000000000000 : ℝ)*(sp1) + (1300709626044351/50000000000000 : ℝ)*(sp2) + (1028548699119767/100000000000000 : ℝ)*(sp3) + (3127422423/100000000000000 : ℝ)*(sp7) + (2903387287/25000000000000 : ℝ)*(sp9) + (7787831161/50000000000000 : ℝ)*(sp10) + (229328963/25000000000000 : ℝ)*(sp12) + (102855182654219/10000000000000 : ℝ)*(f.failure) + (162589676734439/6250000000000 : ℝ)*(f.sum) + (989565420179/1895000000000000000000000000 : ℝ)*base65 + (129575985869150169/23687500000000000000000000000000 : ℝ)*base68 + (128267204995587669/23687500000000000000000000000000 : ℝ)*base70 + (163487806982337669/23687500000000000000000000000000 : ℝ)*base72 + (2882154663797/947500000000000000000000000 : ℝ)*base73 + (193306474878337669/23687500000000000000000000000000 : ℝ)*base76 + (142442392208712669/23687500000000000000000000000000 : ℝ)*base78 + (254056011729150169/23687500000000000000000000000000 : ℝ)*base80 + (3335933878379/1895000000000000000000000000 : ℝ)*base81 + (754779/250000000000000000000 : ℝ)*base89 + (754779/250000000000000000000 : ℝ)*base91 + (754779/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (3239/4000 : ℝ) ≤ (383631367042368526005601011/473750000000000000000000000 : ℝ) := by norm_num
    linear_combination (162859/10000000000000 : ℝ)*(upper1) + (4790167/50000000000000 : ℝ)*(upper2) + (939179/5000000000000 : ℝ)*(upper3) + (846151/4000000000000 : ℝ)*(lower5) + (1922684522745019/100000000000000 : ℝ)*(major0) + (1922684522745019/100000000000000 : ℝ)*(major1) + (1922684522745019/100000000000000 : ℝ)*(major2) + (168073267/20000000000000 : ℝ)*(sp0) + (1049796251/100000000000000 : ℝ)*(sp1) + (14884027139/100000000000000 : ℝ)*(sp2) + (1367308643948723/50000000000000 : ℝ)*(sp8) + (273461707846753/10000000000000 : ℝ)*(sp9) + (2734603244236641/100000000000000 : ℝ)*(sp10) + (8670067078437/800000000000 : ℝ)*(sp11) + (8670067078437/800000000000 : ℝ)*(f.failure) + (136730906413189/5000000000000 : ℝ)*(f.sum) + (5311430053179/1895000000000000000000000000 : ℝ)*base66 + (117732317497832713/189500000000000000000000000000000 : ℝ)*base68 + (864592532594167287/189500000000000000000000000000000 : ℝ)*base69 + (129927126670332713/189500000000000000000000000000000 : ℝ)*base72 + (5844472416349/1895000000000000000000000000 : ℝ)*base74 + (650140373192332713/189500000000000000000000000000000 : ℝ)*base76 + (321714916280167287/189500000000000000000000000000000 : ℝ)*base77 + (1145169223662167287/189500000000000000000000000000000 : ℝ)*base79 + (2433210290077/947500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (72683/20000000000000000000 : ℝ)*base90 + (72683/20000000000000000000 : ℝ)*base92 + (72683/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-44053/50000 : ℝ) ≤ (-41739011332652978694821296210179/47375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49104619/100000000000000 : ℝ)*(upper3) + (18290457/100000000000000 : ℝ)*(lower4) + (65933359/100000000000000 : ℝ)*(upper5) + (983077956982953/50000000000000 : ℝ)*(major0) + (983077956982953/50000000000000 : ℝ)*(major1) + (983077956982953/50000000000000 : ℝ)*(major2) + (5304355701/100000000000000 : ℝ)*(sp0) + (93014969/1000000000000 : ℝ)*(sp5) + (217299474211/100000000000000 : ℝ)*(sp6) + (3718045233/25000000000000 : ℝ)*(sp7) + (71335311620419/2500000000000 : ℝ)*(sp12) + (2853408467675561/100000000000000 : ℝ)*(sp13) + (11412801878793/400000000000 : ℝ)*(sp14) + (1108247004578523/100000000000000 : ℝ)*(sp15) + (221652375351891/20000000000000 : ℝ)*(f.failure) + (2853417769172461/100000000000000 : ℝ)*(f.sum) + (3742106852901/1895000000000000000000000000 : ℝ)*base66 + (553617336231126131/94750000000000000000000000000000 : ℝ)*base68 + (820947738623876131/94750000000000000000000000000000 : ℝ)*base70 + (172217758655376131/94750000000000000000000000000000 : ℝ)*base72 + (1848082586689/1895000000000000000000000000 : ℝ)*base73 + (399774257040876131/94750000000000000000000000000000 : ℝ)*base76 + (287254989187626131/94750000000000000000000000000000 : ℝ)*base78 + (143540238724876131/94750000000000000000000000000000 : ℝ)*base80 + (5123697591751/1895000000000000000000000000 : ℝ)*base82 + (562269/500000000000000000000 : ℝ)*base90 + (562269/500000000000000000000 : ℝ)*base92 + (562269/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1638_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5303/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65019/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1828/3125 : ℝ) else (3239/4000 : ℝ) ≤ X j i ∧ X j i ≤ (44053/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1638_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1638_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5303/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65019/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1828/3125 : ℝ) else (3239/4000 : ℝ) ≤ X j i ∧ X j i ≤ (44053/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1638_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5303/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65019/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1828/3125 : ℝ) else (3239/4000 : ℝ) ≤ X j i ∧ X j i ≤ (44053/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1638_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

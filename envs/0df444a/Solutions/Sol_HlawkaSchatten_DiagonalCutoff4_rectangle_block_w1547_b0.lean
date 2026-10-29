-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1547_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:21.952988+00:00
-- url     : https://prove2.me/submissions/28a8966b-13e9-4891-89ec-b852fbf346c4

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
theorem support_rectangle_w1547_s0_0 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1649333811/10000000000 : ℝ)*x 0 + (5886384517/10000000000 : ℝ)*x 1 + (4870005417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649333811/10000000000 : ℝ)^4591 ≤ (4915714587697/50000000000000 : ℝ)^3567 := by
    have hnat : (1649333811 : ℕ)^4591*50000000000000^3567 ≤ 4915714587697^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649333811 10000000000 4915714587697 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5886384517/10000000000 : ℝ)^4591 ≤ (12639145329357/25000000000000 : ℝ)^3567 := by
    have hnat : (5886384517 : ℕ)^4591*25000000000000^3567 ≤ 12639145329357^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5886384517 10000000000 12639145329357 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4870005417/10000000000 : ℝ)^4591 ≤ (1237874671413/3125000000000 : ℝ)^3567 := by
    have hnat : (4870005417 : ℕ)^4591*3125000000000^3567 ≤ 1237874671413^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870005417 10000000000 1237874671413 3125000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1649333811/10000000000 : ℝ), (5886384517/10000000000 : ℝ), (4870005417/10000000000 : ℝ)] ![(4915714587697/50000000000000 : ℝ), (12639145329357/25000000000000 : ℝ), (1237874671413/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1649333811/10000000000 : ℝ)|^4591 ≤ (4915714587697/50000000000000 : ℝ)^3567
        have hw : |(-1649333811/10000000000 : ℝ)|=(1649333811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5886384517/10000000000 : ℝ)|^4591 ≤ (12639145329357/25000000000000 : ℝ)^3567
        have hw : |(5886384517/10000000000 : ℝ)|=(5886384517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4870005417/10000000000 : ℝ)|^4591 ≤ (1237874671413/3125000000000 : ℝ)^3567
        have hw : |(4870005417/10000000000 : ℝ)|=(4870005417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_1 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5470405907/10000000000 : ℝ)*x 0 + (-2216520603/10000000000 : ℝ)*x 1 + (9740011/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5470405907/10000000000 : ℝ)^4591 ≤ (46005659437991/100000000000000 : ℝ)^3567 := by
    have hnat : (5470405907 : ℕ)^4591*100000000000000^3567 ≤ 46005659437991^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470405907 10000000000 46005659437991 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216520603/10000000000 : ℝ)^4591 ≤ (7191175097363/50000000000000 : ℝ)^3567 := by
    have hnat : (2216520603 : ℕ)^4591*50000000000000^3567 ≤ 7191175097363^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216520603 10000000000 7191175097363 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9740011/20000000 : ℝ)^4591 ≤ (4951498794267/12500000000000 : ℝ)^3567 := by
    have hnat : (9740011 : ℕ)^4591*12500000000000^3567 ≤ 4951498794267^3567*20000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9740011 20000000 4951498794267 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5470405907/10000000000 : ℝ), (-2216520603/10000000000 : ℝ), (9740011/20000000 : ℝ)] ![(46005659437991/100000000000000 : ℝ), (7191175097363/50000000000000 : ℝ), (4951498794267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5470405907/10000000000 : ℝ)|^4591 ≤ (46005659437991/100000000000000 : ℝ)^3567
        have hw : |(5470405907/10000000000 : ℝ)|=(5470405907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216520603/10000000000 : ℝ)|^4591 ≤ (7191175097363/50000000000000 : ℝ)^3567
        have hw : |(-2216520603/10000000000 : ℝ)|=(2216520603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9740011/20000000 : ℝ)|^4591 ≤ (4951498794267/12500000000000 : ℝ)^3567
        have hw : |(9740011/20000000 : ℝ)|=(9740011/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_2 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273520291/500000000 : ℝ)*x 0 + (2435002727/5000000000 : ℝ)*x 1 + (-2216520773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273520291/500000000 : ℝ)^4591 ≤ (9201131699257/20000000000000 : ℝ)^3567 := by
    have hnat : (273520291 : ℕ)^4591*20000000000000^3567 ≤ 9201131699257^3567*500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273520291 500000000 9201131699257 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435002727/5000000000 : ℝ)^4591 ≤ (19805994936283/50000000000000 : ℝ)^3567 := by
    have hnat : (2435002727 : ℕ)^4591*50000000000000^3567 ≤ 19805994936283^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435002727 5000000000 19805994936283 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216520773/10000000000 : ℝ)^4591 ≤ (7191175807237/50000000000000 : ℝ)^3567 := by
    have hnat : (2216520773 : ℕ)^4591*50000000000000^3567 ≤ 7191175807237^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216520773 10000000000 7191175807237 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273520291/500000000 : ℝ), (2435002727/5000000000 : ℝ), (-2216520773/10000000000 : ℝ)] ![(9201131699257/20000000000000 : ℝ), (19805994936283/50000000000000 : ℝ), (7191175807237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273520291/500000000 : ℝ)|^4591 ≤ (9201131699257/20000000000000 : ℝ)^3567
        have hw : |(273520291/500000000 : ℝ)|=(273520291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2435002727/5000000000 : ℝ)|^4591 ≤ (19805994936283/50000000000000 : ℝ)^3567
        have hw : |(2435002727/5000000000 : ℝ)|=(2435002727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216520773/10000000000 : ℝ)|^4591 ≤ (7191175807237/50000000000000 : ℝ)^3567
        have hw : |(-2216520773/10000000000 : ℝ)|=(2216520773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_3 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (413583509/1000000000 : ℝ)*x 0 + (1546041293/5000000000 : ℝ)*x 1 + (340860133/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413583509/1000000000 : ℝ)^4591 ≤ (3209872075507/10000000000000 : ℝ)^3567 := by
    have hnat : (413583509 : ℕ)^4591*10000000000000^3567 ≤ 3209872075507^3567*1000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413583509 1000000000 3209872075507 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546041293/5000000000 : ℝ)^4591 ≤ (5518924173579/25000000000000 : ℝ)^3567 := by
    have hnat : (1546041293 : ℕ)^4591*25000000000000^3567 ≤ 5518924173579^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546041293 5000000000 5518924173579 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340860133/625000000 : ℝ)^4591 ≤ (22912791272361/50000000000000 : ℝ)^3567 := by
    have hnat : (340860133 : ℕ)^4591*50000000000000^3567 ≤ 22912791272361^3567*625000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340860133 625000000 22912791272361 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(413583509/1000000000 : ℝ), (1546041293/5000000000 : ℝ), (340860133/625000000 : ℝ)] ![(3209872075507/10000000000000 : ℝ), (5518924173579/25000000000000 : ℝ), (22912791272361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(413583509/1000000000 : ℝ)|^4591 ≤ (3209872075507/10000000000000 : ℝ)^3567
        have hw : |(413583509/1000000000 : ℝ)|=(413583509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1546041293/5000000000 : ℝ)|^4591 ≤ (5518924173579/25000000000000 : ℝ)^3567
        have hw : |(1546041293/5000000000 : ℝ)|=(1546041293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340860133/625000000 : ℝ)|^4591 ≤ (22912791272361/50000000000000 : ℝ)^3567
        have hw : |(340860133/625000000 : ℝ)|=(340860133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_4 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-826283587/5000000000 : ℝ)*x 0 + (195829933/400000000 : ℝ)*x 1 + (2929862227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826283587/5000000000 : ℝ)^4591 ≤ (9856242723791/100000000000000 : ℝ)^3567 := by
    have hnat : (826283587 : ℕ)^4591*100000000000000^3567 ≤ 9856242723791^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826283587 5000000000 9856242723791 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195829933/400000000 : ℝ)^4591 ≤ (39881693852733/100000000000000 : ℝ)^3567 := by
    have hnat : (195829933 : ℕ)^4591*100000000000000^3567 ≤ 39881693852733^3567*400000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195829933 400000000 39881693852733 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2929862227/5000000000 : ℝ)^4591 ≤ (50262063417761/100000000000000 : ℝ)^3567 := by
    have hnat : (2929862227 : ℕ)^4591*100000000000000^3567 ≤ 50262063417761^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929862227 5000000000 50262063417761 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-826283587/5000000000 : ℝ), (195829933/400000000 : ℝ), (2929862227/5000000000 : ℝ)] ![(9856242723791/100000000000000 : ℝ), (39881693852733/100000000000000 : ℝ), (50262063417761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-826283587/5000000000 : ℝ)|^4591 ≤ (9856242723791/100000000000000 : ℝ)^3567
        have hw : |(-826283587/5000000000 : ℝ)|=(826283587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195829933/400000000 : ℝ)|^4591 ≤ (39881693852733/100000000000000 : ℝ)^3567
        have hw : |(195829933/400000000 : ℝ)|=(195829933/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2929862227/5000000000 : ℝ)|^4591 ≤ (50262063417761/100000000000000 : ℝ)^3567
        have hw : |(2929862227/5000000000 : ℝ)|=(2929862227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_5 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596299609/5000000000 : ℝ)*x 0 + (-1226802051/10000000000 : ℝ)*x 1 + (5859724117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596299609/5000000000 : ℝ)^4591 ≤ (2688800846367/6250000000000 : ℝ)^3567 := by
    have hnat : (2596299609 : ℕ)^4591*6250000000000^3567 ≤ 2688800846367^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596299609 5000000000 2688800846367 6250000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226802051/10000000000 : ℝ)^4591 ≤ (6717126749489/100000000000000 : ℝ)^3567 := by
    have hnat : (1226802051 : ℕ)^4591*100000000000000^3567 ≤ 6717126749489^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226802051 10000000000 6717126749489 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5859724117/10000000000 : ℝ)^4591 ≤ (50262059697297/100000000000000 : ℝ)^3567 := by
    have hnat : (5859724117 : ℕ)^4591*100000000000000^3567 ≤ 50262059697297^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5859724117 10000000000 50262059697297 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596299609/5000000000 : ℝ), (-1226802051/10000000000 : ℝ), (5859724117/10000000000 : ℝ)] ![(2688800846367/6250000000000 : ℝ), (6717126749489/100000000000000 : ℝ), (50262059697297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596299609/5000000000 : ℝ)|^4591 ≤ (2688800846367/6250000000000 : ℝ)^3567
        have hw : |(2596299609/5000000000 : ℝ)|=(2596299609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1226802051/10000000000 : ℝ)|^4591 ≤ (6717126749489/100000000000000 : ℝ)^3567
        have hw : |(-1226802051/10000000000 : ℝ)|=(1226802051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5859724117/10000000000 : ℝ)|^4591 ≤ (50262059697297/100000000000000 : ℝ)^3567
        have hw : |(5859724117/10000000000 : ℝ)|=(5859724117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_6 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192598309/10000000000 : ℝ)*x 0 + (2929862751/5000000000 : ℝ)*x 1 + (-153350157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192598309/10000000000 : ℝ)^4591 ≤ (4302080384879/10000000000000 : ℝ)^3567 := by
    have hnat : (5192598309 : ℕ)^4591*10000000000000^3567 ≤ 4302080384879^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192598309 10000000000 4302080384879 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2929862751/5000000000 : ℝ)^4591 ≤ (10052414997527/20000000000000 : ℝ)^3567 := by
    have hnat : (2929862751 : ℕ)^4591*20000000000000^3567 ≤ 10052414997527^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929862751 5000000000 10052414997527 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153350157/1250000000 : ℝ)^4591 ≤ (6717121147009/100000000000000 : ℝ)^3567 := by
    have hnat : (153350157 : ℕ)^4591*100000000000000^3567 ≤ 6717121147009^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153350157 1250000000 6717121147009 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192598309/10000000000 : ℝ), (2929862751/5000000000 : ℝ), (-153350157/1250000000 : ℝ)] ![(4302080384879/10000000000000 : ℝ), (10052414997527/20000000000000 : ℝ), (6717121147009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192598309/10000000000 : ℝ)|^4591 ≤ (4302080384879/10000000000000 : ℝ)^3567
        have hw : |(5192598309/10000000000 : ℝ)|=(5192598309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2929862751/5000000000 : ℝ)|^4591 ≤ (10052414997527/20000000000000 : ℝ)^3567
        have hw : |(2929862751/5000000000 : ℝ)|=(2929862751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153350157/1250000000 : ℝ)|^4591 ≤ (6717121147009/100000000000000 : ℝ)^3567
        have hw : |(-153350157/1250000000 : ℝ)|=(153350157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s0_7 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4143345593/10000000000 : ℝ)*x 0 + (1078788791/2000000000 : ℝ)*x 1 + (3154028977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4143345593/10000000000 : ℝ)^4591 ≤ (8043440967711/25000000000000 : ℝ)^3567 := by
    have hnat : (4143345593 : ℕ)^4591*25000000000000^3567 ≤ 8043440967711^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143345593 10000000000 8043440967711 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078788791/2000000000 : ℝ)^4591 ≤ (45179685848791/100000000000000 : ℝ)^3567 := by
    have hnat : (1078788791 : ℕ)^4591*100000000000000^3567 ≤ 45179685848791^3567*2000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078788791 2000000000 45179685848791 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154028977/10000000000 : ℝ)^4591 ≤ (4529310053179/20000000000000 : ℝ)^3567 := by
    have hnat : (3154028977 : ℕ)^4591*20000000000000^3567 ≤ 4529310053179^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154028977 10000000000 4529310053179 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4143345593/10000000000 : ℝ), (1078788791/2000000000 : ℝ), (3154028977/10000000000 : ℝ)] ![(8043440967711/25000000000000 : ℝ), (45179685848791/100000000000000 : ℝ), (4529310053179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4143345593/10000000000 : ℝ)|^4591 ≤ (8043440967711/25000000000000 : ℝ)^3567
        have hw : |(4143345593/10000000000 : ℝ)|=(4143345593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078788791/2000000000 : ℝ)|^4591 ≤ (45179685848791/100000000000000 : ℝ)^3567
        have hw : |(1078788791/2000000000 : ℝ)|=(1078788791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154028977/10000000000 : ℝ)|^4591 ≤ (4529310053179/20000000000000 : ℝ)^3567
        have hw : |(3154028977/10000000000 : ℝ)|=(3154028977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1547_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3267/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25039/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4589/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4589 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4589*1^1024 ≤ 0^1024*1^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4589/1024 : ℝ) ≤ (1646848366946061683/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4589 ≤ (1646848366946061683/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4589*100000000000000000000^1024 ≤ 1646848366946061683^1024*5^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1646848366946061683 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1646848366946061683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4589 := by
      have hnat : (1 : ℕ)^1024*1^4589 ≤ 1^4589*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101646848366946061683/100000000000000000000 : ℝ) ≤ (10036515347878167/10000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (101646848366946061683/100000000000000000000 : ℝ)^1024 ≤ (10036515347878167/10000000000000000 : ℝ)^4589 := by
      have hnat : (101646848366946061683 : ℕ)^1024*10000000000000000^4589 ≤ 10036515347878167^4589*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101646848366946061683 100000000000000000000 10036515347878167 10000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10036515347878167/10000000000000000 : ℝ)) (X := (101646848366946061683/100000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51646848366946061683/50000000000000000000 : ℝ) ≤ (5036515347878167/5000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (51646848366946061683/50000000000000000000 : ℝ)^1024 ≤ (5036515347878167/5000000000000000 : ℝ)^4589 := by
      have hnat : (51646848366946061683 : ℕ)^1024*5000000000000000^4589 ≤ 5036515347878167^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51646848366946061683 50000000000000000000 5036515347878167 5000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036515347878167/5000000000000000 : ℝ)) (X := (51646848366946061683/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(36515347878167/4000000000000000 : ℝ)*(0 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36515347878167/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1646848366946061683/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(36515347878167/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4589/1024 : ℝ) := by
    rw [show (1 : ℝ)+(36515347878167/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10036515347878167/10000000000000000 : ℝ) by norm_num, show 1+(1646848366946061683/100000000000000000000 : ℝ)+(0 : ℝ)=(101646848366946061683/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1646848366946061683/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(36515347878167/4000000000000000 : ℝ)*(2/5 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36515347878167/4000000000000000 : ℝ)*(2/5 : ℝ)=(5036515347878167/5000000000000000 : ℝ) by norm_num, show 1+2*(1646848366946061683/100000000000000000000 : ℝ)=(51646848366946061683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(36515347878167/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36515347878167/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(36515347878167/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36515347878167/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(36515347878167/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36515347878167/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1649333811/10000000000 : ℝ)*X 0 0+(5886384517/10000000000 : ℝ)*X 0 1+(4870005417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5470405907/10000000000 : ℝ)*X 1 0+(-2216520603/10000000000 : ℝ)*X 1 1+(9740011/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((273520291/500000000 : ℝ)*X 2 0+(2435002727/5000000000 : ℝ)*X 2 1+(-2216520773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((413583509/1000000000 : ℝ)*X 0 0+(1546041293/5000000000 : ℝ)*X 0 1+(340860133/625000000 : ℝ)*X 0 2+(413583509/1000000000 : ℝ)*X 1 0+(1546041293/5000000000 : ℝ)*X 1 1+(340860133/625000000 : ℝ)*X 1 2+(413583509/1000000000 : ℝ)*X 2 0+(1546041293/5000000000 : ℝ)*X 2 1+(340860133/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-826283587/5000000000 : ℝ)*X 0 0+(195829933/400000000 : ℝ)*X 0 1+(2929862227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596299609/5000000000 : ℝ)*X 1 0+(-1226802051/10000000000 : ℝ)*X 1 1+(5859724117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192598309/10000000000 : ℝ)*X 2 0+(2929862751/5000000000 : ℝ)*X 2 1+(-153350157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4143345593/10000000000 : ℝ)*X 0 0+(1078788791/2000000000 : ℝ)*X 0 1+(3154028977/10000000000 : ℝ)*X 0 2+(4143345593/10000000000 : ℝ)*X 1 0+(1078788791/2000000000 : ℝ)*X 1 1+(3154028977/10000000000 : ℝ)*X 1 2+(4143345593/10000000000 : ℝ)*X 2 0+(1078788791/2000000000 : ℝ)*X 2 1+(3154028977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1328149755417015769684311/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21196839/25000000000000 : ℝ)*(base1) + (1332477853/100000000000000 : ℝ)*(base19) + (1316830263/100000000000000 : ℝ)*(base23) + (196915041/100000000000000 : ℝ)*(upper3) + (142335691/100000000000000 : ℝ)*(upper5) + (703662906904811/100000000000000 : ℝ)*(major0) + (703662906904811/100000000000000 : ℝ)*(major1) + (703662906904811/100000000000000 : ℝ)*(major2) + (983889611171961/100000000000000 : ℝ)*(sp0) + (61493298513707/6250000000000 : ℝ)*(sp1) + (491946395933451/50000000000000 : ℝ)*(sp2) + (8468586184133/2000000000000 : ℝ)*(sp3) + (57278907/1250000000000 : ℝ)*(sp4) + (2089760151/100000000000000 : ℝ)*(sp7) + (105857870938539/25000000000000 : ℝ)*(f.failure) + (196778821739433/20000000000000 : ℝ)*(f.sum) + (371964552238563/200000000000000000000000000000 : ℝ)*base66 + (1997647282638563/400000000000000000000000000000 : ℝ)*base68 + (1725001612561437/400000000000000000000000000000 : ℝ)*base69 + (64993316638563/400000000000000000000000000000 : ℝ)*base72 + (1052847499638563/200000000000000000000000000000 : ℝ)*base74 + (1263257203361437/400000000000000000000000000000 : ℝ)*base75 + (1585449220961437/400000000000000000000000000000 : ℝ)*base77 + (1149924751038563/400000000000000000000000000000 : ℝ)*base80 + (14503997961437/200000000000000000000000000000 : ℝ)*base81 + (4764271/500000000000000000000 : ℝ)*base90 + (4764271/500000000000000000000 : ℝ)*base92 + (4764271/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128051202688496543430999/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9825209/625000000000 : ℝ)*(base19) + (882855123/50000000000000 : ℝ)*(base23) + (390001779/100000000000000 : ℝ)*(base39) + (23130807/12500000000000 : ℝ)*(upper3) + (107235559/25000000000000 : ℝ)*(upper5) + (185476643789637/25000000000000 : ℝ)*(major0) + (185476643789637/25000000000000 : ℝ)*(major1) + (741906185156769/100000000000000 : ℝ)*(major2) + (2176676559/50000000000000 : ℝ)*(sp1) + (1051557623/25000000000000 : ℝ)*(sp2) + (1037367809162519/100000000000000 : ℝ)*(sp4) + (25934047094399/2500000000000 : ℝ)*(sp5) + (25934055680589/2500000000000 : ℝ)*(sp6) + (446444737734123/100000000000000 : ℝ)*(sp7) + (446444737734123/100000000000000 : ℝ)*(f.failure) + (518684099582149/50000000000000 : ℝ)*(f.sum) + (572929633216061/400000000000000000000000000000 : ℝ)*base66 + (1281708448637577/400000000000000000000000000000 : ℝ)*base68 + (147083673455379/100000000000000000000000000000 : ℝ)*base69 + (35680490637577/400000000000000000000000000000 : ℝ)*base72 + (417759120416061/400000000000000000000000000000 : ℝ)*base74 + (737640004055379/100000000000000000000000000000 : ℝ)*base75 + (12206511255379/100000000000000000000000000000 : ℝ)*base77 + (458234842144621/100000000000000000000000000000 : ℝ)*base80 + (111961828405379/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13927953/2000000000000000000000 : ℝ)*base89 + (13927953/2000000000000000000000 : ℝ)*base91 + (13927953/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1547_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1547_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1547_s1_0 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1793819243/10000000000 : ℝ)*x 0 + (69353933/125000000 : ℝ)*x 1 + (204602313/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1793819243/10000000000 : ℝ)^4591 ≤ (1369198701917/12500000000000 : ℝ)^3567 := by
    have hnat : (1793819243 : ℕ)^4591*12500000000000^3567 ≤ 1369198701917^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793819243 10000000000 1369198701917 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69353933/125000000 : ℝ)^4591 ≤ (46850677421289/100000000000000 : ℝ)^3567 := by
    have hnat : (69353933 : ℕ)^4591*100000000000000^3567 ≤ 46850677421289^3567*125000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69353933 125000000 46850677421289 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204602313/400000000 : ℝ)^4591 ≤ (42195732947291/100000000000000 : ℝ)^3567 := by
    have hnat : (204602313 : ℕ)^4591*100000000000000^3567 ≤ 42195732947291^3567*400000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204602313 400000000 42195732947291 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1793819243/10000000000 : ℝ), (69353933/125000000 : ℝ), (204602313/400000000 : ℝ)] ![(1369198701917/12500000000000 : ℝ), (46850677421289/100000000000000 : ℝ), (42195732947291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1793819243/10000000000 : ℝ)|^4591 ≤ (1369198701917/12500000000000 : ℝ)^3567
        have hw : |(-1793819243/10000000000 : ℝ)|=(1793819243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69353933/125000000 : ℝ)|^4591 ≤ (46850677421289/100000000000000 : ℝ)^3567
        have hw : |(69353933/125000000 : ℝ)|=(69353933/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204602313/400000000 : ℝ)|^4591 ≤ (42195732947291/100000000000000 : ℝ)^3567
        have hw : |(204602313/400000000 : ℝ)|=(204602313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_1 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345096651/2500000000 : ℝ)*x 0 + (-2021012749/10000000000 : ℝ)*x 1 + (5115056581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345096651/2500000000 : ℝ)^4591 ≤ (1125839572373/2500000000000 : ℝ)^3567 := by
    have hnat : (1345096651 : ℕ)^4591*2500000000000^3567 ≤ 1125839572373^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345096651 2500000000 1125839572373 2500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2021012749/10000000000 : ℝ)^4591 ≤ (6385348672001/50000000000000 : ℝ)^3567 := by
    have hnat : (2021012749 : ℕ)^4591*50000000000000^3567 ≤ 6385348672001^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021012749 10000000000 6385348672001 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5115056581/10000000000 : ℝ)^4591 ≤ (10548929934781/25000000000000 : ℝ)^3567 := by
    have hnat : (5115056581 : ℕ)^4591*25000000000000^3567 ≤ 10548929934781^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115056581 10000000000 10548929934781 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345096651/2500000000 : ℝ), (-2021012749/10000000000 : ℝ), (5115056581/10000000000 : ℝ)] ![(1125839572373/2500000000000 : ℝ), (6385348672001/50000000000000 : ℝ), (10548929934781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345096651/2500000000 : ℝ)|^4591 ≤ (1125839572373/2500000000000 : ℝ)^3567
        have hw : |(1345096651/2500000000 : ℝ)|=(1345096651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2021012749/10000000000 : ℝ)|^4591 ≤ (6385348672001/50000000000000 : ℝ)^3567
        have hw : |(-2021012749/10000000000 : ℝ)|=(2021012749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5115056581/10000000000 : ℝ)|^4591 ≤ (10548929934781/25000000000000 : ℝ)^3567
        have hw : |(5115056581/10000000000 : ℝ)|=(5115056581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_2 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21521543/40000000 : ℝ)*x 0 + (1278764299/2500000000 : ℝ)*x 1 + (-2021013079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21521543/40000000 : ℝ)^4591 ≤ (45033573694979/100000000000000 : ℝ)^3567 := by
    have hnat : (21521543 : ℕ)^4591*100000000000000^3567 ≤ 45033573694979^3567*40000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21521543 40000000 45033573694979 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278764299/2500000000 : ℝ)^4591 ≤ (8439145253777/20000000000000 : ℝ)^3567 := by
    have hnat : (1278764299 : ℕ)^4591*20000000000000^3567 ≤ 8439145253777^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278764299 2500000000 8439145253777 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021013079/10000000000 : ℝ)^4591 ≤ (6385350013943/50000000000000 : ℝ)^3567 := by
    have hnat : (2021013079 : ℕ)^4591*50000000000000^3567 ≤ 6385350013943^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021013079 10000000000 6385350013943 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21521543/40000000 : ℝ), (1278764299/2500000000 : ℝ), (-2021013079/10000000000 : ℝ)] ![(45033573694979/100000000000000 : ℝ), (8439145253777/20000000000000 : ℝ), (6385350013943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21521543/40000000 : ℝ)|^4591 ≤ (45033573694979/100000000000000 : ℝ)^3567
        have hw : |(21521543/40000000 : ℝ)|=(21521543/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1278764299/2500000000 : ℝ)|^4591 ≤ (8439145253777/20000000000000 : ℝ)^3567
        have hw : |(1278764299/2500000000 : ℝ)|=(1278764299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2021013079/10000000000 : ℝ)|^4591 ≤ (6385350013943/50000000000000 : ℝ)^3567
        have hw : |(-2021013079/10000000000 : ℝ)|=(2021013079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_3 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236839609/10000000000 : ℝ)*x 0 + (93950591/250000000 : ℝ)*x 1 + (1191187213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236839609/10000000000 : ℝ)^4591 ≤ (6622237386127/20000000000000 : ℝ)^3567 := by
    have hnat : (4236839609 : ℕ)^4591*20000000000000^3567 ≤ 6622237386127^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236839609 10000000000 6622237386127 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93950591/250000000 : ℝ)^4591 ≤ (1135012346243/4000000000000 : ℝ)^3567 := by
    have hnat : (93950591 : ℕ)^4591*4000000000000^3567 ≤ 1135012346243^3567*250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93950591 250000000 1135012346243 4000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1191187213/2500000000 : ℝ)^4591 ≤ (38513504397237/100000000000000 : ℝ)^3567 := by
    have hnat : (1191187213 : ℕ)^4591*100000000000000^3567 ≤ 38513504397237^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191187213 2500000000 38513504397237 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236839609/10000000000 : ℝ), (93950591/250000000 : ℝ), (1191187213/2500000000 : ℝ)] ![(6622237386127/20000000000000 : ℝ), (1135012346243/4000000000000 : ℝ), (38513504397237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236839609/10000000000 : ℝ)|^4591 ≤ (6622237386127/20000000000000 : ℝ)^3567
        have hw : |(4236839609/10000000000 : ℝ)|=(4236839609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93950591/250000000 : ℝ)|^4591 ≤ (1135012346243/4000000000000 : ℝ)^3567
        have hw : |(93950591/250000000 : ℝ)|=(93950591/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1191187213/2500000000 : ℝ)|^4591 ≤ (38513504397237/100000000000000 : ℝ)^3567
        have hw : |(1191187213/2500000000 : ℝ)|=(1191187213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_4 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1794063249/10000000000 : ℝ)*x 0 + (5119670297/10000000000 : ℝ)*x 1 + (43309617/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1794063249/10000000000 : ℝ)^4591 ≤ (10955507360761/100000000000000 : ℝ)^3567 := by
    have hnat : (1794063249 : ℕ)^4591*100000000000000^3567 ≤ 10955507360761^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794063249 10000000000 10955507360761 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5119670297/10000000000 : ℝ)^4591 ≤ (21122356097513/50000000000000 : ℝ)^3567 := by
    have hnat : (5119670297 : ℕ)^4591*50000000000000^3567 ≤ 21122356097513^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119670297 10000000000 21122356097513 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43309617/78125000 : ℝ)^4591 ≤ (1462493138579/3125000000000 : ℝ)^3567 := by
    have hnat : (43309617 : ℕ)^4591*3125000000000^3567 ≤ 1462493138579^3567*78125000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43309617 78125000 1462493138579 3125000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1794063249/10000000000 : ℝ), (5119670297/10000000000 : ℝ), (43309617/78125000 : ℝ)] ![(10955507360761/100000000000000 : ℝ), (21122356097513/50000000000000 : ℝ), (1462493138579/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1794063249/10000000000 : ℝ)|^4591 ≤ (10955507360761/100000000000000 : ℝ)^3567
        have hw : |(-1794063249/10000000000 : ℝ)|=(1794063249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5119670297/10000000000 : ℝ)|^4591 ≤ (21122356097513/50000000000000 : ℝ)^3567
        have hw : |(5119670297/10000000000 : ℝ)|=(5119670297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43309617/78125000 : ℝ)|^4591 ≤ (1462493138579/3125000000000 : ℝ)^3567
        have hw : |(43309617/78125000 : ℝ)|=(43309617/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_5 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265813333/10000000000 : ℝ)*x 0 + (-1592440309/10000000000 : ℝ)*x 1 + (5543630791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265813333/10000000000 : ℝ)^4591 ≤ (43803103850293/100000000000000 : ℝ)^3567 := by
    have hnat : (5265813333 : ℕ)^4591*100000000000000^3567 ≤ 43803103850293^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265813333 10000000000 43803103850293 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1592440309/10000000000 : ℝ)^4591 ≤ (9397117714891/100000000000000 : ℝ)^3567 := by
    have hnat : (1592440309 : ℕ)^4591*100000000000000^3567 ≤ 9397117714891^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592440309 10000000000 9397117714891 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5543630791/10000000000 : ℝ)^4591 ≤ (5849972303049/12500000000000 : ℝ)^3567 := by
    have hnat : (5543630791 : ℕ)^4591*12500000000000^3567 ≤ 5849972303049^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543630791 10000000000 5849972303049 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265813333/10000000000 : ℝ), (-1592440309/10000000000 : ℝ), (5543630791/10000000000 : ℝ)] ![(43803103850293/100000000000000 : ℝ), (9397117714891/100000000000000 : ℝ), (5849972303049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265813333/10000000000 : ℝ)|^4591 ≤ (43803103850293/100000000000000 : ℝ)^3567
        have hw : |(5265813333/10000000000 : ℝ)|=(5265813333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1592440309/10000000000 : ℝ)|^4591 ≤ (9397117714891/100000000000000 : ℝ)^3567
        have hw : |(-1592440309/10000000000 : ℝ)|=(1592440309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5543630791/10000000000 : ℝ)|^4591 ≤ (5849972303049/12500000000000 : ℝ)^3567
        have hw : |(5543630791/10000000000 : ℝ)|=(5543630791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_6 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265814551/10000000000 : ℝ)*x 0 + (692953821/1250000000 : ℝ)*x 1 + (-1592438909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265814551/10000000000 : ℝ)^4591 ≤ (43803116890693/100000000000000 : ℝ)^3567 := by
    have hnat : (5265814551 : ℕ)^4591*100000000000000^3567 ≤ 43803116890693^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265814551 10000000000 43803116890693 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692953821/1250000000 : ℝ)^4591 ≤ (46799776001363/100000000000000 : ℝ)^3567 := by
    have hnat : (692953821 : ℕ)^4591*100000000000000^3567 ≤ 46799776001363^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692953821 1250000000 46799776001363 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592438909/10000000000 : ℝ)^4591 ≤ (9397107081699/100000000000000 : ℝ)^3567 := by
    have hnat : (1592438909 : ℕ)^4591*100000000000000^3567 ≤ 9397107081699^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592438909 10000000000 9397107081699 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265814551/10000000000 : ℝ), (692953821/1250000000 : ℝ), (-1592438909/10000000000 : ℝ)] ![(43803116890693/100000000000000 : ℝ), (46799776001363/100000000000000 : ℝ), (9397107081699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265814551/10000000000 : ℝ)|^4591 ≤ (43803116890693/100000000000000 : ℝ)^3567
        have hw : |(5265814551/10000000000 : ℝ)|=(5265814551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692953821/1250000000 : ℝ)|^4591 ≤ (46799776001363/100000000000000 : ℝ)^3567
        have hw : |(692953821/1250000000 : ℝ)|=(692953821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1592438909/10000000000 : ℝ)|^4591 ≤ (9397107081699/100000000000000 : ℝ)^3567
        have hw : |(-1592438909/10000000000 : ℝ)|=(1592438909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s1_7 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118702229/5000000000 : ℝ)*x 0 + (594253619/1250000000 : ℝ)*x 1 + (3768906559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118702229/5000000000 : ℝ)^4591 ≤ (33116868621279/100000000000000 : ℝ)^3567 := by
    have hnat : (2118702229 : ℕ)^4591*100000000000000^3567 ≤ 33116868621279^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118702229 5000000000 33116868621279 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594253619/1250000000 : ℝ)^4591 ≤ (19201008266797/50000000000000 : ℝ)^3567 := by
    have hnat : (594253619 : ℕ)^4591*50000000000000^3567 ≤ 19201008266797^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594253619 1250000000 19201008266797 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3768906559/10000000000 : ℝ)^4591 ≤ (28481114834893/100000000000000 : ℝ)^3567 := by
    have hnat : (3768906559 : ℕ)^4591*100000000000000^3567 ≤ 28481114834893^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3768906559 10000000000 28481114834893 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118702229/5000000000 : ℝ), (594253619/1250000000 : ℝ), (3768906559/10000000000 : ℝ)] ![(33116868621279/100000000000000 : ℝ), (19201008266797/50000000000000 : ℝ), (28481114834893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118702229/5000000000 : ℝ)|^4591 ≤ (33116868621279/100000000000000 : ℝ)^3567
        have hw : |(2118702229/5000000000 : ℝ)|=(2118702229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(594253619/1250000000 : ℝ)|^4591 ≤ (19201008266797/50000000000000 : ℝ)^3567
        have hw : |(594253619/1250000000 : ℝ)|=(594253619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3768906559/10000000000 : ℝ)|^4591 ≤ (28481114834893/100000000000000 : ℝ)^3567
        have hw : |(3768906559/10000000000 : ℝ)|=(3768906559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1547_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4401/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4493/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3267/100000 : ℝ) ^ (4589/1024 : ℝ) ≤ (21940201084723/100000000000000000000 : ℝ) := by
    have hpowers : (3267/100000 : ℝ)^4589 ≤ (21940201084723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3267 : ℕ)^4589*100000000000000000000^1024 ≤ 21940201084723^1024*100000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3267 100000 21940201084723 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3267/100000 : ℝ)) (X := (21940201084723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25039/100000 : ℝ) ^ (4589/1024 : ℝ) ≤ (100903188287982647/50000000000000000000 : ℝ) := by
    have hpowers : (25039/100000 : ℝ)^4589 ≤ (100903188287982647/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25039 : ℕ)^4589*50000000000000000000^1024 ≤ 100903188287982647^1024*100000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039 100000 100903188287982647 50000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25039/100000 : ℝ)) (X := (100903188287982647/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000021940201084723/50000000000000000000 : ℝ) ≤ (5000000489578603/5000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50000021940201084723/50000000000000000000 : ℝ)^1024 ≤ (5000000489578603/5000000000000000 : ℝ)^4589 := by
      have hnat : (50000021940201084723 : ℕ)^1024*5000000000000000^4589 ≤ 5000000489578603^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000021940201084723 50000000000000000000 5000000489578603 5000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000489578603/5000000000000000 : ℝ)) (X := (50000021940201084723/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100201828316777050017/100000000000000000000 : ℝ) ≤ (7816015716373/7812500000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (100201828316777050017/100000000000000000000 : ℝ)^1024 ≤ (7816015716373/7812500000000 : ℝ)^4589 := by
      have hnat : (100201828316777050017 : ℕ)^1024*7812500000000^4589 ≤ 7816015716373^4589*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100201828316777050017 100000000000000000000 7816015716373 7812500000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (7816015716373/7812500000000 : ℝ)) (X := (100201828316777050017/100000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25100903188287982647/25000000000000000000 : ℝ) ≤ (5004499627378837/5000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (25100903188287982647/25000000000000000000 : ℝ)^1024 ≤ (5004499627378837/5000000000000000 : ℝ)^4589 := by
      have hnat : (25100903188287982647 : ℕ)^1024*5000000000000000^4589 ≤ 5004499627378837^4589*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25100903188287982647 25000000000000000000 5004499627378837 5000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004499627378837/5000000000000000 : ℝ)) (X := (25100903188287982647/25000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21940201084723/100000000000000000000 : ℝ) ≤ ((54422655987955990019/54430000000000000000 : ℝ)+2*(2249568900117/1088600000000000 : ℝ)*(3267/100000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (54422655987955990019/54430000000000000000 : ℝ)+2*(2249568900117/1088600000000000 : ℝ)*(3267/100000 : ℝ)=(5000000489578603/5000000000000000 : ℝ) by norm_num, show 1+2*(21940201084723/100000000000000000000 : ℝ)=(50000021940201084723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100903188287982647/50000000000000000000 : ℝ)+(21940201084723/100000000000000000000 : ℝ) ≤ ((54422655987955990019/54430000000000000000 : ℝ)+(2249568900117/1088600000000000 : ℝ)*((25039/100000 : ℝ)+(3267/100000 : ℝ)))^(4589/1024 : ℝ) := by
    rw [show (54422655987955990019/54430000000000000000 : ℝ)+(2249568900117/1088600000000000 : ℝ)*((25039/100000 : ℝ)+(3267/100000 : ℝ))=(7816015716373/7812500000000 : ℝ) by norm_num, show 1+(100903188287982647/50000000000000000000 : ℝ)+(21940201084723/100000000000000000000 : ℝ)=(100201828316777050017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100903188287982647/50000000000000000000 : ℝ) ≤ ((54422655987955990019/54430000000000000000 : ℝ)+2*(2249568900117/1088600000000000 : ℝ)*(25039/100000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (54422655987955990019/54430000000000000000 : ℝ)+2*(2249568900117/1088600000000000 : ℝ)*(25039/100000 : ℝ)=(5004499627378837/5000000000000000 : ℝ) by norm_num, show 1+2*(100903188287982647/50000000000000000000 : ℝ)=(25100903188287982647/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54422655987955990019/54430000000000000000 : ℝ)*(X 1 0+X 2 0)+(2249568900117/1088600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (3267/100000 : ℝ)) (hi := (25039/100000 : ℝ)) (c := (54422655987955990019/54430000000000000000 : ℝ)) (alpha := (2249568900117/1088600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54422655987955990019/54430000000000000000 : ℝ)*(X 0 1+X 2 1)+(2249568900117/1088600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (3267/100000 : ℝ)) (hi := (25039/100000 : ℝ)) (c := (54422655987955990019/54430000000000000000 : ℝ)) (alpha := (2249568900117/1088600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54422655987955990019/54430000000000000000 : ℝ)*(X 0 2+X 1 2)+(2249568900117/1088600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (3267/100000 : ℝ)) (hi := (25039/100000 : ℝ)) (c := (54422655987955990019/54430000000000000000 : ℝ)) (alpha := (2249568900117/1088600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1793819243/10000000000 : ℝ)*X 0 0+(69353933/125000000 : ℝ)*X 0 1+(204602313/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1345096651/2500000000 : ℝ)*X 1 0+(-2021012749/10000000000 : ℝ)*X 1 1+(5115056581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21521543/40000000 : ℝ)*X 2 0+(1278764299/2500000000 : ℝ)*X 2 1+(-2021013079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4236839609/10000000000 : ℝ)*X 0 0+(93950591/250000000 : ℝ)*X 0 1+(1191187213/2500000000 : ℝ)*X 0 2+(4236839609/10000000000 : ℝ)*X 1 0+(93950591/250000000 : ℝ)*X 1 1+(1191187213/2500000000 : ℝ)*X 1 2+(4236839609/10000000000 : ℝ)*X 2 0+(93950591/250000000 : ℝ)*X 2 1+(1191187213/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1794063249/10000000000 : ℝ)*X 0 0+(5119670297/10000000000 : ℝ)*X 0 1+(43309617/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265813333/10000000000 : ℝ)*X 1 0+(-1592440309/10000000000 : ℝ)*X 1 1+(5543630791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265814551/10000000000 : ℝ)*X 2 0+(692953821/1250000000 : ℝ)*X 2 1+(-1592438909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118702229/5000000000 : ℝ)*X 0 0+(594253619/1250000000 : ℝ)*X 0 1+(3768906559/10000000000 : ℝ)*X 0 2+(2118702229/5000000000 : ℝ)*X 1 0+(594253619/1250000000 : ℝ)*X 1 1+(3768906559/10000000000 : ℝ)*X 1 2+(2118702229/5000000000 : ℝ)*X 2 0+(594253619/1250000000 : ℝ)*X 2 1+(3768906559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1739083559065063050326770749/680375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238013339/100000000000000 : ℝ)*(base19) + (4406943/12500000000000 : ℝ)*(lower2) + (9786589/25000000000000 : ℝ)*(lower3) + (30732219/25000000000000 : ℝ)*(lower4) + (412677761622481/25000000000000 : ℝ)*(major0) + (412677761622481/25000000000000 : ℝ)*(major1) + (412677761622481/25000000000000 : ℝ)*(major2) + (461620234152097/20000000000000 : ℝ)*(sp0) + (1154048929728839/50000000000000 : ℝ)*(sp1) + (1154048236030951/50000000000000 : ℝ)*(sp2) + (124165092535427/12500000000000 : ℝ)*(sp3) + (768322367/25000000000000 : ℝ)*(sp5) + (587337323/12500000000000 : ℝ)*(sp6) + (96733729/100000000000000 : ℝ)*(sp7) + (496660418508573/50000000000000 : ℝ)*(f.failure) + (461620234152097/20000000000000 : ℝ)*(f.sum) + (127726286261211/27215000000000000000000000000 : ℝ)*base66 + (17925994987829867139/1360750000000000000000000000000000 : ℝ)*base67 + (17222983340064867139/1360750000000000000000000000000000 : ℝ)*base69 + (4373831337139367139/1360750000000000000000000000000000 : ℝ)*base71 + (2782198284767/850468750000000000000000000 : ℝ)*base73 + (12588754653669117139/1360750000000000000000000000000000 : ℝ)*base75 + (495734757613367139/1360750000000000000000000000000000 : ℝ)*base77 + (9755695329811867139/1360750000000000000000000000000000 : ℝ)*base79 + (225533382224319/27215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2463097/1000000000000000000000 : ℝ)*base90 + (2463097/1000000000000000000000 : ℝ)*base92 + (2463097/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7863903818742456888386706357/2721500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60814661/25000000000000 : ℝ)*(base19) + (407818683/50000000000000 : ℝ)*(base23) + (64768811/100000000000000 : ℝ)*(upper3) + (329867/625000000000 : ℝ)*(upper4) + (30877841/12500000000000 : ℝ)*(upper5) + (1686908932205901/100000000000000 : ℝ)*(major0) + (1686908932205901/100000000000000 : ℝ)*(major1) + (1686908932205901/100000000000000 : ℝ)*(major2) + (729800727/12500000000000 : ℝ)*(sp2) + (211266151/50000000000000 : ℝ)*(sp3) + (36854917711113/1562500000000 : ℝ)*(sp4) + (589678622563147/25000000000000 : ℝ)*(sp5) + (2358708079468049/100000000000000 : ℝ)*(sp6) + (101510261205001/10000000000000 : ℝ)*(sp7) + (126887879322789/12500000000000 : ℝ)*(f.failure) + (36854917711113/1562500000000 : ℝ)*(f.sum) + (153475443426517/54430000000000000000000000000 : ℝ)*base65 + (23045830018342247881/5443000000000000000000000000000000 : ℝ)*base68 + (28540378613888247881/5443000000000000000000000000000000 : ℝ)*base70 + (2372040168256247881/5443000000000000000000000000000000 : ℝ)*base72 + (20657677341977/54430000000000000000000000000 : ℝ)*base73 + (2659537795356247881/5443000000000000000000000000000000 : ℝ)*base76 + (22343821649358752119/5443000000000000000000000000000000 : ℝ)*base77 + (48102356107905752119/5443000000000000000000000000000000 : ℝ)*base79 + (177908829177853/54430000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (187521/250000000000000000000 : ℝ)*base90 + (187521/250000000000000000000 : ℝ)*base92 + (187521/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1547_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4493/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1547_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1547_s2_0 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-453648481/2500000000 : ℝ)*x 0 + (5447510991/10000000000 : ℝ)*x 1 + (1040471089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453648481/2500000000 : ℝ)^4591 ≤ (11117134027707/100000000000000 : ℝ)^3567 := by
    have hnat : (453648481 : ℕ)^4591*100000000000000^3567 ≤ 11117134027707^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453648481 2500000000 11117134027707 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447510991/10000000000 : ℝ)^4591 ≤ (45757989264011/100000000000000 : ℝ)^3567 := by
    have hnat : (5447510991 : ℕ)^4591*100000000000000^3567 ≤ 45757989264011^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447510991 10000000000 45757989264011 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040471089/2000000000 : ℝ)^4591 ≤ (43124876688023/100000000000000 : ℝ)^3567 := by
    have hnat : (1040471089 : ℕ)^4591*100000000000000^3567 ≤ 43124876688023^3567*2000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040471089 2000000000 43124876688023 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453648481/2500000000 : ℝ), (5447510991/10000000000 : ℝ), (1040471089/2000000000 : ℝ)] ![(11117134027707/100000000000000 : ℝ), (45757989264011/100000000000000 : ℝ), (43124876688023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453648481/2500000000 : ℝ)|^4591 ≤ (11117134027707/100000000000000 : ℝ)^3567
        have hw : |(-453648481/2500000000 : ℝ)|=(453648481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447510991/10000000000 : ℝ)|^4591 ≤ (45757989264011/100000000000000 : ℝ)^3567
        have hw : |(5447510991/10000000000 : ℝ)|=(5447510991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040471089/2000000000 : ℝ)|^4591 ≤ (43124876688023/100000000000000 : ℝ)^3567
        have hw : |(1040471089/2000000000 : ℝ)|=(1040471089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_1 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338627269/2500000000 : ℝ)*x 0 + (-1940556217/10000000000 : ℝ)*x 1 + (5202355373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338627269/2500000000 : ℝ)^4591 ≤ (44755003031047/100000000000000 : ℝ)^3567 := by
    have hnat : (1338627269 : ℕ)^4591*100000000000000^3567 ≤ 44755003031047^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338627269 2500000000 44755003031047 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940556217/10000000000 : ℝ)^4591 ≤ (3030030259317/25000000000000 : ℝ)^3567 := by
    have hnat : (1940556217 : ℕ)^4591*25000000000000^3567 ≤ 3030030259317^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940556217 10000000000 3030030259317 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202355373/10000000000 : ℝ)^4591 ≤ (269530474499/625000000000 : ℝ)^3567 := by
    have hnat : (5202355373 : ℕ)^4591*625000000000^3567 ≤ 269530474499^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202355373 10000000000 269530474499 625000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338627269/2500000000 : ℝ), (-1940556217/10000000000 : ℝ), (5202355373/10000000000 : ℝ)] ![(44755003031047/100000000000000 : ℝ), (3030030259317/25000000000000 : ℝ), (269530474499/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338627269/2500000000 : ℝ)|^4591 ≤ (44755003031047/100000000000000 : ℝ)^3567
        have hw : |(1338627269/2500000000 : ℝ)|=(1338627269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1940556217/10000000000 : ℝ)|^4591 ≤ (3030030259317/25000000000000 : ℝ)^3567
        have hw : |(-1940556217/10000000000 : ℝ)|=(1940556217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202355373/10000000000 : ℝ)|^4591 ≤ (269530474499/625000000000 : ℝ)^3567
        have hw : |(5202355373/10000000000 : ℝ)|=(5202355373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_2 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677254499/5000000000 : ℝ)*x 0 + (5202355447/10000000000 : ℝ)*x 1 + (-1940556223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677254499/5000000000 : ℝ)^4591 ≤ (22377501095967/50000000000000 : ℝ)^3567 := by
    have hnat : (2677254499 : ℕ)^4591*50000000000000^3567 ≤ 22377501095967^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677254499 5000000000 22377501095967 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202355447/10000000000 : ℝ)^4591 ≤ (43124876709361/100000000000000 : ℝ)^3567 := by
    have hnat : (5202355447 : ℕ)^4591*100000000000000^3567 ≤ 43124876709361^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202355447 10000000000 43124876709361 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1940556223/10000000000 : ℝ)^4591 ≤ (24240242171/200000000000 : ℝ)^3567 := by
    have hnat : (1940556223 : ℕ)^4591*200000000000^3567 ≤ 24240242171^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940556223 10000000000 24240242171 200000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677254499/5000000000 : ℝ), (5202355447/10000000000 : ℝ), (-1940556223/10000000000 : ℝ)] ![(22377501095967/50000000000000 : ℝ), (43124876709361/100000000000000 : ℝ), (24240242171/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677254499/5000000000 : ℝ)|^4591 ≤ (22377501095967/50000000000000 : ℝ)^3567
        have hw : |(2677254499/5000000000 : ℝ)|=(2677254499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202355447/10000000000 : ℝ)|^4591 ≤ (43124876709361/100000000000000 : ℝ)^3567
        have hw : |(5202355447/10000000000 : ℝ)|=(5202355447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1940556223/10000000000 : ℝ)|^4591 ≤ (24240242171/200000000000 : ℝ)^3567
        have hw : |(-1940556223/10000000000 : ℝ)|=(1940556223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_3 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125920867/5000000000 : ℝ)*x 0 + (3974881441/10000000000 : ℝ)*x 1 + (181781207/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125920867/5000000000 : ℝ)^4591 ≤ (33262163717239/100000000000000 : ℝ)^3567 := by
    have hnat : (2125920867 : ℕ)^4591*100000000000000^3567 ≤ 33262163717239^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125920867 5000000000 33262163717239 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3974881441/10000000000 : ℝ)^4591 ≤ (3812499460919/12500000000000 : ℝ)^3567 := by
    have hnat : (3974881441 : ℕ)^4591*12500000000000^3567 ≤ 3812499460919^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3974881441 10000000000 3812499460919 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181781207/400000000 : ℝ)^4591 ≤ (1811892028461/5000000000000 : ℝ)^3567 := by
    have hnat : (181781207 : ℕ)^4591*5000000000000^3567 ≤ 1811892028461^3567*400000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181781207 400000000 1811892028461 5000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125920867/5000000000 : ℝ), (3974881441/10000000000 : ℝ), (181781207/400000000 : ℝ)] ![(33262163717239/100000000000000 : ℝ), (3812499460919/12500000000000 : ℝ), (1811892028461/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125920867/5000000000 : ℝ)|^4591 ≤ (33262163717239/100000000000000 : ℝ)^3567
        have hw : |(2125920867/5000000000 : ℝ)|=(2125920867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3974881441/10000000000 : ℝ)|^4591 ≤ (3812499460919/12500000000000 : ℝ)^3567
        have hw : |(3974881441/10000000000 : ℝ)|=(3974881441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181781207/400000000 : ℝ)|^4591 ≤ (1811892028461/5000000000000 : ℝ)^3567
        have hw : |(181781207/400000000 : ℝ)|=(181781207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_4 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-453659487/2500000000 : ℝ)*x 0 + (5203840543/10000000000 : ℝ)*x 1 + (340375823/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453659487/2500000000 : ℝ)^4591 ≤ (2223496234169/20000000000000 : ℝ)^3567 := by
    have hnat : (453659487 : ℕ)^4591*20000000000000^3567 ≤ 2223496234169^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453659487 2500000000 2223496234169 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203840543/10000000000 : ℝ)^4591 ≤ (1725628886043/4000000000000 : ℝ)^3567 := by
    have hnat : (5203840543 : ℕ)^4591*4000000000000^3567 ≤ 1725628886043^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203840543 10000000000 1725628886043 4000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340375823/625000000 : ℝ)^4591 ≤ (45741796672731/100000000000000 : ℝ)^3567 := by
    have hnat : (340375823 : ℕ)^4591*100000000000000^3567 ≤ 45741796672731^3567*625000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340375823 625000000 45741796672731 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453659487/2500000000 : ℝ), (5203840543/10000000000 : ℝ), (340375823/625000000 : ℝ)] ![(2223496234169/20000000000000 : ℝ), (1725628886043/4000000000000 : ℝ), (45741796672731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453659487/2500000000 : ℝ)|^4591 ≤ (2223496234169/20000000000000 : ℝ)^3567
        have hw : |(-453659487/2500000000 : ℝ)|=(453659487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203840543/10000000000 : ℝ)|^4591 ≤ (1725628886043/4000000000000 : ℝ)^3567
        have hw : |(5203840543/10000000000 : ℝ)|=(5203840543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340375823/625000000 : ℝ)|^4591 ≤ (45741796672731/100000000000000 : ℝ)^3567
        have hw : |(340375823/625000000 : ℝ)|=(340375823/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_5 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644912863/5000000000 : ℝ)*x 0 + (-339379693/2000000000 : ℝ)*x 1 + (170187901/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644912863/5000000000 : ℝ)^4591 ≤ (8812071662303/20000000000000 : ℝ)^3567 := by
    have hnat : (2644912863 : ℕ)^4591*20000000000000^3567 ≤ 8812071662303^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644912863 5000000000 8812071662303 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339379693/2000000000 : ℝ)^4591 ≤ (5098924316429/50000000000000 : ℝ)^3567 := by
    have hnat : (339379693 : ℕ)^4591*50000000000000^3567 ≤ 5098924316429^3567*2000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339379693 2000000000 5098924316429 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170187901/312500000 : ℝ)^4591 ≤ (22870896520231/50000000000000 : ℝ)^3567 := by
    have hnat : (170187901 : ℕ)^4591*50000000000000^3567 ≤ 22870896520231^3567*312500000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170187901 312500000 22870896520231 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644912863/5000000000 : ℝ), (-339379693/2000000000 : ℝ), (170187901/312500000 : ℝ)] ![(8812071662303/20000000000000 : ℝ), (5098924316429/50000000000000 : ℝ), (22870896520231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644912863/5000000000 : ℝ)|^4591 ≤ (8812071662303/20000000000000 : ℝ)^3567
        have hw : |(2644912863/5000000000 : ℝ)|=(2644912863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339379693/2000000000 : ℝ)|^4591 ≤ (5098924316429/50000000000000 : ℝ)^3567
        have hw : |(-339379693/2000000000 : ℝ)|=(339379693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170187901/312500000 : ℝ)|^4591 ≤ (22870896520231/50000000000000 : ℝ)^3567
        have hw : |(170187901/312500000 : ℝ)|=(170187901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_6 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165307047/312500000 : ℝ)*x 0 + (2723006627/5000000000 : ℝ)*x 1 + (-1696898183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165307047/312500000 : ℝ)^4591 ≤ (44060355931587/100000000000000 : ℝ)^3567 := by
    have hnat : (165307047 : ℕ)^4591*100000000000000^3567 ≤ 44060355931587^3567*312500000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165307047 312500000 44060355931587 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723006627/5000000000 : ℝ)^4591 ≤ (22870898801209/50000000000000 : ℝ)^3567 := by
    have hnat : (2723006627 : ℕ)^4591*50000000000000^3567 ≤ 22870898801209^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723006627 5000000000 22870898801209 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1696898183/10000000000 : ℝ)^4591 ≤ (2039569290321/20000000000000 : ℝ)^3567 := by
    have hnat : (1696898183 : ℕ)^4591*20000000000000^3567 ≤ 2039569290321^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696898183 10000000000 2039569290321 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165307047/312500000 : ℝ), (2723006627/5000000000 : ℝ), (-1696898183/10000000000 : ℝ)] ![(44060355931587/100000000000000 : ℝ), (22870898801209/50000000000000 : ℝ), (2039569290321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165307047/312500000 : ℝ)|^4591 ≤ (44060355931587/100000000000000 : ℝ)^3567
        have hw : |(165307047/312500000 : ℝ)|=(165307047/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723006627/5000000000 : ℝ)|^4591 ≤ (22870898801209/50000000000000 : ℝ)^3567
        have hw : |(2723006627/5000000000 : ℝ)|=(2723006627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1696898183/10000000000 : ℝ)|^4591 ≤ (2039569290321/20000000000000 : ℝ)^3567
        have hw : |(-1696898183/10000000000 : ℝ)|=(1696898183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s2_7 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251943189/10000000000 : ℝ)*x 0 + (2270539537/5000000000 : ℝ)*x 1 + (3978363549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251943189/10000000000 : ℝ)^4591 ≤ (33263185250549/100000000000000 : ℝ)^3567 := by
    have hnat : (4251943189 : ℕ)^4591*100000000000000^3567 ≤ 33263185250549^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251943189 10000000000 33263185250549 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270539537/5000000000 : ℝ)^4591 ≤ (36202425522317/100000000000000 : ℝ)^3567 := by
    have hnat : (2270539537 : ℕ)^4591*100000000000000^3567 ≤ 36202425522317^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270539537 5000000000 36202425522317 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3978363549/10000000000 : ℝ)^4591 ≤ (30534389206383/100000000000000 : ℝ)^3567 := by
    have hnat : (3978363549 : ℕ)^4591*100000000000000^3567 ≤ 30534389206383^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978363549 10000000000 30534389206383 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251943189/10000000000 : ℝ), (2270539537/5000000000 : ℝ), (3978363549/10000000000 : ℝ)] ![(33263185250549/100000000000000 : ℝ), (36202425522317/100000000000000 : ℝ), (30534389206383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251943189/10000000000 : ℝ)|^4591 ≤ (33263185250549/100000000000000 : ℝ)^3567
        have hw : |(4251943189/10000000000 : ℝ)|=(4251943189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270539537/5000000000 : ℝ)|^4591 ≤ (36202425522317/100000000000000 : ℝ)^3567
        have hw : |(2270539537/5000000000 : ℝ)|=(2270539537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3978363549/10000000000 : ℝ)|^4591 ≤ (30534389206383/100000000000000 : ℝ)^3567
        have hw : |(3978363549/10000000000 : ℝ)|=(3978363549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1547_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10683/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15877/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4401/50000 : ℝ) ^ (4589/1024 : ℝ) ≤ (1862941004870113/100000000000000000000 : ℝ) := by
    have hpowers : (4401/50000 : ℝ)^4589 ≤ (1862941004870113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4401 : ℕ)^4589*100000000000000000000^1024 ≤ 1862941004870113^1024*50000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4401 50000 1862941004870113 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4401/50000 : ℝ)) (X := (1862941004870113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4493/25000 : ℝ) ^ (4589/1024 : ℝ) ≤ (45657757310575471/100000000000000000000 : ℝ) := by
    have hpowers : (4493/25000 : ℝ)^4589 ≤ (45657757310575471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4493 : ℕ)^4589*100000000000000000000^1024 ≤ 45657757310575471^1024*25000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4493 25000 45657757310575471 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4493/25000 : ℝ)) (X := (45657757310575471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001862941004870113/50000000000000000000 : ℝ) ≤ (5000041569491857/5000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50001862941004870113/50000000000000000000 : ℝ)^1024 ≤ (5000041569491857/5000000000000000 : ℝ)^4589 := by
      have hnat : (50001862941004870113 : ℕ)^1024*5000000000000000^4589 ≤ 5000041569491857^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001862941004870113 50000000000000000000 5000041569491857 5000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041569491857/5000000000000000 : ℝ)) (X := (50001862941004870113/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252970043644715349/6250000000000000000 : ℝ) ≤ (2000212038420219/2000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (6252970043644715349/6250000000000000000 : ℝ)^1024 ≤ (2000212038420219/2000000000000000 : ℝ)^4589 := by
      have hnat : (6252970043644715349 : ℕ)^1024*2000000000000000^4589 ≤ 2000212038420219^4589*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252970043644715349 6250000000000000000 2000212038420219 2000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000212038420219/2000000000000000 : ℝ)) (X := (6252970043644715349/6250000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045657757310575471/50000000000000000000 : ℝ) ≤ (2500509311304619/2500000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50045657757310575471/50000000000000000000 : ℝ)^1024 ≤ (2500509311304619/2500000000000000 : ℝ)^4589 := by
      have hnat : (50045657757310575471 : ℕ)^1024*2500000000000000^4589 ≤ 2500509311304619^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045657757310575471 50000000000000000000 2500509311304619 2500000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500509311304619/2500000000000000 : ℝ)) (X := (50045657757310575471/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1862941004870113/100000000000000000000 : ℝ) ≤ ((5730222646337642641/5731250000000000000 : ℝ)+2*(977053117381/917000000000000 : ℝ)*(4401/50000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (5730222646337642641/5731250000000000000 : ℝ)+2*(977053117381/917000000000000 : ℝ)*(4401/50000 : ℝ)=(5000041569491857/5000000000000000 : ℝ) by norm_num, show 1+2*(1862941004870113/100000000000000000000 : ℝ)=(50001862941004870113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45657757310575471/100000000000000000000 : ℝ)+(1862941004870113/100000000000000000000 : ℝ) ≤ ((5730222646337642641/5731250000000000000 : ℝ)+(977053117381/917000000000000 : ℝ)*((4493/25000 : ℝ)+(4401/50000 : ℝ)))^(4589/1024 : ℝ) := by
    rw [show (5730222646337642641/5731250000000000000 : ℝ)+(977053117381/917000000000000 : ℝ)*((4493/25000 : ℝ)+(4401/50000 : ℝ))=(2000212038420219/2000000000000000 : ℝ) by norm_num, show 1+(45657757310575471/100000000000000000000 : ℝ)+(1862941004870113/100000000000000000000 : ℝ)=(6252970043644715349/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45657757310575471/100000000000000000000 : ℝ) ≤ ((5730222646337642641/5731250000000000000 : ℝ)+2*(977053117381/917000000000000 : ℝ)*(4493/25000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (5730222646337642641/5731250000000000000 : ℝ)+2*(977053117381/917000000000000 : ℝ)*(4493/25000 : ℝ)=(2500509311304619/2500000000000000 : ℝ) by norm_num, show 1+2*(45657757310575471/100000000000000000000 : ℝ)=(50045657757310575471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5730222646337642641/5731250000000000000 : ℝ)*(X 1 0+X 2 0)+(977053117381/917000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (4401/50000 : ℝ)) (hi := (4493/25000 : ℝ)) (c := (5730222646337642641/5731250000000000000 : ℝ)) (alpha := (977053117381/917000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5730222646337642641/5731250000000000000 : ℝ)*(X 0 1+X 2 1)+(977053117381/917000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (4401/50000 : ℝ)) (hi := (4493/25000 : ℝ)) (c := (5730222646337642641/5731250000000000000 : ℝ)) (alpha := (977053117381/917000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5730222646337642641/5731250000000000000 : ℝ)*(X 0 2+X 1 2)+(977053117381/917000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (4401/50000 : ℝ)) (hi := (4493/25000 : ℝ)) (c := (5730222646337642641/5731250000000000000 : ℝ)) (alpha := (977053117381/917000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-453648481/2500000000 : ℝ)*X 0 0+(5447510991/10000000000 : ℝ)*X 0 1+(1040471089/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338627269/2500000000 : ℝ)*X 1 0+(-1940556217/10000000000 : ℝ)*X 1 1+(5202355373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677254499/5000000000 : ℝ)*X 2 0+(5202355447/10000000000 : ℝ)*X 2 1+(-1940556223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125920867/5000000000 : ℝ)*X 0 0+(3974881441/10000000000 : ℝ)*X 0 1+(181781207/400000000 : ℝ)*X 0 2+(2125920867/5000000000 : ℝ)*X 1 0+(3974881441/10000000000 : ℝ)*X 1 1+(181781207/400000000 : ℝ)*X 1 2+(2125920867/5000000000 : ℝ)*X 2 0+(3974881441/10000000000 : ℝ)*X 2 1+(181781207/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-453659487/2500000000 : ℝ)*X 0 0+(5203840543/10000000000 : ℝ)*X 0 1+(340375823/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644912863/5000000000 : ℝ)*X 1 0+(-339379693/2000000000 : ℝ)*X 1 1+(170187901/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165307047/312500000 : ℝ)*X 2 0+(2723006627/5000000000 : ℝ)*X 2 1+(-1696898183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251943189/10000000000 : ℝ)*X 0 0+(2270539537/5000000000 : ℝ)*X 0 1+(3978363549/10000000000 : ℝ)*X 0 2+(4251943189/10000000000 : ℝ)*X 1 0+(2270539537/5000000000 : ℝ)*X 1 1+(3978363549/10000000000 : ℝ)*X 1 2+(4251943189/10000000000 : ℝ)*X 2 0+(2270539537/5000000000 : ℝ)*X 2 1+(3978363549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249973754466869873818923/45850000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214220853/20000000000000 : ℝ)*(base19) + (885237409/100000000000000 : ℝ)*(base23) + (33852919/50000000000000 : ℝ)*(lower2) + (89331223/50000000000000 : ℝ)*(upper3) + (13412383/20000000000000 : ℝ)*(upper5) + (2917275080380039/100000000000000 : ℝ)*(major0) + (2917275080380039/100000000000000 : ℝ)*(major1) + (2917275080380039/100000000000000 : ℝ)*(major2) + (2039528744644519/50000000000000 : ℝ)*(sp0) + (2039534485232701/50000000000000 : ℝ)*(sp1) + (2039534578166129/50000000000000 : ℝ)*(sp2) + (1755473177458781/100000000000000 : ℝ)*(sp3) + (3138070157/25000000000000 : ℝ)*(sp4) + (3379999307/50000000000000 : ℝ)*(sp7) + (351095987491479/20000000000000 : ℝ)*(f.failure) + (2039535020784833/50000000000000 : ℝ)*(f.sum) + (259890978010459/45850000000000000000000000000 : ℝ)*base65 + (2359072477563613251/573125000000000000000000000000000 : ℝ)*base68 + (667110822716386749/573125000000000000000000000000000 : ℝ)*base69 + (483976937835761749/573125000000000000000000000000000 : ℝ)*base71 + (42290451906691/45850000000000000000000000000 : ℝ)*base74 + (3842169926561113251/573125000000000000000000000000000 : ℝ)*base76 + (4389440431183261749/573125000000000000000000000000000 : ℝ)*base77 + (13000508824993613251/573125000000000000000000000000000 : ℝ)*base80 + (188128099349909/45850000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (746069/400000000000000000000 : ℝ)*base89 + (746069/400000000000000000000 : ℝ)*base91 + (746069/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8330701684007849519589/1146250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1095287229/100000000000000 : ℝ)*(base19) + (560589203/50000000000000 : ℝ)*(base23) + (70161561/100000000000000 : ℝ)*(upper2) + (35415347/100000000000000 : ℝ)*(upper5) + (9228740433533/312500000000 : ℝ)*(major0) + (9228740433533/312500000000 : ℝ)*(major1) + (9228740433533/312500000000 : ℝ)*(major2) + (3098032951/50000000000000 : ℝ)*(sp0) + (20972882703/100000000000000 : ℝ)*(sp1) + (5283092261/20000000000000 : ℝ)*(sp2) + (4129291404494029/100000000000000 : ℝ)*(sp4) + (4129275532389999/100000000000000 : ℝ)*(sp5) + (206463503196011/5000000000000 : ℝ)*(sp6) + (177709603464159/10000000000000 : ℝ)*(sp7) + (177709603464159/10000000000000 : ℝ)*(f.failure) + (1032324400139983/25000000000000 : ℝ)*(f.sum) + (15057509671443/2292500000000000000000000000 : ℝ)*base65 + (23829963343217099/14328125000000000000000000000000 : ℝ)*base67 + (633729225566819/3582031250000000000000000000000 : ℝ)*base70 + (8736083462598069/3582031250000000000000000000000 : ℝ)*base72 + (7686702634773/2292500000000000000000000000 : ℝ)*base73 + (79516951775467099/14328125000000000000000000000000 : ℝ)*base75 + (1028936911254319/3582031250000000000000000000000 : ℝ)*base78 + (55550604025060849/14328125000000000000000000000000 : ℝ)*base79 + (14040224539861/4585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (538451/200000000000000000000 : ℝ)*base90 + (538451/200000000000000000000 : ℝ)*base92 + (538451/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1547_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1547_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1547_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1547_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1547_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1547_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1547_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:17.992007+00:00
-- url     : https://prove2.me/submissions/82d131be-870a-49e3-bc18-9a14f7900aee

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
theorem support_rectangle_w1161_s3_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154237359/10000000000 : ℝ)*x 0 + (5427245173/10000000000 : ℝ)*x 1 + (523384021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154237359/10000000000 : ℝ)^4177 ≤ (130848051647/1000000000000 : ℝ)^3153 := by
    have hnat : (2154237359 : ℕ)^4177*1000000000000^3153 ≤ 130848051647^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154237359 10000000000 130848051647 1000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427245173/10000000000 : ℝ)^4177 ≤ (2225096212379/5000000000000 : ℝ)^3153 := by
    have hnat : (5427245173 : ℕ)^4177*5000000000000^3153 ≤ 2225096212379^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427245173 10000000000 2225096212379 5000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523384021/1000000000 : ℝ)^4177 ≤ (21206635287077/50000000000000 : ℝ)^3153 := by
    have hnat : (523384021 : ℕ)^4177*50000000000000^3153 ≤ 21206635287077^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523384021 1000000000 21206635287077 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154237359/10000000000 : ℝ), (5427245173/10000000000 : ℝ), (523384021/1000000000 : ℝ)] ![(130848051647/1000000000000 : ℝ), (2225096212379/5000000000000 : ℝ), (21206635287077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154237359/10000000000 : ℝ)|^4177 ≤ (130848051647/1000000000000 : ℝ)^3153
        have hw : |(-2154237359/10000000000 : ℝ)|=(2154237359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427245173/10000000000 : ℝ)|^4177 ≤ (2225096212379/5000000000000 : ℝ)^3153
        have hw : |(5427245173/10000000000 : ℝ)|=(5427245173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523384021/1000000000 : ℝ)|^4177 ≤ (21206635287077/50000000000000 : ℝ)^3153
        have hw : |(523384021/1000000000 : ℝ)|=(523384021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338334801/2500000000 : ℝ)*x 0 + (-2253058831/10000000000 : ℝ)*x 1 + (5233840017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338334801/2500000000 : ℝ)^4177 ≤ (1365652587561/3125000000000 : ℝ)^3153 := by
    have hnat : (1338334801 : ℕ)^4177*3125000000000^3153 ≤ 1365652587561^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338334801 2500000000 1365652587561 3125000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253058831/10000000000 : ℝ)^4177 ≤ (1388584867881/10000000000000 : ℝ)^3153 := by
    have hnat : (2253058831 : ℕ)^4177*10000000000000^3153 ≤ 1388584867881^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253058831 10000000000 1388584867881 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233840017/10000000000 : ℝ)^4177 ≤ (8482653700441/20000000000000 : ℝ)^3153 := by
    have hnat : (5233840017 : ℕ)^4177*20000000000000^3153 ≤ 8482653700441^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233840017 10000000000 8482653700441 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338334801/2500000000 : ℝ), (-2253058831/10000000000 : ℝ), (5233840017/10000000000 : ℝ)] ![(1365652587561/3125000000000 : ℝ), (1388584867881/10000000000000 : ℝ), (8482653700441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338334801/2500000000 : ℝ)|^4177 ≤ (1365652587561/3125000000000 : ℝ)^3153
        have hw : |(1338334801/2500000000 : ℝ)|=(1338334801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253058831/10000000000 : ℝ)|^4177 ≤ (1388584867881/10000000000000 : ℝ)^3153
        have hw : |(-2253058831/10000000000 : ℝ)|=(2253058831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233840017/10000000000 : ℝ)|^4177 ≤ (8482653700441/20000000000000 : ℝ)^3153
        have hw : |(5233840017/10000000000 : ℝ)|=(5233840017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070667857/2000000000 : ℝ)*x 0 + (1046768009/2000000000 : ℝ)*x 1 + (-2253058687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070667857/2000000000 : ℝ)^4177 ≤ (1748035347117/4000000000000 : ℝ)^3153 := by
    have hnat : (1070667857 : ℕ)^4177*4000000000000^3153 ≤ 1748035347117^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070667857 2000000000 1748035347117 4000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046768009/2000000000 : ℝ)^4177 ≤ (21206634401399/50000000000000 : ℝ)^3153 := by
    have hnat : (1046768009 : ℕ)^4177*50000000000000^3153 ≤ 21206634401399^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046768009 2000000000 21206634401399 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253058687/10000000000 : ℝ)^4177 ≤ (3471461875773/25000000000000 : ℝ)^3153 := by
    have hnat : (2253058687 : ℕ)^4177*25000000000000^3153 ≤ 3471461875773^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253058687 10000000000 3471461875773 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070667857/2000000000 : ℝ), (1046768009/2000000000 : ℝ), (-2253058687/10000000000 : ℝ)] ![(1748035347117/4000000000000 : ℝ), (21206634401399/50000000000000 : ℝ), (3471461875773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070667857/2000000000 : ℝ)|^4177 ≤ (1748035347117/4000000000000 : ℝ)^3153
        have hw : |(1070667857/2000000000 : ℝ)|=(1070667857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046768009/2000000000 : ℝ)|^4177 ≤ (21206634401399/50000000000000 : ℝ)^3153
        have hw : |(1046768009/2000000000 : ℝ)|=(1046768009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253058687/10000000000 : ℝ)|^4177 ≤ (3471461875773/25000000000000 : ℝ)^3153
        have hw : |(-2253058687/10000000000 : ℝ)|=(2253058687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544983067/1250000000 : ℝ)*x 0 + (2085495607/5000000000 : ℝ)*x 1 + (227859991/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544983067/1250000000 : ℝ)^4177 ≤ (33295429285411/100000000000000 : ℝ)^3153 := by
    have hnat : (544983067 : ℕ)^4177*100000000000000^3153 ≤ 33295429285411^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544983067 1250000000 33295429285411 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085495607/5000000000 : ℝ)^4177 ≤ (31398171803711/100000000000000 : ℝ)^3153 := by
    have hnat : (2085495607 : ℕ)^4177*100000000000000^3153 ≤ 31398171803711^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085495607 5000000000 31398171803711 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227859991/500000000 : ℝ)^4177 ≤ (35306398901837/100000000000000 : ℝ)^3153 := by
    have hnat : (227859991 : ℕ)^4177*100000000000000^3153 ≤ 35306398901837^3153*500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227859991 500000000 35306398901837 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544983067/1250000000 : ℝ), (2085495607/5000000000 : ℝ), (227859991/500000000 : ℝ)] ![(33295429285411/100000000000000 : ℝ), (31398171803711/100000000000000 : ℝ), (35306398901837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544983067/1250000000 : ℝ)|^4177 ≤ (33295429285411/100000000000000 : ℝ)^3153
        have hw : |(544983067/1250000000 : ℝ)|=(544983067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085495607/5000000000 : ℝ)|^4177 ≤ (31398171803711/100000000000000 : ℝ)^3153
        have hw : |(2085495607/5000000000 : ℝ)|=(2085495607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227859991/500000000 : ℝ)|^4177 ≤ (35306398901837/100000000000000 : ℝ)^3153
        have hw : |(227859991/500000000 : ℝ)|=(227859991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154254511/10000000000 : ℝ)*x 0 + (5234580729/10000000000 : ℝ)*x 1 + (5426500591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154254511/10000000000 : ℝ)^4177 ≤ (13084943180733/100000000000000 : ℝ)^3153 := by
    have hnat : (2154254511 : ℕ)^4177*100000000000000^3153 ≤ 13084943180733^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154254511 10000000000 13084943180733 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234580729/10000000000 : ℝ)^4177 ≤ (21210610294977/50000000000000 : ℝ)^3153 := by
    have hnat : (5234580729 : ℕ)^4177*50000000000000^3153 ≤ 21210610294977^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234580729 10000000000 21210610294977 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426500591/10000000000 : ℝ)^4177 ≤ (4449383621837/10000000000000 : ℝ)^3153 := by
    have hnat : (5426500591 : ℕ)^4177*10000000000000^3153 ≤ 4449383621837^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426500591 10000000000 4449383621837 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154254511/10000000000 : ℝ), (5234580729/10000000000 : ℝ), (5426500591/10000000000 : ℝ)] ![(13084943180733/100000000000000 : ℝ), (21210610294977/50000000000000 : ℝ), (4449383621837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154254511/10000000000 : ℝ)|^4177 ≤ (13084943180733/100000000000000 : ℝ)^3153
        have hw : |(-2154254511/10000000000 : ℝ)|=(2154254511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234580729/10000000000 : ℝ)|^4177 ≤ (21210610294977/50000000000000 : ℝ)^3153
        have hw : |(5234580729/10000000000 : ℝ)|=(5234580729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426500591/10000000000 : ℝ)|^4177 ≤ (4449383621837/10000000000000 : ℝ)^3153
        have hw : |(5426500591/10000000000 : ℝ)|=(5426500591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304273257/10000000000 : ℝ)*x 0 + (-1030199363/5000000000 : ℝ)*x 1 + (5426500419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304273257/10000000000 : ℝ)^4177 ≤ (43171051101789/100000000000000 : ℝ)^3153 := by
    have hnat : (5304273257 : ℕ)^4177*100000000000000^3153 ≤ 43171051101789^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304273257 10000000000 43171051101789 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030199363/5000000000 : ℝ)^4177 ≤ (12335114528371/100000000000000 : ℝ)^3153 := by
    have hnat : (1030199363 : ℕ)^4177*100000000000000^3153 ≤ 12335114528371^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030199363 5000000000 12335114528371 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426500419/10000000000 : ℝ)^4177 ≤ (2224691717503/5000000000000 : ℝ)^3153 := by
    have hnat : (5426500419 : ℕ)^4177*5000000000000^3153 ≤ 2224691717503^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426500419 10000000000 2224691717503 5000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304273257/10000000000 : ℝ), (-1030199363/5000000000 : ℝ), (5426500419/10000000000 : ℝ)] ![(43171051101789/100000000000000 : ℝ), (12335114528371/100000000000000 : ℝ), (2224691717503/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304273257/10000000000 : ℝ)|^4177 ≤ (43171051101789/100000000000000 : ℝ)^3153
        have hw : |(5304273257/10000000000 : ℝ)|=(5304273257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030199363/5000000000 : ℝ)|^4177 ≤ (12335114528371/100000000000000 : ℝ)^3153
        have hw : |(-1030199363/5000000000 : ℝ)|=(1030199363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426500419/10000000000 : ℝ)|^4177 ≤ (2224691717503/5000000000000 : ℝ)^3153
        have hw : |(5426500419/10000000000 : ℝ)|=(5426500419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304274031/10000000000 : ℝ)*x 0 + (169578119/312500000 : ℝ)*x 1 + (-206039851/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304274031/10000000000 : ℝ)^4177 ≤ (43171059447209/100000000000000 : ℝ)^3153 := by
    have hnat : (5304274031 : ℕ)^4177*100000000000000^3153 ≤ 43171059447209^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304274031 10000000000 43171059447209 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169578119/312500000 : ℝ)^4177 ≤ (8898765542643/20000000000000 : ℝ)^3153 := by
    have hnat : (169578119 : ℕ)^4177*20000000000000^3153 ≤ 8898765542643^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169578119 312500000 8898765542643 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206039851/1000000000 : ℝ)^4177 ≤ (6167556407629/50000000000000 : ℝ)^3153 := by
    have hnat : (206039851 : ℕ)^4177*50000000000000^3153 ≤ 6167556407629^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206039851 1000000000 6167556407629 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304274031/10000000000 : ℝ), (169578119/312500000 : ℝ), (-206039851/1000000000 : ℝ)] ![(43171059447209/100000000000000 : ℝ), (8898765542643/20000000000000 : ℝ), (6167556407629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304274031/10000000000 : ℝ)|^4177 ≤ (43171059447209/100000000000000 : ℝ)^3153
        have hw : |(5304274031/10000000000 : ℝ)|=(5304274031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169578119/312500000 : ℝ)|^4177 ≤ (8898765542643/20000000000000 : ℝ)^3153
        have hw : |(169578119/312500000 : ℝ)|=(169578119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206039851/1000000000 : ℝ)|^4177 ≤ (6167556407629/50000000000000 : ℝ)^3153
        have hw : |(-206039851/1000000000 : ℝ)|=(206039851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s3_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179949299/5000000000 : ℝ)*x 0 + (569465149/1250000000 : ℝ)*x 1 + (4172478263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179949299/5000000000 : ℝ)^4177 ≤ (33295773891401/100000000000000 : ℝ)^3153 := by
    have hnat : (2179949299 : ℕ)^4177*100000000000000^3153 ≤ 33295773891401^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179949299 5000000000 33295773891401 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569465149/1250000000 : ℝ)^4177 ≤ (35291223790067/100000000000000 : ℝ)^3153 := by
    have hnat : (569465149 : ℕ)^4177*100000000000000^3153 ≤ 35291223790067^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569465149 1250000000 35291223790067 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172478263/10000000000 : ℝ)^4177 ≤ (3141300231113/10000000000000 : ℝ)^3153 := by
    have hnat : (4172478263 : ℕ)^4177*10000000000000^3153 ≤ 3141300231113^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172478263 10000000000 3141300231113 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179949299/5000000000 : ℝ), (569465149/1250000000 : ℝ), (4172478263/10000000000 : ℝ)] ![(33295773891401/100000000000000 : ℝ), (35291223790067/100000000000000 : ℝ), (3141300231113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179949299/5000000000 : ℝ)|^4177 ≤ (33295773891401/100000000000000 : ℝ)^3153
        have hw : |(2179949299/5000000000 : ℝ)|=(2179949299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569465149/1250000000 : ℝ)|^4177 ≤ (35291223790067/100000000000000 : ℝ)^3153
        have hw : |(569465149/1250000000 : ℝ)|=(569465149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172478263/10000000000 : ℝ)|^4177 ≤ (3141300231113/10000000000000 : ℝ)^3153
        have hw : |(4172478263/10000000000 : ℝ)|=(4172478263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10691/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14783/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8223/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1831/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8223/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1831/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8223/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1831/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8223/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1831/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8223/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1831/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8223/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1831/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1831/20000 : ℝ) ^ (8353/2048 : ℝ) ≤ (5821111932351401/100000000000000000000 : ℝ) := by
    have hpowers : (1831/20000 : ℝ)^8353 ≤ (5821111932351401/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1831 : ℕ)^8353*100000000000000000000^2048 ≤ 5821111932351401^2048*20000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1831 20000 5821111932351401 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1831/20000 : ℝ)) (X := (5821111932351401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8223/50000 : ℝ) ^ (8353/2048 : ℝ) ≤ (3967282145933709/6250000000000000000 : ℝ) := by
    have hpowers : (8223/50000 : ℝ)^8353 ≤ (3967282145933709/6250000000000000000 : ℝ)^2048 := by
      have hnat : (8223 : ℕ)^8353*6250000000000000000^2048 ≤ 3967282145933709^2048*50000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8223 50000 3967282145933709 6250000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8223/50000 : ℝ)) (X := (3967282145933709/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005821111932351401/50000000000000000000 : ℝ) ≤ (10000285433100689/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50005821111932351401/50000000000000000000 : ℝ)^2048 ≤ (10000285433100689/10000000000000000 : ℝ)^8353 := by
      have hnat : (50005821111932351401 : ℕ)^2048*10000000000000000^8353 ≤ 10000285433100689^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005821111932351401 50000000000000000000 10000285433100689 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000285433100689/10000000000000000 : ℝ)) (X := (50005821111932351401/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013859525253458149/20000000000000000000 : ℝ) ≤ (1250212325565793/1250000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (20013859525253458149/20000000000000000000 : ℝ)^2048 ≤ (1250212325565793/1250000000000000 : ℝ)^8353 := by
      have hnat : (20013859525253458149 : ℕ)^2048*1250000000000000^8353 ≤ 1250212325565793^8353*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013859525253458149 20000000000000000000 1250212325565793 1250000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250212325565793/1250000000000000 : ℝ)) (X := (20013859525253458149/20000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3128967282145933709/3125000000000000000 : ℝ) ≤ (10003111775951999/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (3128967282145933709/3125000000000000000 : ℝ)^2048 ≤ (10003111775951999/10000000000000000 : ℝ)^8353 := by
      have hnat : (3128967282145933709 : ℕ)^2048*10000000000000000^8353 ≤ 10003111775951999^8353*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128967282145933709 3125000000000000000 10003111775951999 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003111775951999/10000000000000000 : ℝ)) (X := (3128967282145933709/3125000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5821111932351401/100000000000000000000 : ℝ) ≤ ((72886205923933380449/72910000000000000000 : ℝ)+2*(282634285131/145820000000000 : ℝ)*(1831/20000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (72886205923933380449/72910000000000000000 : ℝ)+2*(282634285131/145820000000000 : ℝ)*(1831/20000 : ℝ)=(10000285433100689/10000000000000000 : ℝ) by norm_num, show 1+2*(5821111932351401/100000000000000000000 : ℝ)=(50005821111932351401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3967282145933709/6250000000000000000 : ℝ)+(5821111932351401/100000000000000000000 : ℝ) ≤ ((72886205923933380449/72910000000000000000 : ℝ)+(282634285131/145820000000000 : ℝ)*((8223/50000 : ℝ)+(1831/20000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (72886205923933380449/72910000000000000000 : ℝ)+(282634285131/145820000000000 : ℝ)*((8223/50000 : ℝ)+(1831/20000 : ℝ))=(1250212325565793/1250000000000000 : ℝ) by norm_num, show 1+(3967282145933709/6250000000000000000 : ℝ)+(5821111932351401/100000000000000000000 : ℝ)=(20013859525253458149/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3967282145933709/6250000000000000000 : ℝ) ≤ ((72886205923933380449/72910000000000000000 : ℝ)+2*(282634285131/145820000000000 : ℝ)*(8223/50000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (72886205923933380449/72910000000000000000 : ℝ)+2*(282634285131/145820000000000 : ℝ)*(8223/50000 : ℝ)=(10003111775951999/10000000000000000 : ℝ) by norm_num, show 1+2*(3967282145933709/6250000000000000000 : ℝ)=(3128967282145933709/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72886205923933380449/72910000000000000000 : ℝ)*(X 1 0+X 2 0)+(282634285131/145820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (1831/20000 : ℝ)) (hi := (8223/50000 : ℝ)) (c := (72886205923933380449/72910000000000000000 : ℝ)) (alpha := (282634285131/145820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72886205923933380449/72910000000000000000 : ℝ)*(X 0 1+X 2 1)+(282634285131/145820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (1831/20000 : ℝ)) (hi := (8223/50000 : ℝ)) (c := (72886205923933380449/72910000000000000000 : ℝ)) (alpha := (282634285131/145820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72886205923933380449/72910000000000000000 : ℝ)*(X 0 2+X 1 2)+(282634285131/145820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (1831/20000 : ℝ)) (hi := (8223/50000 : ℝ)) (c := (72886205923933380449/72910000000000000000 : ℝ)) (alpha := (282634285131/145820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154237359/10000000000 : ℝ)*X 0 0+(5427245173/10000000000 : ℝ)*X 0 1+(523384021/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338334801/2500000000 : ℝ)*X 1 0+(-2253058831/10000000000 : ℝ)*X 1 1+(5233840017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070667857/2000000000 : ℝ)*X 2 0+(1046768009/2000000000 : ℝ)*X 2 1+(-2253058687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544983067/1250000000 : ℝ)*X 0 0+(2085495607/5000000000 : ℝ)*X 0 1+(227859991/500000000 : ℝ)*X 0 2+(544983067/1250000000 : ℝ)*X 1 0+(2085495607/5000000000 : ℝ)*X 1 1+(227859991/500000000 : ℝ)*X 1 2+(544983067/1250000000 : ℝ)*X 2 0+(2085495607/5000000000 : ℝ)*X 2 1+(227859991/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2154254511/10000000000 : ℝ)*X 0 0+(5234580729/10000000000 : ℝ)*X 0 1+(5426500591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304273257/10000000000 : ℝ)*X 1 0+(-1030199363/5000000000 : ℝ)*X 1 1+(5426500419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304274031/10000000000 : ℝ)*X 2 0+(169578119/312500000 : ℝ)*X 2 1+(-206039851/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179949299/5000000000 : ℝ)*X 0 0+(569465149/1250000000 : ℝ)*X 0 1+(4172478263/10000000000 : ℝ)*X 0 2+(2179949299/5000000000 : ℝ)*X 1 0+(569465149/1250000000 : ℝ)*X 1 1+(4172478263/10000000000 : ℝ)*X 1 2+(2179949299/5000000000 : ℝ)*X 2 0+(569465149/1250000000 : ℝ)*X 2 1+(4172478263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52299227013578582463/22784375000000000000000000 : ℝ) := by norm_num
    linear_combination (380496157/50000000000000 : ℝ)*(base19) + (376504037/50000000000000 : ℝ)*(base23) + (11538859/25000000000000 : ℝ)*(lower2) + (1625661/20000000000000 : ℝ)*(upper3) + (112915799/100000000000000 : ℝ)*(upper5) + (1939951105685199/50000000000000 : ℝ)*(major0) + (1939951105685199/50000000000000 : ℝ)*(major1) + (1939951105685199/50000000000000 : ℝ)*(major2) + (1034101277814963/20000000000000 : ℝ)*(sp0) + (1292629713120399/25000000000000 : ℝ)*(sp1) + (1034103772093167/20000000000000 : ℝ)*(sp2) + (1294639945259611/50000000000000 : ℝ)*(sp3) + (2644879819/20000000000000 : ℝ)*(sp4) + (1210558591/25000000000000 : ℝ)*(sp7) + (1294642366376793/50000000000000 : ℝ)*(f.failure) + (517051961347391/10000000000000 : ℝ)*(f.sum) + (228766326109/455687500000000000000000000 : ℝ)*base65 + (8055012775036774351/3645500000000000000000000000000000 : ℝ)*base67 + (16670676575281274351/3645500000000000000000000000000000 : ℝ)*base69 + (13231892554225649/3645500000000000000000000000000000 : ℝ)*base72 + (10562081612109/3645500000000000000000000000 : ℝ)*base73 + (22766892301002225649/3645500000000000000000000000000000 : ℝ)*base76 + (26809619596944725649/3645500000000000000000000000000000 : ℝ)*base78 + (9364825158249274351/3645500000000000000000000000000000 : ℝ)*base79 + (46640271725181/7291000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6052773/1250000000000000000000 : ℝ)*base90 + (6052773/1250000000000000000000 : ℝ)*base92 + (6052773/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1938443249172346554238527033/911375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223795787/100000000000000 : ℝ)*(base19) + (1072560697/100000000000000 : ℝ)*(base23) + (809917/20000000000000 : ℝ)*(upper2) + (5970473/25000000000000 : ℝ)*(upper5) + (1954957121971461/50000000000000 : ℝ)*(major0) + (1954957121971461/50000000000000 : ℝ)*(major1) + (1954957121971461/50000000000000 : ℝ)*(major2) + (101370151/50000000000000 : ℝ)*(sp0) + (431799671/50000000000000 : ℝ)*(sp1) + (59999279/625000000000 : ℝ)*(sp2) + (2605257352045157/50000000000000 : ℝ)*(sp4) + (5210513819435487/100000000000000 : ℝ)*(sp5) + (5210504234385279/100000000000000 : ℝ)*(sp6) + (26093135101571/1000000000000 : ℝ)*(sp7) + (26093135101571/1000000000000 : ℝ)*(f.failure) + (651314363353827/12500000000000 : ℝ)*(f.sum) + (10770797095367/3645500000000000000000000000 : ℝ)*base65 + (1950067308987134011/3645500000000000000000000000000000 : ℝ)*base68 + (23768381286451865989/3645500000000000000000000000000000 : ℝ)*base69 + (23978418835950365989/3645500000000000000000000000000000 : ℝ)*base71 + (7842715815047/3645500000000000000000000000 : ℝ)*base74 + (18191062034930365989/3645500000000000000000000000000000 : ℝ)*base75 + (13696661127699365989/3645500000000000000000000000000000 : ℝ)*base77 + (37560174912372865989/3645500000000000000000000000000000 : ℝ)*base79 + (2440049352719/911375000000000000000000000 : ℝ)*base81 + (150631/25000000000000000000 : ℝ)*base90 + (150631/25000000000000000000 : ℝ)*base92 + (150631/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1161_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_s4_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-539271971/2500000000 : ℝ)*x 0 + (2700495493/5000000000 : ℝ)*x 1 + (5258229269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539271971/2500000000 : ℝ)^4177 ≤ (2621549444243/20000000000000 : ℝ)^3153 := by
    have hnat : (539271971 : ℕ)^4177*20000000000000^3153 ≤ 2621549444243^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539271971 2500000000 2621549444243 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700495493/5000000000 : ℝ)^4177 ≤ (4421695580551/10000000000000 : ℝ)^3153 := by
    have hnat : (2700495493 : ℕ)^4177*10000000000000^3153 ≤ 4421695580551^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700495493 5000000000 4421695580551 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258229269/10000000000 : ℝ)^4177 ≤ (42675296951607/100000000000000 : ℝ)^3153 := by
    have hnat : (5258229269 : ℕ)^4177*100000000000000^3153 ≤ 42675296951607^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258229269 10000000000 42675296951607 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539271971/2500000000 : ℝ), (2700495493/5000000000 : ℝ), (5258229269/10000000000 : ℝ)] ![(2621549444243/20000000000000 : ℝ), (4421695580551/10000000000000 : ℝ), (42675296951607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539271971/2500000000 : ℝ)|^4177 ≤ (2621549444243/20000000000000 : ℝ)^3153
        have hw : |(-539271971/2500000000 : ℝ)|=(539271971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700495493/5000000000 : ℝ)|^4177 ≤ (4421695580551/10000000000000 : ℝ)^3153
        have hw : |(2700495493/5000000000 : ℝ)|=(2700495493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258229269/10000000000 : ℝ)|^4177 ≤ (42675296951607/100000000000000 : ℝ)^3153
        have hw : |(5258229269/10000000000 : ℝ)|=(5258229269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673385653/5000000000 : ℝ)*x 0 + (-111481191/500000000 : ℝ)*x 1 + (2629114719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673385653/5000000000 : ℝ)^4177 ≤ (43629868504287/100000000000000 : ℝ)^3153 := by
    have hnat : (2673385653 : ℕ)^4177*100000000000000^3153 ≤ 43629868504287^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673385653 5000000000 43629868504287 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111481191/500000000 : ℝ)^4177 ≤ (3423708177447/25000000000000 : ℝ)^3153 := by
    have hnat : (111481191 : ℕ)^4177*25000000000000^3153 ≤ 3423708177447^3153*500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111481191 500000000 3423708177447 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629114719/5000000000 : ℝ)^4177 ≤ (21337649384323/50000000000000 : ℝ)^3153 := by
    have hnat : (2629114719 : ℕ)^4177*50000000000000^3153 ≤ 21337649384323^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629114719 5000000000 21337649384323 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673385653/5000000000 : ℝ), (-111481191/500000000 : ℝ), (2629114719/5000000000 : ℝ)] ![(43629868504287/100000000000000 : ℝ), (3423708177447/25000000000000 : ℝ), (21337649384323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673385653/5000000000 : ℝ)|^4177 ≤ (43629868504287/100000000000000 : ℝ)^3153
        have hw : |(2673385653/5000000000 : ℝ)|=(2673385653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111481191/500000000 : ℝ)|^4177 ≤ (3423708177447/25000000000000 : ℝ)^3153
        have hw : |(-111481191/500000000 : ℝ)|=(111481191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629114719/5000000000 : ℝ)|^4177 ≤ (21337649384323/50000000000000 : ℝ)^3153
        have hw : |(2629114719/5000000000 : ℝ)|=(2629114719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346771293/10000000000 : ℝ)*x 0 + (2629114743/5000000000 : ℝ)*x 1 + (-2229623773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346771293/10000000000 : ℝ)^4177 ≤ (8725973672751/20000000000000 : ℝ)^3153 := by
    have hnat : (5346771293 : ℕ)^4177*20000000000000^3153 ≤ 8725973672751^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346771293 10000000000 8725973672751 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629114743/5000000000 : ℝ)^4177 ≤ (5334412410591/12500000000000 : ℝ)^3153 := by
    have hnat : (2629114743 : ℕ)^4177*12500000000000^3153 ≤ 5334412410591^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629114743 5000000000 5334412410591 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229623773/10000000000 : ℝ)^4177 ≤ (3423708081837/25000000000000 : ℝ)^3153 := by
    have hnat : (2229623773 : ℕ)^4177*25000000000000^3153 ≤ 3423708081837^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229623773 10000000000 3423708081837 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346771293/10000000000 : ℝ), (2629114743/5000000000 : ℝ), (-2229623773/10000000000 : ℝ)] ![(8725973672751/20000000000000 : ℝ), (5334412410591/12500000000000 : ℝ), (3423708081837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346771293/10000000000 : ℝ)|^4177 ≤ (8725973672751/20000000000000 : ℝ)^3153
        have hw : |(5346771293/10000000000 : ℝ)|=(5346771293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629114743/5000000000 : ℝ)|^4177 ≤ (5334412410591/12500000000000 : ℝ)^3153
        have hw : |(2629114743/5000000000 : ℝ)|=(2629114743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229623773/10000000000 : ℝ)|^4177 ≤ (3423708081837/25000000000000 : ℝ)^3153
        have hw : |(-2229623773/10000000000 : ℝ)|=(2229623773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361568767/10000000000 : ℝ)*x 0 + (2110667769/5000000000 : ℝ)*x 1 + (4506415009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361568767/10000000000 : ℝ)^4177 ≤ (33312672099747/100000000000000 : ℝ)^3153 := by
    have hnat : (4361568767 : ℕ)^4177*100000000000000^3153 ≤ 33312672099747^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361568767 10000000000 33312672099747 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110667769/5000000000 : ℝ)^4177 ≤ (3987651717929/12500000000000 : ℝ)^3153 := by
    have hnat : (2110667769 : ℕ)^4177*12500000000000^3153 ≤ 3987651717929^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110667769 5000000000 3987651717929 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506415009/10000000000 : ℝ)^4177 ≤ (34786114143627/100000000000000 : ℝ)^3153 := by
    have hnat : (4506415009 : ℕ)^4177*100000000000000^3153 ≤ 34786114143627^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506415009 10000000000 34786114143627 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361568767/10000000000 : ℝ), (2110667769/5000000000 : ℝ), (4506415009/10000000000 : ℝ)] ![(33312672099747/100000000000000 : ℝ), (3987651717929/12500000000000 : ℝ), (34786114143627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361568767/10000000000 : ℝ)|^4177 ≤ (33312672099747/100000000000000 : ℝ)^3153
        have hw : |(4361568767/10000000000 : ℝ)|=(4361568767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110667769/5000000000 : ℝ)|^4177 ≤ (3987651717929/12500000000000 : ℝ)^3153
        have hw : |(2110667769/5000000000 : ℝ)|=(2110667769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506415009/10000000000 : ℝ)|^4177 ≤ (34786114143627/100000000000000 : ℝ)^3153
        have hw : |(4506415009/10000000000 : ℝ)|=(4506415009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078547491/5000000000 : ℝ)*x 0 + (5258633529/10000000000 : ℝ)*x 1 + (108011699/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078547491/5000000000 : ℝ)^4177 ≤ (6553902180391/50000000000000 : ℝ)^3153 := by
    have hnat : (1078547491 : ℕ)^4177*50000000000000^3153 ≤ 6553902180391^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078547491 5000000000 6553902180391 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258633529/10000000000 : ℝ)^4177 ≤ (8535928698423/20000000000000 : ℝ)^3153 := by
    have hnat : (5258633529 : ℕ)^4177*20000000000000^3153 ≤ 8535928698423^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258633529 10000000000 8535928698423 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108011699/200000000 : ℝ)^4177 ≤ (44212552131821/100000000000000 : ℝ)^3153 := by
    have hnat : (108011699 : ℕ)^4177*100000000000000^3153 ≤ 44212552131821^3153*200000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108011699 200000000 44212552131821 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078547491/5000000000 : ℝ), (5258633529/10000000000 : ℝ), (108011699/200000000 : ℝ)] ![(6553902180391/50000000000000 : ℝ), (8535928698423/20000000000000 : ℝ), (44212552131821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078547491/5000000000 : ℝ)|^4177 ≤ (6553902180391/50000000000000 : ℝ)^3153
        have hw : |(-1078547491/5000000000 : ℝ)|=(1078547491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258633529/10000000000 : ℝ)|^4177 ≤ (8535928698423/20000000000000 : ℝ)^3153
        have hw : |(5258633529/10000000000 : ℝ)|=(5258633529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108011699/200000000 : ℝ)|^4177 ≤ (44212552131821/100000000000000 : ℝ)^3153
        have hw : |(108011699/200000000 : ℝ)|=(108011699/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655276923/5000000000 : ℝ)*x 0 + (-417453581/2000000000 : ℝ)*x 1 + (168768277/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655276923/5000000000 : ℝ)^4177 ≤ (10809695665721/25000000000000 : ℝ)^3153 := by
    have hnat : (2655276923 : ℕ)^4177*25000000000000^3153 ≤ 10809695665721^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655276923 5000000000 10809695665721 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417453581/2000000000 : ℝ)^4177 ≤ (3137166532881/25000000000000 : ℝ)^3153 := by
    have hnat : (417453581 : ℕ)^4177*25000000000000^3153 ≤ 3137166532881^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417453581 2000000000 3137166532881 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168768277/312500000 : ℝ)^4177 ≤ (44212551199117/100000000000000 : ℝ)^3153 := by
    have hnat : (168768277 : ℕ)^4177*100000000000000^3153 ≤ 44212551199117^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168768277 312500000 44212551199117 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655276923/5000000000 : ℝ), (-417453581/2000000000 : ℝ), (168768277/312500000 : ℝ)] ![(10809695665721/25000000000000 : ℝ), (3137166532881/25000000000000 : ℝ), (44212551199117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655276923/5000000000 : ℝ)|^4177 ≤ (10809695665721/25000000000000 : ℝ)^3153
        have hw : |(2655276923/5000000000 : ℝ)|=(2655276923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417453581/2000000000 : ℝ)|^4177 ≤ (3137166532881/25000000000000 : ℝ)^3153
        have hw : |(-417453581/2000000000 : ℝ)|=(417453581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168768277/312500000 : ℝ)|^4177 ≤ (44212551199117/100000000000000 : ℝ)^3153
        have hw : |(168768277/312500000 : ℝ)|=(168768277/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663819203/1250000000 : ℝ)*x 0 + (5400584869/10000000000 : ℝ)*x 1 + (-1043634099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663819203/1250000000 : ℝ)^4177 ≤ (10809695067079/25000000000000 : ℝ)^3153 := by
    have hnat : (663819203 : ℕ)^4177*25000000000000^3153 ≤ 10809695067079^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663819203 1250000000 10809695067079 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400584869/10000000000 : ℝ)^4177 ≤ (1381642226667/3125000000000 : ℝ)^3153 := by
    have hnat : (5400584869 : ℕ)^4177*3125000000000^3153 ≤ 1381642226667^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400584869 10000000000 1381642226667 3125000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043634099/5000000000 : ℝ)^4177 ≤ (1254866846513/10000000000000 : ℝ)^3153 := by
    have hnat : (1043634099 : ℕ)^4177*10000000000000^3153 ≤ 1254866846513^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043634099 5000000000 1254866846513 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663819203/1250000000 : ℝ), (5400584869/10000000000 : ℝ), (-1043634099/5000000000 : ℝ)] ![(10809695067079/25000000000000 : ℝ), (1381642226667/3125000000000 : ℝ), (1254866846513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663819203/1250000000 : ℝ)|^4177 ≤ (10809695067079/25000000000000 : ℝ)^3153
        have hw : |(663819203/1250000000 : ℝ)|=(663819203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400584869/10000000000 : ℝ)|^4177 ≤ (1381642226667/3125000000000 : ℝ)^3153
        have hw : |(5400584869/10000000000 : ℝ)|=(5400584869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043634099/5000000000 : ℝ)|^4177 ≤ (1254866846513/10000000000000 : ℝ)^3153
        have hw : |(-1043634099/5000000000 : ℝ)|=(1043634099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s4_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361582321/10000000000 : ℝ)*x 0 + (901121499/2000000000 : ℝ)*x 1 + (2111073313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361582321/10000000000 : ℝ)^4177 ≤ (33312809243159/100000000000000 : ℝ)^3153 := by
    have hnat : (4361582321 : ℕ)^4177*100000000000000^3153 ≤ 33312809243159^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361582321 10000000000 33312809243159 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901121499/2000000000 : ℝ)^4177 ≤ (34777856566093/100000000000000 : ℝ)^3153 := by
    have hnat : (901121499 : ℕ)^4177*100000000000000^3153 ≤ 34777856566093^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901121499 2000000000 34777856566093 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111073313/5000000000 : ℝ)^4177 ≤ (7977333544929/25000000000000 : ℝ)^3153 := by
    have hnat : (2111073313 : ℕ)^4177*25000000000000^3153 ≤ 7977333544929^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111073313 5000000000 7977333544929 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361582321/10000000000 : ℝ), (901121499/2000000000 : ℝ), (2111073313/5000000000 : ℝ)] ![(33312809243159/100000000000000 : ℝ), (34777856566093/100000000000000 : ℝ), (7977333544929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361582321/10000000000 : ℝ)|^4177 ≤ (33312809243159/100000000000000 : ℝ)^3153
        have hw : |(4361582321/10000000000 : ℝ)|=(4361582321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901121499/2000000000 : ℝ)|^4177 ≤ (34777856566093/100000000000000 : ℝ)^3153
        have hw : |(901121499/2000000000 : ℝ)|=(901121499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111073313/5000000000 : ℝ)|^4177 ≤ (7977333544929/25000000000000 : ℝ)^3153
        have hw : |(2111073313/5000000000 : ℝ)|=(2111073313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10691/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10691/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10691/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10691/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10691/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10691/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10691/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (5479125742990561/50000000000000000000 : ℝ) := by
    have hpowers : (10691/100000 : ℝ)^8353 ≤ (5479125742990561/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10691 : ℕ)^8353*50000000000000000000^2048 ≤ 5479125742990561^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10691 100000 5479125742990561 50000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10691/100000 : ℝ)) (X := (5479125742990561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14783/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (8218879539469507/20000000000000000000 : ℝ) := by
    have hpowers : (14783/100000 : ℝ)^8353 ≤ (8218879539469507/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14783 : ℕ)^8353*20000000000000000000^2048 ≤ 8218879539469507^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14783 100000 8218879539469507 20000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14783/100000 : ℝ)) (X := (8218879539469507/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005479125742990561/25000000000000000000 : ℝ) ≤ (1000053730738541/1000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25005479125742990561/25000000000000000000 : ℝ)^2048 ≤ (1000053730738541/1000000000000000 : ℝ)^8353 := by
      have hnat : (25005479125742990561 : ℕ)^2048*1000000000000000^8353 ≤ 1000053730738541^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005479125742990561 25000000000000000000 1000053730738541 1000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053730738541/1000000000000000 : ℝ)) (X := (25005479125742990561/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052052649183328657/100000000000000000000 : ℝ) ≤ (10001275983352273/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (100052052649183328657/100000000000000000000 : ℝ)^2048 ≤ (10001275983352273/10000000000000000 : ℝ)^8353 := by
      have hnat : (100052052649183328657 : ℕ)^2048*10000000000000000^8353 ≤ 10001275983352273^8353*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052052649183328657 100000000000000000000 10001275983352273 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001275983352273/10000000000000000 : ℝ)) (X := (100052052649183328657/100000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008218879539469507/10000000000000000000 : ℝ) ≤ (312562958103723/312500000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (10008218879539469507/10000000000000000000 : ℝ)^2048 ≤ (312562958103723/312500000000000 : ℝ)^8353 := by
      have hnat : (10008218879539469507 : ℕ)^2048*312500000000000^8353 ≤ 312562958103723^8353*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008218879539469507 10000000000000000000 312562958103723 312500000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312562958103723/312500000000000 : ℝ)) (X := (10008218879539469507/10000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5479125742990561/50000000000000000000 : ℝ) ≤ ((20453202146148816527/20460000000000000000 : ℝ)+2*(738675966863/409200000000000 : ℝ)*(10691/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (20453202146148816527/20460000000000000000 : ℝ)+2*(738675966863/409200000000000 : ℝ)*(10691/100000 : ℝ)=(1000053730738541/1000000000000000 : ℝ) by norm_num, show 1+2*(5479125742990561/50000000000000000000 : ℝ)=(25005479125742990561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8218879539469507/20000000000000000000 : ℝ)+(5479125742990561/50000000000000000000 : ℝ) ≤ ((20453202146148816527/20460000000000000000 : ℝ)+(738675966863/409200000000000 : ℝ)*((14783/100000 : ℝ)+(10691/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (20453202146148816527/20460000000000000000 : ℝ)+(738675966863/409200000000000 : ℝ)*((14783/100000 : ℝ)+(10691/100000 : ℝ))=(10001275983352273/10000000000000000 : ℝ) by norm_num, show 1+(8218879539469507/20000000000000000000 : ℝ)+(5479125742990561/50000000000000000000 : ℝ)=(100052052649183328657/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8218879539469507/20000000000000000000 : ℝ) ≤ ((20453202146148816527/20460000000000000000 : ℝ)+2*(738675966863/409200000000000 : ℝ)*(14783/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (20453202146148816527/20460000000000000000 : ℝ)+2*(738675966863/409200000000000 : ℝ)*(14783/100000 : ℝ)=(312562958103723/312500000000000 : ℝ) by norm_num, show 1+2*(8218879539469507/20000000000000000000 : ℝ)=(10008218879539469507/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20453202146148816527/20460000000000000000 : ℝ)*(X 1 0+X 2 0)+(738675966863/409200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (10691/100000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (20453202146148816527/20460000000000000000 : ℝ)) (alpha := (738675966863/409200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20453202146148816527/20460000000000000000 : ℝ)*(X 0 1+X 2 1)+(738675966863/409200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (10691/100000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (20453202146148816527/20460000000000000000 : ℝ)) (alpha := (738675966863/409200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20453202146148816527/20460000000000000000 : ℝ)*(X 0 2+X 1 2)+(738675966863/409200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (10691/100000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (20453202146148816527/20460000000000000000 : ℝ)) (alpha := (738675966863/409200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-539271971/2500000000 : ℝ)*X 0 0+(2700495493/5000000000 : ℝ)*X 0 1+(5258229269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673385653/5000000000 : ℝ)*X 1 0+(-111481191/500000000 : ℝ)*X 1 1+(2629114719/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346771293/10000000000 : ℝ)*X 2 0+(2629114743/5000000000 : ℝ)*X 2 1+(-2229623773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361568767/10000000000 : ℝ)*X 0 0+(2110667769/5000000000 : ℝ)*X 0 1+(4506415009/10000000000 : ℝ)*X 0 2+(4361568767/10000000000 : ℝ)*X 1 0+(2110667769/5000000000 : ℝ)*X 1 1+(4506415009/10000000000 : ℝ)*X 1 2+(4361568767/10000000000 : ℝ)*X 2 0+(2110667769/5000000000 : ℝ)*X 2 1+(4506415009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1078547491/5000000000 : ℝ)*X 0 0+(5258633529/10000000000 : ℝ)*X 0 1+(108011699/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655276923/5000000000 : ℝ)*X 1 0+(-417453581/2000000000 : ℝ)*X 1 1+(168768277/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663819203/1250000000 : ℝ)*X 2 0+(5400584869/10000000000 : ℝ)*X 2 1+(-1043634099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361582321/10000000000 : ℝ)*X 0 0+(901121499/2000000000 : ℝ)*X 0 1+(2111073313/5000000000 : ℝ)*X 0 2+(4361582321/10000000000 : ℝ)*X 1 0+(901121499/2000000000 : ℝ)*X 1 1+(2111073313/5000000000 : ℝ)*X 1 2+(4361582321/10000000000 : ℝ)*X 2 0+(901121499/2000000000 : ℝ)*X 2 1+(2111073313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (621507181473873255290823477/85250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1390888447/100000000000000 : ℝ)*(base19) + (119876603/10000000000000 : ℝ)*(base23) + (46808639/50000000000000 : ℝ)*(lower2) + (218935899/100000000000000 : ℝ)*(upper3) + (9474951/6250000000000 : ℝ)*(upper5) + (1314073758322617/25000000000000 : ℝ)*(major0) + (1314073758322617/25000000000000 : ℝ)*(major1) + (1314073758322617/25000000000000 : ℝ)*(major2) + (7004718726100127/100000000000000 : ℝ)*(sp0) + (3502378300538531/50000000000000 : ℝ)*(sp1) + (7004756793199479/100000000000000 : ℝ)*(sp2) + (876952937526847/25000000000000 : ℝ)*(sp3) + (19632932691/50000000000000 : ℝ)*(sp4) + (5020373617/25000000000000 : ℝ)*(sp7) + (54809872368779/1562500000000 : ℝ)*(f.failure) + (7004757991965509/100000000000000 : ℝ)*(f.sum) + (2725325663597/1705000000000000000000000000 : ℝ)*base65 + (335879535621652947/170500000000000000000000000000000 : ℝ)*base68 + (4281339699261152947/170500000000000000000000000000000 : ℝ)*base70 + (1139700607807652947/170500000000000000000000000000000 : ℝ)*base72 + (6733441143537/1705000000000000000000000000 : ℝ)*base73 + (3794346191617652947/170500000000000000000000000000000 : ℝ)*base76 + (2528145768245152947/170500000000000000000000000000000 : ℝ)*base78 + (2537305544348652947/170500000000000000000000000000000 : ℝ)*base80 + (1567845233477/426250000000000000000000000 : ℝ)*base82 + (316781/39062500000000000000 : ℝ)*base89 + (316781/39062500000000000000 : ℝ)*base91 + (316781/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36845740434920064648072201/31000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247084597/20000000000000 : ℝ)*(base19) + (581276691/50000000000000 : ℝ)*(base23) + (16872017/10000000000000 : ℝ)*(upper2) + (146188659/100000000000000 : ℝ)*(upper5) + (5286243068661231/100000000000000 : ℝ)*(major0) + (5286243068661231/100000000000000 : ℝ)*(major1) + (5286243068661231/100000000000000 : ℝ)*(major2) + (1589274843/50000000000000 : ℝ)*(sp0) + (38838465537/100000000000000 : ℝ)*(sp1) + (24749439541/100000000000000 : ℝ)*(sp2) + (7044665019208607/100000000000000 : ℝ)*(sp4) + (7044628123869771/100000000000000 : ℝ)*(sp5) + (704464228576537/10000000000000 : ℝ)*(sp6) + (1763908949972541/50000000000000 : ℝ)*(sp7) + (1763908949972541/50000000000000 : ℝ)*(f.failure) + (7044668197758293/100000000000000 : ℝ)*(f.sum) + (24615478290229/6820000000000000000000000000 : ℝ)*base66 + (8371551337913128421/682000000000000000000000000000000 : ℝ)*base68 + (7028838895127128421/682000000000000000000000000000000 : ℝ)*base70 + (7634624299835128421/682000000000000000000000000000000 : ℝ)*base72 + (26025292806449/6820000000000000000000000000 : ℝ)*base74 + (13849521008339128421/682000000000000000000000000000000 : ℝ)*base76 + (11615067380845128421/682000000000000000000000000000000 : ℝ)*base78 + (11994320304587128421/682000000000000000000000000000000 : ℝ)*base80 + (19381135485329/6820000000000000000000000000 : ℝ)*base82 + (17084199/1250000000000000000000 : ℝ)*base89 + (17084199/1250000000000000000000 : ℝ)*base91 + (17084199/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1161_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_s5_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215768481/1000000000 : ℝ)*x 0 + (2697208479/5000000000 : ℝ)*x 1 + (164512853/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215768481/1000000000 : ℝ)^4177 ≤ (3278138186253/25000000000000 : ℝ)^3153 := by
    have hnat : (215768481 : ℕ)^4177*25000000000000^3153 ≤ 3278138186253^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215768481 1000000000 3278138186253 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697208479/5000000000 : ℝ)^4177 ≤ (44145670244913/100000000000000 : ℝ)^3153 := by
    have hnat : (2697208479 : ℕ)^4177*100000000000000^3153 ≤ 44145670244913^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697208479 5000000000 44145670244913 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164512853/312500000 : ℝ)^4177 ≤ (42741776998717/100000000000000 : ℝ)^3153 := by
    have hnat : (164512853 : ℕ)^4177*100000000000000^3153 ≤ 42741776998717^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164512853 312500000 42741776998717 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215768481/1000000000 : ℝ), (2697208479/5000000000 : ℝ), (164512853/312500000 : ℝ)] ![(3278138186253/25000000000000 : ℝ), (44145670244913/100000000000000 : ℝ), (42741776998717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215768481/1000000000 : ℝ)|^4177 ≤ (3278138186253/25000000000000 : ℝ)^3153
        have hw : |(-215768481/1000000000 : ℝ)|=(215768481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697208479/5000000000 : ℝ)|^4177 ≤ (44145670244913/100000000000000 : ℝ)^3153
        have hw : |(2697208479/5000000000 : ℝ)|=(2697208479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164512853/312500000 : ℝ)|^4177 ≤ (42741776998717/100000000000000 : ℝ)^3153
        have hw : |(164512853/312500000 : ℝ)|=(164512853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069023867/2000000000 : ℝ)*x 0 + (-2223646307/10000000000 : ℝ)*x 1 + (5264411013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069023867/2000000000 : ℝ)^4177 ≤ (21806005650807/50000000000000 : ℝ)^3153 := by
    have hnat : (1069023867 : ℕ)^4177*50000000000000^3153 ≤ 21806005650807^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069023867 2000000000 21806005650807 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223646307/10000000000 : ℝ)^4177 ≤ (6823107362923/50000000000000 : ℝ)^3153 := by
    have hnat : (2223646307 : ℕ)^4177*50000000000000^3153 ≤ 6823107362923^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223646307 10000000000 6823107362923 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264411013/10000000000 : ℝ)^4177 ≤ (21370886977411/50000000000000 : ℝ)^3153 := by
    have hnat : (5264411013 : ℕ)^4177*50000000000000^3153 ≤ 21370886977411^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264411013 10000000000 21370886977411 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069023867/2000000000 : ℝ), (-2223646307/10000000000 : ℝ), (5264411013/10000000000 : ℝ)] ![(21806005650807/50000000000000 : ℝ), (6823107362923/50000000000000 : ℝ), (21370886977411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069023867/2000000000 : ℝ)|^4177 ≤ (21806005650807/50000000000000 : ℝ)^3153
        have hw : |(1069023867/2000000000 : ℝ)|=(1069023867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2223646307/10000000000 : ℝ)|^4177 ≤ (6823107362923/50000000000000 : ℝ)^3153
        have hw : |(-2223646307/10000000000 : ℝ)|=(2223646307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264411013/10000000000 : ℝ)|^4177 ≤ (21370886977411/50000000000000 : ℝ)^3153
        have hw : |(5264411013/10000000000 : ℝ)|=(5264411013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345118957/10000000000 : ℝ)*x 0 + (2632205573/5000000000 : ℝ)*x 1 + (-1111823317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345118957/10000000000 : ℝ)^4177 ≤ (21806003607889/50000000000000 : ℝ)^3153 := by
    have hnat : (5345118957 : ℕ)^4177*50000000000000^3153 ≤ 21806003607889^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345118957 10000000000 21806003607889 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632205573/5000000000 : ℝ)^4177 ≤ (8548355077069/20000000000000 : ℝ)^3153 := by
    have hnat : (2632205573 : ℕ)^4177*20000000000000^3153 ≤ 8548355077069^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632205573 5000000000 8548355077069 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111823317/5000000000 : ℝ)^4177 ≤ (6823108692167/50000000000000 : ℝ)^3153 := by
    have hnat : (1111823317 : ℕ)^4177*50000000000000^3153 ≤ 6823108692167^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111823317 5000000000 6823108692167 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345118957/10000000000 : ℝ), (2632205573/5000000000 : ℝ), (-1111823317/5000000000 : ℝ)] ![(21806003607889/50000000000000 : ℝ), (8548355077069/20000000000000 : ℝ), (6823108692167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345118957/10000000000 : ℝ)|^4177 ≤ (21806003607889/50000000000000 : ℝ)^3153
        have hw : |(5345118957/10000000000 : ℝ)|=(5345118957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632205573/5000000000 : ℝ)|^4177 ≤ (8548355077069/20000000000000 : ℝ)^3153
        have hw : |(2632205573/5000000000 : ℝ)|=(2632205573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111823317/5000000000 : ℝ)|^4177 ≤ (6823108692167/50000000000000 : ℝ)^3153
        have hw : |(-1111823317/5000000000 : ℝ)|=(1111823317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361916369/10000000000 : ℝ)*x 0 + (846805341/2000000000 : ℝ)*x 1 + (449363447/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361916369/10000000000 : ℝ)^4177 ≤ (33316189284139/100000000000000 : ℝ)^3153 := by
    have hnat : (4361916369 : ℕ)^4177*100000000000000^3153 ≤ 33316189284139^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361916369 10000000000 33316189284139 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846805341/2000000000 : ℝ)^4177 ≤ (32028332964779/100000000000000 : ℝ)^3153 := by
    have hnat : (846805341 : ℕ)^4177*100000000000000^3153 ≤ 32028332964779^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846805341 2000000000 32028332964779 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449363447/1000000000 : ℝ)^4177 ≤ (8663869434313/25000000000000 : ℝ)^3153 := by
    have hnat : (449363447 : ℕ)^4177*25000000000000^3153 ≤ 8663869434313^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449363447 1000000000 8663869434313 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361916369/10000000000 : ℝ), (846805341/2000000000 : ℝ), (449363447/1000000000 : ℝ)] ![(33316189284139/100000000000000 : ℝ), (32028332964779/100000000000000 : ℝ), (8663869434313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361916369/10000000000 : ℝ)|^4177 ≤ (33316189284139/100000000000000 : ℝ)^3153
        have hw : |(4361916369/10000000000 : ℝ)|=(4361916369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846805341/2000000000 : ℝ)|^4177 ≤ (32028332964779/100000000000000 : ℝ)^3153
        have hw : |(846805341/2000000000 : ℝ)|=(846805341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449363447/1000000000 : ℝ)|^4177 ≤ (8663869434313/25000000000000 : ℝ)^3153
        have hw : |(449363447/1000000000 : ℝ)|=(449363447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157689793/10000000000 : ℝ)*x 0 + (2632373531/5000000000 : ℝ)*x 1 + (1078816027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157689793/10000000000 : ℝ)^4177 ≤ (13112592862229/100000000000000 : ℝ)^3153 := by
    have hnat : (2157689793 : ℕ)^4177*100000000000000^3153 ≤ 13112592862229^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157689793 10000000000 13112592862229 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632373531/5000000000 : ℝ)^4177 ≤ (42745388472621/100000000000000 : ℝ)^3153 := by
    have hnat : (2632373531 : ℕ)^4177*100000000000000^3153 ≤ 42745388472621^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632373531 5000000000 42745388472621 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078816027/2000000000 : ℝ)^4177 ≤ (44142018659667/100000000000000 : ℝ)^3153 := by
    have hnat : (1078816027 : ℕ)^4177*100000000000000^3153 ≤ 44142018659667^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078816027 2000000000 44142018659667 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157689793/10000000000 : ℝ), (2632373531/5000000000 : ℝ), (1078816027/2000000000 : ℝ)] ![(13112592862229/100000000000000 : ℝ), (42745388472621/100000000000000 : ℝ), (44142018659667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157689793/10000000000 : ℝ)|^4177 ≤ (13112592862229/100000000000000 : ℝ)^3153
        have hw : |(-2157689793/10000000000 : ℝ)|=(2157689793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632373531/5000000000 : ℝ)|^4177 ≤ (42745388472621/100000000000000 : ℝ)^3153
        have hw : |(2632373531/5000000000 : ℝ)|=(2632373531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078816027/2000000000 : ℝ)|^4177 ≤ (44142018659667/100000000000000 : ℝ)^3153
        have hw : |(1078816027/2000000000 : ℝ)|=(1078816027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312136529/10000000000 : ℝ)*x 0 + (-2093976223/10000000000 : ℝ)*x 1 + (337130031/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312136529/10000000000 : ℝ)^4177 ≤ (43255854847539/100000000000000 : ℝ)^3153 := by
    have hnat : (5312136529 : ℕ)^4177*100000000000000^3153 ≤ 43255854847539^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312136529 10000000000 43255854847539 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093976223/10000000000 : ℝ)^4177 ≤ (12602122561073/100000000000000 : ℝ)^3153 := by
    have hnat : (2093976223 : ℕ)^4177*100000000000000^3153 ≤ 12602122561073^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093976223 10000000000 12602122561073 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337130031/625000000 : ℝ)^4177 ≤ (22071011286661/50000000000000 : ℝ)^3153 := by
    have hnat : (337130031 : ℕ)^4177*50000000000000^3153 ≤ 22071011286661^3153*625000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337130031 625000000 22071011286661 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312136529/10000000000 : ℝ), (-2093976223/10000000000 : ℝ), (337130031/625000000 : ℝ)] ![(43255854847539/100000000000000 : ℝ), (12602122561073/100000000000000 : ℝ), (22071011286661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312136529/10000000000 : ℝ)|^4177 ≤ (43255854847539/100000000000000 : ℝ)^3153
        have hw : |(5312136529/10000000000 : ℝ)|=(5312136529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093976223/10000000000 : ℝ)|^4177 ≤ (12602122561073/100000000000000 : ℝ)^3153
        have hw : |(-2093976223/10000000000 : ℝ)|=(2093976223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337130031/625000000 : ℝ)|^4177 ≤ (22071011286661/50000000000000 : ℝ)^3153
        have hw : |(337130031/625000000 : ℝ)|=(337130031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664017003/1250000000 : ℝ)*x 0 + (674260107/1250000000 : ℝ)*x 1 + (-2093976417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664017003/1250000000 : ℝ)^4177 ≤ (43255849399909/100000000000000 : ℝ)^3153 := by
    have hnat : (664017003 : ℕ)^4177*100000000000000^3153 ≤ 43255849399909^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664017003 1250000000 43255849399909 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674260107/1250000000 : ℝ)^4177 ≤ (8828405295227/20000000000000 : ℝ)^3153 := by
    have hnat : (674260107 : ℕ)^4177*20000000000000^3153 ≤ 8828405295227^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674260107 1250000000 8828405295227 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093976417/10000000000 : ℝ)^4177 ≤ (12602124107801/100000000000000 : ℝ)^3153 := by
    have hnat : (2093976417 : ℕ)^4177*100000000000000^3153 ≤ 12602124107801^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093976417 10000000000 12602124107801 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664017003/1250000000 : ℝ), (674260107/1250000000 : ℝ), (-2093976417/10000000000 : ℝ)] ![(43255849399909/100000000000000 : ℝ), (8828405295227/20000000000000 : ℝ), (12602124107801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664017003/1250000000 : ℝ)|^4177 ≤ (43255849399909/100000000000000 : ℝ)^3153
        have hw : |(664017003/1250000000 : ℝ)|=(664017003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674260107/1250000000 : ℝ)|^4177 ≤ (8828405295227/20000000000000 : ℝ)^3153
        have hw : |(674260107/1250000000 : ℝ)|=(674260107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093976417/10000000000 : ℝ)|^4177 ≤ (12602124107801/100000000000000 : ℝ)^3153
        have hw : |(-2093976417/10000000000 : ℝ)|=(2093976417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s5_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872385557/2000000000 : ℝ)*x 0 + (2246482003/5000000000 : ℝ)*x 1 + (1058674673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872385557/2000000000 : ℝ)^4177 ≤ (3331630479761/10000000000000 : ℝ)^3153 := by
    have hnat : (872385557 : ℕ)^4177*10000000000000^3153 ≤ 3331630479761^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872385557 2000000000 3331630479761 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246482003/5000000000 : ℝ)^4177 ≤ (6929725582081/20000000000000 : ℝ)^3153 := by
    have hnat : (2246482003 : ℕ)^4177*20000000000000^3153 ≤ 6929725582081^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246482003 5000000000 6929725582081 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058674673/2500000000 : ℝ)^4177 ≤ (32035067277969/100000000000000 : ℝ)^3153 := by
    have hnat : (1058674673 : ℕ)^4177*100000000000000^3153 ≤ 32035067277969^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058674673 2500000000 32035067277969 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872385557/2000000000 : ℝ), (2246482003/5000000000 : ℝ), (1058674673/2500000000 : ℝ)] ![(3331630479761/10000000000000 : ℝ), (6929725582081/20000000000000 : ℝ), (32035067277969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872385557/2000000000 : ℝ)|^4177 ≤ (3331630479761/10000000000000 : ℝ)^3153
        have hw : |(872385557/2000000000 : ℝ)|=(872385557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246482003/5000000000 : ℝ)|^4177 ≤ (6929725582081/20000000000000 : ℝ)^3153
        have hw : |(2246482003/5000000000 : ℝ)|=(2246482003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058674673/2500000000 : ℝ)|^4177 ≤ (32035067277969/100000000000000 : ℝ)^3153
        have hw : |(1058674673/2500000000 : ℝ)|=(1058674673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (11211/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (13300465300023487/100000000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^8353 ≤ (13300465300023487/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11211 : ℕ)^8353*100000000000000000000^2048 ≤ 13300465300023487^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 13300465300023487 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (13300465300023487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8353/2048 : ℝ) ≤ (17608327397261859/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8353 ≤ (17608327397261859/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8353*50000000000000000000^2048 ≤ 17608327397261859^2048*50000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17608327397261859 50000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17608327397261859/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013300465300023487/50000000000000000000 : ℝ) ≤ (2500163034949609/2500000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50013300465300023487/50000000000000000000 : ℝ)^2048 ≤ (2500163034949609/2500000000000000 : ℝ)^8353 := by
      have hnat : (50013300465300023487 : ℕ)^2048*2500000000000000^8353 ≤ 2500163034949609^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013300465300023487 50000000000000000000 2500163034949609 2500000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500163034949609/2500000000000000 : ℝ)) (X := (50013300465300023487/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009703424018909441/20000000000000000000 : ℝ) ≤ (10001189331652471/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (20009703424018909441/20000000000000000000 : ℝ)^2048 ≤ (10001189331652471/10000000000000000 : ℝ)^8353 := by
      have hnat : (20009703424018909441 : ℕ)^2048*10000000000000000^8353 ≤ 10001189331652471^8353*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009703424018909441 20000000000000000000 10001189331652471 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001189331652471/10000000000000000 : ℝ)) (X := (20009703424018909441/20000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017608327397261859/25000000000000000000 : ℝ) ≤ (5000863261753253/5000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25017608327397261859/25000000000000000000 : ℝ)^2048 ≤ (5000863261753253/5000000000000000 : ℝ)^8353 := by
      have hnat : (25017608327397261859 : ℕ)^2048*5000000000000000^8353 ≤ 5000863261753253^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017608327397261859 25000000000000000000 5000863261753253 5000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000863261753253/5000000000000000 : ℝ)) (X := (25017608327397261859/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13300465300023487/100000000000000000000 : ℝ) ≤ ((15109963251429749629/15115000000000000000 : ℝ)+2*(107438370807/60460000000000 : ℝ)*(11211/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (15109963251429749629/15115000000000000000 : ℝ)+2*(107438370807/60460000000000 : ℝ)*(11211/100000 : ℝ)=(2500163034949609/2500000000000000 : ℝ) by norm_num, show 1+2*(13300465300023487/100000000000000000000 : ℝ)=(50013300465300023487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17608327397261859/50000000000000000000 : ℝ)+(13300465300023487/100000000000000000000 : ℝ) ≤ ((15109963251429749629/15115000000000000000 : ℝ)+(107438370807/60460000000000 : ℝ)*((7117/50000 : ℝ)+(11211/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (15109963251429749629/15115000000000000000 : ℝ)+(107438370807/60460000000000 : ℝ)*((7117/50000 : ℝ)+(11211/100000 : ℝ))=(10001189331652471/10000000000000000 : ℝ) by norm_num, show 1+(17608327397261859/50000000000000000000 : ℝ)+(13300465300023487/100000000000000000000 : ℝ)=(20009703424018909441/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17608327397261859/50000000000000000000 : ℝ) ≤ ((15109963251429749629/15115000000000000000 : ℝ)+2*(107438370807/60460000000000 : ℝ)*(7117/50000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (15109963251429749629/15115000000000000000 : ℝ)+2*(107438370807/60460000000000 : ℝ)*(7117/50000 : ℝ)=(5000863261753253/5000000000000000 : ℝ) by norm_num, show 1+2*(17608327397261859/50000000000000000000 : ℝ)=(25017608327397261859/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15109963251429749629/15115000000000000000 : ℝ)*(X 1 0+X 2 0)+(107438370807/60460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (15109963251429749629/15115000000000000000 : ℝ)) (alpha := (107438370807/60460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15109963251429749629/15115000000000000000 : ℝ)*(X 0 1+X 2 1)+(107438370807/60460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (15109963251429749629/15115000000000000000 : ℝ)) (alpha := (107438370807/60460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15109963251429749629/15115000000000000000 : ℝ)*(X 0 2+X 1 2)+(107438370807/60460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (15109963251429749629/15115000000000000000 : ℝ)) (alpha := (107438370807/60460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215768481/1000000000 : ℝ)*X 0 0+(2697208479/5000000000 : ℝ)*X 0 1+(164512853/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069023867/2000000000 : ℝ)*X 1 0+(-2223646307/10000000000 : ℝ)*X 1 1+(5264411013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345118957/10000000000 : ℝ)*X 2 0+(2632205573/5000000000 : ℝ)*X 2 1+(-1111823317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361916369/10000000000 : ℝ)*X 0 0+(846805341/2000000000 : ℝ)*X 0 1+(449363447/1000000000 : ℝ)*X 0 2+(4361916369/10000000000 : ℝ)*X 1 0+(846805341/2000000000 : ℝ)*X 1 1+(449363447/1000000000 : ℝ)*X 1 2+(4361916369/10000000000 : ℝ)*X 2 0+(846805341/2000000000 : ℝ)*X 2 1+(449363447/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157689793/10000000000 : ℝ)*X 0 0+(2632373531/5000000000 : ℝ)*X 0 1+(1078816027/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312136529/10000000000 : ℝ)*X 1 0+(-2093976223/10000000000 : ℝ)*X 1 1+(337130031/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664017003/1250000000 : ℝ)*X 2 0+(674260107/1250000000 : ℝ)*X 2 1+(-2093976417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872385557/2000000000 : ℝ)*X 0 0+(2246482003/5000000000 : ℝ)*X 0 1+(1058674673/2500000000 : ℝ)*X 0 2+(872385557/2000000000 : ℝ)*X 1 0+(2246482003/5000000000 : ℝ)*X 1 1+(1058674673/2500000000 : ℝ)*X 1 2+(872385557/2000000000 : ℝ)*X 2 0+(2246482003/5000000000 : ℝ)*X 2 1+(1058674673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (569474989003331557042966323/75575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188395199/50000000000000 : ℝ)*(base21) + (144238169/100000000000000 : ℝ)*(upper2) + (1603537/20000000000000 : ℝ)*(lower4) + (5639981/100000000000000 : ℝ)*(upper5) + (1154395205822829/20000000000000 : ℝ)*(major0) + (1154395205822829/20000000000000 : ℝ)*(major1) + (1154395205822829/20000000000000 : ℝ)*(major2) + (961497001350839/12500000000000 : ℝ)*(sp0) + (3845979611642691/50000000000000 : ℝ)*(sp1) + (769194766180277/10000000000000 : ℝ)*(sp2) + (481496360530491/12500000000000 : ℝ)*(sp3) + (16787521331/100000000000000 : ℝ)*(sp5) + (5594442709/20000000000000 : ℝ)*(sp6) + (982400663/20000000000000 : ℝ)*(sp7) + (1925987898123621/50000000000000 : ℝ)*(f.failure) + (961497001350839/12500000000000 : ℝ)*(f.sum) + (29856024127843/1511500000000000000000000000 : ℝ)*base66 + (2580549069366569559/302300000000000000000000000000000 : ℝ)*base68 + (479709676998369559/302300000000000000000000000000000 : ℝ)*base70 + (589572314568430441/302300000000000000000000000000000 : ℝ)*base71 + (4325066102487/1511500000000000000000000000 : ℝ)*base74 + (2308126906795369559/302300000000000000000000000000000 : ℝ)*base76 + (261249494003869559/302300000000000000000000000000000 : ℝ)*base78 + (1189076330307769559/302300000000000000000000000000000 : ℝ)*base80 + (569177287303/302300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7035681/1250000000000000000000 : ℝ)*base90 + (7035681/1250000000000000000000 : ℝ)*base92 + (7035681/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4059556165323569197095341349/377875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381852723/20000000000000 : ℝ)*(base19) + (537626731/25000000000000 : ℝ)*(base23) + (160003021/50000000000000 : ℝ)*(upper3) + (226645941/50000000000000 : ℝ)*(lower4) + (2900982075337591/50000000000000 : ℝ)*(major0) + (2900982075337591/50000000000000 : ℝ)*(major1) + (2900982075337591/50000000000000 : ℝ)*(major2) + (8083131857/12500000000000 : ℝ)*(sp1) + (84469801541/100000000000000 : ℝ)*(sp2) + (693897201/50000000000000 : ℝ)*(sp3) + (77319393268063/1000000000000 : ℝ)*(sp4) + (1932968188121957/25000000000000 : ℝ)*(sp5) + (1546370541299567/20000000000000 : ℝ)*(sp6) + (3871987228645679/100000000000000 : ℝ)*(sp7) + (3871988616440081/100000000000000 : ℝ)*(f.failure) + (77319393268063/1000000000000 : ℝ)*(f.sum) + (771427012109/604600000000000000000000000 : ℝ)*base66 + (4722132734283253739/755750000000000000000000000000000 : ℝ)*base67 + (7708242140245253739/755750000000000000000000000000000 : ℝ)*base69 + (6345981742547503739/755750000000000000000000000000000 : ℝ)*base71 + (181250964823/302300000000000000000000000 : ℝ)*base74 + (35788223085678253739/755750000000000000000000000000000 : ℝ)*base75 + (4365530550518753739/755750000000000000000000000000000 : ℝ)*base77 + (445168039943753739/755750000000000000000000000000000 : ℝ)*base79 + (13657500676637/3023000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9512259/2500000000000000000000 : ℝ)*base89 + (9512259/2500000000000000000000 : ℝ)*base91 + (9512259/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1161_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1161_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1161_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1161_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1161_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

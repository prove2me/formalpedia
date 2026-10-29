-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1545_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:44.545596+00:00
-- url     : https://prove2.me/submissions/2f237b83-1b05-4c17-9af2-d9b689bc769a

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
theorem support_rectangle_w1545_s0_0 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-66055461/400000000 : ℝ)*x 0 + (1471967201/2500000000 : ℝ)*x 1 + (4869181163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66055461/400000000 : ℝ)^4587 ≤ (49207333171/500000000000 : ℝ)^3563 := by
    have hnat : (66055461 : ℕ)^4587*500000000000^3563 ≤ 49207333171^3563*400000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66055461 400000000 49207333171 500000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1471967201/2500000000 : ℝ)^4587 ≤ (10112871414077/20000000000000 : ℝ)^3563 := by
    have hnat : (1471967201 : ℕ)^4587*20000000000000^3563 ≤ 10112871414077^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471967201 2500000000 10112871414077 20000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4869181163/10000000000 : ℝ)^4587 ≤ (9898544069909/25000000000000 : ℝ)^3563 := by
    have hnat : (4869181163 : ℕ)^4587*25000000000000^3563 ≤ 9898544069909^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869181163 10000000000 9898544069909 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66055461/400000000 : ℝ), (1471967201/2500000000 : ℝ), (4869181163/10000000000 : ℝ)] ![(49207333171/500000000000 : ℝ), (10112871414077/20000000000000 : ℝ), (9898544069909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66055461/400000000 : ℝ)|^4587 ≤ (49207333171/500000000000 : ℝ)^3563
        have hw : |(-66055461/400000000 : ℝ)|=(66055461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1471967201/2500000000 : ℝ)|^4587 ≤ (10112871414077/20000000000000 : ℝ)^3563
        have hw : |(1471967201/2500000000 : ℝ)|=(1471967201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4869181163/10000000000 : ℝ)|^4587 ≤ (9898544069909/25000000000000 : ℝ)^3563
        have hw : |(4869181163/10000000000 : ℝ)|=(4869181163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_1 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341927271/625000000 : ℝ)*x 0 + (-2220002557/10000000000 : ℝ)*x 1 + (2434590619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341927271/625000000 : ℝ)^4587 ≤ (23000687783567/50000000000000 : ℝ)^3563 := by
    have hnat : (341927271 : ℕ)^4587*50000000000000^3563 ≤ 23000687783567^3563*625000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341927271 625000000 23000687783567 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220002557/10000000000 : ℝ)^4587 ≤ (14404447356081/100000000000000 : ℝ)^3563 := by
    have hnat : (2220002557 : ℕ)^4587*100000000000000^3563 ≤ 14404447356081^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220002557 10000000000 14404447356081 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2434590619/5000000000 : ℝ)^4587 ≤ (39594177064781/100000000000000 : ℝ)^3563 := by
    have hnat : (2434590619 : ℕ)^4587*100000000000000^3563 ≤ 39594177064781^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434590619 5000000000 39594177064781 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341927271/625000000 : ℝ), (-2220002557/10000000000 : ℝ), (2434590619/5000000000 : ℝ)] ![(23000687783567/50000000000000 : ℝ), (14404447356081/100000000000000 : ℝ), (39594177064781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341927271/625000000 : ℝ)|^4587 ≤ (23000687783567/50000000000000 : ℝ)^3563
        have hw : |(341927271/625000000 : ℝ)|=(341927271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2220002557/10000000000 : ℝ)|^4587 ≤ (14404447356081/100000000000000 : ℝ)^3563
        have hw : |(-2220002557/10000000000 : ℝ)|=(2220002557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2434590619/5000000000 : ℝ)|^4587 ≤ (39594177064781/100000000000000 : ℝ)^3563
        have hw : |(2434590619/5000000000 : ℝ)|=(2434590619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_2 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170963633/312500000 : ℝ)*x 0 + (2434590599/5000000000 : ℝ)*x 1 + (-222000271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170963633/312500000 : ℝ)^4587 ≤ (4600137470113/10000000000000 : ℝ)^3563 := by
    have hnat : (170963633 : ℕ)^4587*10000000000000^3563 ≤ 4600137470113^3563*312500000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170963633 312500000 4600137470113 10000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434590599/5000000000 : ℝ)^4587 ≤ (39594176646037/100000000000000 : ℝ)^3563 := by
    have hnat : (2434590599 : ℕ)^4587*100000000000000^3563 ≤ 39594176646037^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434590599 5000000000 39594176646037 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222000271/1000000000 : ℝ)^4587 ≤ (1440444863413/10000000000000 : ℝ)^3563 := by
    have hnat : (222000271 : ℕ)^4587*10000000000000^3563 ≤ 1440444863413^3563*1000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222000271 1000000000 1440444863413 10000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170963633/312500000 : ℝ), (2434590599/5000000000 : ℝ), (-222000271/1000000000 : ℝ)] ![(4600137470113/10000000000000 : ℝ), (39594176646037/100000000000000 : ℝ), (1440444863413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170963633/312500000 : ℝ)|^4587 ≤ (4600137470113/10000000000000 : ℝ)^3563
        have hw : |(170963633/312500000 : ℝ)|=(170963633/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2434590599/5000000000 : ℝ)|^4587 ≤ (39594176646037/100000000000000 : ℝ)^3563
        have hw : |(2434590599/5000000000 : ℝ)|=(2434590599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222000271/1000000000 : ℝ)|^4587 ≤ (1440444863413/10000000000000 : ℝ)^3563
        have hw : |(-222000271/1000000000 : ℝ)|=(222000271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_3 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2068180123/5000000000 : ℝ)*x 0 + (1546004183/5000000000 : ℝ)*x 1 + (5455784221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068180123/5000000000 : ℝ)^4587 ≤ (32094834314367/100000000000000 : ℝ)^3563 := by
    have hnat : (2068180123 : ℕ)^4587*100000000000000^3563 ≤ 32094834314367^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068180123 5000000000 32094834314367 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546004183/5000000000 : ℝ)^4587 ≤ (22066665569217/100000000000000 : ℝ)^3563 := by
    have hnat : (1546004183 : ℕ)^4587*100000000000000^3563 ≤ 22066665569217^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546004183 5000000000 22066665569217 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455784221/10000000000 : ℝ)^4587 ≤ (916770001881/2000000000000 : ℝ)^3563 := by
    have hnat : (5455784221 : ℕ)^4587*2000000000000^3563 ≤ 916770001881^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455784221 10000000000 916770001881 2000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2068180123/5000000000 : ℝ), (1546004183/5000000000 : ℝ), (5455784221/10000000000 : ℝ)] ![(32094834314367/100000000000000 : ℝ), (22066665569217/100000000000000 : ℝ), (916770001881/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2068180123/5000000000 : ℝ)|^4587 ≤ (32094834314367/100000000000000 : ℝ)^3563
        have hw : |(2068180123/5000000000 : ℝ)|=(2068180123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1546004183/5000000000 : ℝ)|^4587 ≤ (22066665569217/100000000000000 : ℝ)^3563
        have hw : |(1546004183/5000000000 : ℝ)|=(1546004183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455784221/10000000000 : ℝ)|^4587 ≤ (916770001881/2000000000000 : ℝ)^3563
        have hw : |(5455784221/10000000000 : ℝ)|=(5455784221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_4 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16546359/100000000 : ℝ)*x 0 + (978998691/2000000000 : ℝ)*x 1 + (5861136417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16546359/100000000 : ℝ)^4587 ≤ (1973280753919/20000000000000 : ℝ)^3563 := by
    have hnat : (16546359 : ℕ)^4587*20000000000000^3563 ≤ 1973280753919^3563*100000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16546359 100000000 1973280753919 20000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978998691/2000000000 : ℝ)^4587 ≤ (9966150058353/25000000000000 : ℝ)^3563 := by
    have hnat : (978998691 : ℕ)^4587*25000000000000^3563 ≤ 9966150058353^3563*2000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978998691 2000000000 9966150058353 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5861136417/10000000000 : ℝ)^4587 ≤ (50268995983683/100000000000000 : ℝ)^3563 := by
    have hnat : (5861136417 : ℕ)^4587*100000000000000^3563 ≤ 50268995983683^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5861136417 10000000000 50268995983683 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16546359/100000000 : ℝ), (978998691/2000000000 : ℝ), (5861136417/10000000000 : ℝ)] ![(1973280753919/20000000000000 : ℝ), (9966150058353/25000000000000 : ℝ), (50268995983683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16546359/100000000 : ℝ)|^4587 ≤ (1973280753919/20000000000000 : ℝ)^3563
        have hw : |(-16546359/100000000 : ℝ)|=(16546359/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(978998691/2000000000 : ℝ)|^4587 ≤ (9966150058353/25000000000000 : ℝ)^3563
        have hw : |(978998691/2000000000 : ℝ)|=(978998691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5861136417/10000000000 : ℝ)|^4587 ≤ (50268995983683/100000000000000 : ℝ)^3563
        have hw : |(5861136417/10000000000 : ℝ)|=(5861136417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_5 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192403849/10000000000 : ℝ)*x 0 + (-307011921/2500000000 : ℝ)*x 1 + (5861136193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192403849/10000000000 : ℝ)^4587 ≤ (43009644689663/100000000000000 : ℝ)^3563 := by
    have hnat : (5192403849 : ℕ)^4587*100000000000000^3563 ≤ 43009644689663^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192403849 10000000000 43009644689663 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307011921/2500000000 : ℝ)^4587 ≤ (6721361785823/100000000000000 : ℝ)^3563 := by
    have hnat : (307011921 : ℕ)^4587*100000000000000^3563 ≤ 6721361785823^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307011921 2500000000 6721361785823 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5861136193/10000000000 : ℝ)^4587 ≤ (50268993510369/100000000000000 : ℝ)^3563 := by
    have hnat : (5861136193 : ℕ)^4587*100000000000000^3563 ≤ 50268993510369^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5861136193 10000000000 50268993510369 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192403849/10000000000 : ℝ), (-307011921/2500000000 : ℝ), (5861136193/10000000000 : ℝ)] ![(43009644689663/100000000000000 : ℝ), (6721361785823/100000000000000 : ℝ), (50268993510369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192403849/10000000000 : ℝ)|^4587 ≤ (43009644689663/100000000000000 : ℝ)^3563
        have hw : |(5192403849/10000000000 : ℝ)|=(5192403849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307011921/2500000000 : ℝ)|^4587 ≤ (6721361785823/100000000000000 : ℝ)^3563
        have hw : |(-307011921/2500000000 : ℝ)|=(307011921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5861136193/10000000000 : ℝ)|^4587 ≤ (50268993510369/100000000000000 : ℝ)^3563
        have hw : |(5861136193/10000000000 : ℝ)|=(5861136193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_6 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192402883/10000000000 : ℝ)*x 0 + (2930568813/5000000000 : ℝ)*x 1 + (-12280469/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192402883/10000000000 : ℝ)^4587 ≤ (5376204298559/12500000000000 : ℝ)^3563 := by
    have hnat : (5192402883 : ℕ)^4587*12500000000000^3563 ≤ 5376204298559^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192402883 10000000000 5376204298559 12500000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2930568813/5000000000 : ℝ)^4587 ≤ (12567252333239/25000000000000 : ℝ)^3563 := by
    have hnat : (2930568813 : ℕ)^4587*25000000000000^3563 ≤ 12567252333239^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930568813 5000000000 12567252333239 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12280469/100000000 : ℝ)^4587 ≤ (6721356261603/100000000000000 : ℝ)^3563 := by
    have hnat : (12280469 : ℕ)^4587*100000000000000^3563 ≤ 6721356261603^3563*100000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12280469 100000000 6721356261603 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192402883/10000000000 : ℝ), (2930568813/5000000000 : ℝ), (-12280469/100000000 : ℝ)] ![(5376204298559/12500000000000 : ℝ), (12567252333239/25000000000000 : ℝ), (6721356261603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192402883/10000000000 : ℝ)|^4587 ≤ (5376204298559/12500000000000 : ℝ)^3563
        have hw : |(5192402883/10000000000 : ℝ)|=(5192402883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2930568813/5000000000 : ℝ)|^4587 ≤ (12567252333239/25000000000000 : ℝ)^3563
        have hw : |(2930568813/5000000000 : ℝ)|=(2930568813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12280469/100000000 : ℝ)|^4587 ≤ (6721356261603/100000000000000 : ℝ)^3563
        have hw : |(-12280469/100000000 : ℝ)|=(12280469/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s0_7 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20719487/50000000 : ℝ)*x 0 + (5395887663/10000000000 : ℝ)*x 1 + (3154036711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20719487/50000000 : ℝ)^4587 ≤ (16085071992021/50000000000000 : ℝ)^3563 := by
    have hnat : (20719487 : ℕ)^4587*50000000000000^3563 ≤ 16085071992021^3563*50000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20719487 50000000 16085071992021 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395887663/10000000000 : ℝ)^4587 ≤ (4519165466759/10000000000000 : ℝ)^3563 := by
    have hnat : (5395887663 : ℕ)^4587*10000000000000^3563 ≤ 4519165466759^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395887663 10000000000 4519165466759 10000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154036711/10000000000 : ℝ)^4587 ≤ (5659550335417/25000000000000 : ℝ)^3563 := by
    have hnat : (3154036711 : ℕ)^4587*25000000000000^3563 ≤ 5659550335417^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154036711 10000000000 5659550335417 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20719487/50000000 : ℝ), (5395887663/10000000000 : ℝ), (3154036711/10000000000 : ℝ)] ![(16085071992021/50000000000000 : ℝ), (4519165466759/10000000000000 : ℝ), (5659550335417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20719487/50000000 : ℝ)|^4587 ≤ (16085071992021/50000000000000 : ℝ)^3563
        have hw : |(20719487/50000000 : ℝ)|=(20719487/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395887663/10000000000 : ℝ)|^4587 ≤ (4519165466759/10000000000000 : ℝ)^3563
        have hw : |(5395887663/10000000000 : ℝ)|=(5395887663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154036711/10000000000 : ℝ)|^4587 ≤ (5659550335417/25000000000000 : ℝ)^3563
        have hw : |(3154036711/10000000000 : ℝ)|=(3154036711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1545_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3133/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4585/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4585 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4585*1^1024 ≤ 0^1024*1^4585 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4585 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4585/1024 : ℝ) ≤ (330550685622000133/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4585 ≤ (330550685622000133/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4585*20000000000000000000^1024 ≤ 330550685622000133^1024*5^4585 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 330550685622000133 20000000000000000000 4585 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (330550685622000133/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4585 := by
      have hnat : (1 : ℕ)^1024*1^4585 ≤ 1^4585*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20330550685622000133/20000000000000000000 : ℝ) ≤ (10036677478761859/10000000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (20330550685622000133/20000000000000000000 : ℝ)^1024 ≤ (10036677478761859/10000000000000000 : ℝ)^4585 := by
      have hnat : (20330550685622000133 : ℕ)^1024*10000000000000000^4585 ≤ 10036677478761859^4585*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20330550685622000133 20000000000000000000 10036677478761859 10000000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10036677478761859/10000000000000000 : ℝ)) (X := (20330550685622000133/20000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10330550685622000133/10000000000000000000 : ℝ) ≤ (5036677478761859/5000000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (10330550685622000133/10000000000000000000 : ℝ)^1024 ≤ (5036677478761859/5000000000000000 : ℝ)^4585 := by
      have hnat : (10330550685622000133 : ℕ)^1024*5000000000000000^4585 ≤ 5036677478761859^4585*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10330550685622000133 10000000000000000000 5036677478761859 5000000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036677478761859/5000000000000000 : ℝ)) (X := (10330550685622000133/10000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(36677478761859/4000000000000000 : ℝ)*(0 : ℝ))^(4585/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36677478761859/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(330550685622000133/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(36677478761859/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4585/1024 : ℝ) := by
    rw [show (1 : ℝ)+(36677478761859/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10036677478761859/10000000000000000 : ℝ) by norm_num, show 1+(330550685622000133/20000000000000000000 : ℝ)+(0 : ℝ)=(20330550685622000133/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(330550685622000133/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(36677478761859/4000000000000000 : ℝ)*(2/5 : ℝ))^(4585/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36677478761859/4000000000000000 : ℝ)*(2/5 : ℝ)=(5036677478761859/5000000000000000 : ℝ) by norm_num, show 1+2*(330550685622000133/20000000000000000000 : ℝ)=(10330550685622000133/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(36677478761859/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36677478761859/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(36677478761859/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36677478761859/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(36677478761859/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36677478761859/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66055461/400000000 : ℝ)*X 0 0+(1471967201/2500000000 : ℝ)*X 0 1+(4869181163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((341927271/625000000 : ℝ)*X 1 0+(-2220002557/10000000000 : ℝ)*X 1 1+(2434590619/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((170963633/312500000 : ℝ)*X 2 0+(2434590599/5000000000 : ℝ)*X 2 1+(-222000271/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2068180123/5000000000 : ℝ)*X 0 0+(1546004183/5000000000 : ℝ)*X 0 1+(5455784221/10000000000 : ℝ)*X 0 2+(2068180123/5000000000 : ℝ)*X 1 0+(1546004183/5000000000 : ℝ)*X 1 1+(5455784221/10000000000 : ℝ)*X 1 2+(2068180123/5000000000 : ℝ)*X 2 0+(1546004183/5000000000 : ℝ)*X 2 1+(5455784221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16546359/100000000 : ℝ)*X 0 0+(978998691/2000000000 : ℝ)*X 0 1+(5861136417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5192403849/10000000000 : ℝ)*X 1 0+(-307011921/2500000000 : ℝ)*X 1 1+(5861136193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192402883/10000000000 : ℝ)*X 2 0+(2930568813/5000000000 : ℝ)*X 2 1+(-12280469/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((20719487/50000000 : ℝ)*X 0 0+(5395887663/10000000000 : ℝ)*X 0 1+(3154036711/10000000000 : ℝ)*X 0 2+(20719487/50000000 : ℝ)*X 1 0+(5395887663/10000000000 : ℝ)*X 1 1+(3154036711/10000000000 : ℝ)*X 1 2+(20719487/50000000 : ℝ)*X 2 0+(5395887663/10000000000 : ℝ)*X 2 1+(3154036711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25931791890136608010203/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22020219/50000000000000 : ℝ)*(base1) + (58504917/12500000000000 : ℝ)*(base19) + (453684559/100000000000000 : ℝ)*(base23) + (20530003/25000000000000 : ℝ)*(upper3) + (6591357/20000000000000 : ℝ)*(upper5) + (140471171205139/20000000000000 : ℝ)*(major0) + (140471171205139/20000000000000 : ℝ)*(major1) + (140471171205139/20000000000000 : ℝ)*(major2) + (98165692840367/10000000000000 : ℝ)*(sp0) + (245414466851467/25000000000000 : ℝ)*(sp1) + (245414470440161/25000000000000 : ℝ)*(sp2) + (16922100679481/4000000000000 : ℝ)*(sp3) + (1451081971/100000000000000 : ℝ)*(sp4) + (182284853/25000000000000 : ℝ)*(sp7) + (676885264267/160000000000 : ℝ)*(f.failure) + (245414583861301/25000000000000 : ℝ)*(f.sum) + (57786634006599/40000000000000000000000000000 : ℝ)*base66 + (379372245286599/80000000000000000000000000000 : ℝ)*base68 + (165503212073401/80000000000000000000000000000 : ℝ)*base69 + (154509909846599/80000000000000000000000000000 : ℝ)*base72 + (147398215206599/40000000000000000000000000000 : ℝ)*base74 + (657888665286599/80000000000000000000000000000 : ℝ)*base76 + (122117047126599/80000000000000000000000000000 : ℝ)*base78 + (94582872553401/80000000000000000000000000000 : ℝ)*base79 + (18431030686599/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (13843/8000000000000000000 : ℝ)*base89 + (13843/8000000000000000000 : ℝ)*base91 + (13843/8000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294586967060379148212507/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (294789483/20000000000000 : ℝ)*(base19) + (170608963/10000000000000 : ℝ)*(base23) + (111541953/25000000000000 : ℝ)*(base39) + (173742939/100000000000000 : ℝ)*(upper3) + (441710857/100000000000000 : ℝ)*(upper5) + (185137574591761/25000000000000 : ℝ)*(major0) + (185137574591761/25000000000000 : ℝ)*(major1) + (11571091440613/1562500000000 : ℝ)*(major2) + (520586779/12500000000000 : ℝ)*(sp1) + (1955652491/50000000000000 : ℝ)*(sp2) + (258760206695471/25000000000000 : ℝ)*(sp4) + (1035035188140237/100000000000000 : ℝ)*(sp5) + (258758913888771/25000000000000 : ℝ)*(sp6) + (446059127393077/100000000000000 : ℝ)*(sp7) + (446059127393077/100000000000000 : ℝ)*(f.failure) + (16172519889839/1562500000000 : ℝ)*(f.sum) + (193440869883229/100000000000000000000000000000 : ℝ)*base66 + (21589878785817/6250000000000000000000000000 : ℝ)*base67 + (780852275056301/100000000000000000000000000000 : ℝ)*base70 + (7382669301683/6250000000000000000000000000 : ℝ)*base72 + (116984121783229/100000000000000000000000000000 : ℝ)*base74 + (248177007956301/100000000000000000000000000000 : ℝ)*base76 + (347923773956301/100000000000000000000000000000 : ℝ)*base78 + (372296855343699/100000000000000000000000000000 : ℝ)*base79 + (210665783906301/50000000000000000000000000000 : ℝ)*base82 + (34092333/5000000000000000000000 : ℝ)*base89 + (34092333/5000000000000000000000 : ℝ)*base91 + (34092333/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1545_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3133/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1545_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1545_s1_0 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1796390353/10000000000 : ℝ)*x 0 + (5549524087/10000000000 : ℝ)*x 1 + (5114184087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1796390353/10000000000 : ℝ)^4587 ≤ (10967730662077/100000000000000 : ℝ)^3563 := by
    have hnat : (1796390353 : ℕ)^4587*100000000000000^3563 ≤ 10967730662077^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796390353 10000000000 10967730662077 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5549524087/10000000000 : ℝ)^4587 ≤ (23427464582101/50000000000000 : ℝ)^3563 := by
    have hnat : (5549524087 : ℕ)^4587*50000000000000^3563 ≤ 23427464582101^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549524087 10000000000 23427464582101 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5114184087/10000000000 : ℝ)^4587 ≤ (21088670077913/50000000000000 : ℝ)^3563 := by
    have hnat : (5114184087 : ℕ)^4587*50000000000000^3563 ≤ 21088670077913^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114184087 10000000000 21088670077913 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1796390353/10000000000 : ℝ), (5549524087/10000000000 : ℝ), (5114184087/10000000000 : ℝ)] ![(10967730662077/100000000000000 : ℝ), (23427464582101/50000000000000 : ℝ), (21088670077913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1796390353/10000000000 : ℝ)|^4587 ≤ (10967730662077/100000000000000 : ℝ)^3563
        have hw : |(-1796390353/10000000000 : ℝ)|=(1796390353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5549524087/10000000000 : ℝ)|^4587 ≤ (23427464582101/50000000000000 : ℝ)^3563
        have hw : |(5549524087/10000000000 : ℝ)|=(5549524087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5114184087/10000000000 : ℝ)|^4587 ≤ (21088670077913/50000000000000 : ℝ)^3563
        have hw : |(5114184087/10000000000 : ℝ)|=(5114184087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_1 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345183737/2500000000 : ℝ)*x 0 + (-253090913/1250000000 : ℝ)*x 1 + (639272903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345183737/2500000000 : ℝ)^4587 ≤ (45028340707241/100000000000000 : ℝ)^3563 := by
    have hnat : (1345183737 : ℕ)^4587*100000000000000^3563 ≤ 45028340707241^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345183737 2500000000 45028340707241 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253090913/1250000000 : ℝ)^4587 ≤ (6397164142423/50000000000000 : ℝ)^3563 := by
    have hnat : (253090913 : ℕ)^4587*50000000000000^3563 ≤ 6397164142423^3563*1250000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253090913 1250000000 6397164142423 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639272903/1250000000 : ℝ)^4587 ≤ (42177330993061/100000000000000 : ℝ)^3563 := by
    have hnat : (639272903 : ℕ)^4587*100000000000000^3563 ≤ 42177330993061^3563*1250000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639272903 1250000000 42177330993061 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345183737/2500000000 : ℝ), (-253090913/1250000000 : ℝ), (639272903/1250000000 : ℝ)] ![(45028340707241/100000000000000 : ℝ), (6397164142423/50000000000000 : ℝ), (42177330993061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345183737/2500000000 : ℝ)|^4587 ≤ (45028340707241/100000000000000 : ℝ)^3563
        have hw : |(1345183737/2500000000 : ℝ)|=(1345183737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253090913/1250000000 : ℝ)|^4587 ≤ (6397164142423/50000000000000 : ℝ)^3563
        have hw : |(-253090913/1250000000 : ℝ)|=(253090913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639272903/1250000000 : ℝ)|^4587 ≤ (42177330993061/100000000000000 : ℝ)^3563
        have hw : |(639272903/1250000000 : ℝ)|=(639272903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_2 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345183601/2500000000 : ℝ)*x 0 + (5114183687/10000000000 : ℝ)*x 1 + (-101236371/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345183601/2500000000 : ℝ)^4587 ≤ (45028334846451/100000000000000 : ℝ)^3563 := by
    have hnat : (1345183601 : ℕ)^4587*100000000000000^3563 ≤ 45028334846451^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345183601 2500000000 45028334846451 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5114183687/10000000000 : ℝ)^4587 ≤ (4217733590889/10000000000000 : ℝ)^3563 := by
    have hnat : (5114183687 : ℕ)^4587*10000000000000^3563 ≤ 4217733590889^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114183687 10000000000 4217733590889 10000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101236371/500000000 : ℝ)^4587 ≤ (319858230713/2500000000000 : ℝ)^3563 := by
    have hnat : (101236371 : ℕ)^4587*2500000000000^3563 ≤ 319858230713^3563*500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101236371 500000000 319858230713 2500000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345183601/2500000000 : ℝ), (5114183687/10000000000 : ℝ), (-101236371/500000000 : ℝ)] ![(45028334846451/100000000000000 : ℝ), (4217733590889/10000000000000 : ℝ), (319858230713/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345183601/2500000000 : ℝ)|^4587 ≤ (45028334846451/100000000000000 : ℝ)^3563
        have hw : |(1345183601/2500000000 : ℝ)|=(1345183601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5114183687/10000000000 : ℝ)|^4587 ≤ (4217733590889/10000000000000 : ℝ)^3563
        have hw : |(5114183687/10000000000 : ℝ)|=(5114183687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101236371/500000000 : ℝ)|^4587 ≤ (319858230713/2500000000000 : ℝ)^3563
        have hw : |(-101236371/500000000 : ℝ)|=(101236371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_3 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237570119/10000000000 : ℝ)*x 0 + (3757234793/10000000000 : ℝ)*x 1 + (4767404439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237570119/10000000000 : ℝ)^4587 ≤ (33109371951631/100000000000000 : ℝ)^3563 := by
    have hnat : (4237570119 : ℕ)^4587*100000000000000^3563 ≤ 33109371951631^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237570119 10000000000 33109371951631 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3757234793/10000000000 : ℝ)^4587 ≤ (28358694540169/100000000000000 : ℝ)^3563 := by
    have hnat : (3757234793 : ℕ)^4587*100000000000000^3563 ≤ 28358694540169^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3757234793 10000000000 28358694540169 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4767404439/10000000000 : ℝ)^4587 ≤ (9632983376159/25000000000000 : ℝ)^3563 := by
    have hnat : (4767404439 : ℕ)^4587*25000000000000^3563 ≤ 9632983376159^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767404439 10000000000 9632983376159 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237570119/10000000000 : ℝ), (3757234793/10000000000 : ℝ), (4767404439/10000000000 : ℝ)] ![(33109371951631/100000000000000 : ℝ), (28358694540169/100000000000000 : ℝ), (9632983376159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237570119/10000000000 : ℝ)|^4587 ≤ (33109371951631/100000000000000 : ℝ)^3563
        have hw : |(4237570119/10000000000 : ℝ)|=(4237570119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3757234793/10000000000 : ℝ)|^4587 ≤ (28358694540169/100000000000000 : ℝ)^3563
        have hw : |(3757234793/10000000000 : ℝ)|=(3757234793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4767404439/10000000000 : ℝ)|^4587 ≤ (9632983376159/25000000000000 : ℝ)^3563
        have hw : |(4767404439/10000000000 : ℝ)|=(4767404439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_4 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179663699/1000000000 : ℝ)*x 0 + (319926989/625000000 : ℝ)*x 1 + (5544804679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179663699/1000000000 : ℝ)^4587 ≤ (1371208661983/12500000000000 : ℝ)^3563 := by
    have hnat : (179663699 : ℕ)^4587*12500000000000^3563 ≤ 1371208661983^3563*1000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179663699 1000000000 1371208661983 12500000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319926989/625000000 : ℝ)^4587 ≤ (42226693205479/100000000000000 : ℝ)^3563 := by
    have hnat : (319926989 : ℕ)^4587*100000000000000^3563 ≤ 42226693205479^3563*625000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319926989 625000000 42226693205479 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5544804679/10000000000 : ℝ)^4587 ≤ (11700909371747/25000000000000 : ℝ)^3563 := by
    have hnat : (5544804679 : ℕ)^4587*25000000000000^3563 ≤ 11700909371747^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544804679 10000000000 11700909371747 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179663699/1000000000 : ℝ), (319926989/625000000 : ℝ), (5544804679/10000000000 : ℝ)] ![(1371208661983/12500000000000 : ℝ), (42226693205479/100000000000000 : ℝ), (11700909371747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179663699/1000000000 : ℝ)|^4587 ≤ (1371208661983/12500000000000 : ℝ)^3563
        have hw : |(-179663699/1000000000 : ℝ)|=(179663699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319926989/625000000 : ℝ)|^4587 ≤ (42226693205479/100000000000000 : ℝ)^3563
        have hw : |(319926989/625000000 : ℝ)|=(319926989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5544804679/10000000000 : ℝ)|^4587 ≤ (11700909371747/25000000000000 : ℝ)^3563
        have hw : |(5544804679/10000000000 : ℝ)|=(5544804679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_5 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265635761/10000000000 : ℝ)*x 0 + (-19926343/125000000 : ℝ)*x 1 + (2772402263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265635761/10000000000 : ℝ)^4587 ≤ (21896074775669/50000000000000 : ℝ)^3563 := by
    have hnat : (5265635761 : ℕ)^4587*50000000000000^3563 ≤ 21896074775669^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265635761 10000000000 21896074775669 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19926343/125000000 : ℝ)^4587 ≤ (4702107304873/50000000000000 : ℝ)^3563 := by
    have hnat : (19926343 : ℕ)^4587*50000000000000^3563 ≤ 4702107304873^3563*125000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19926343 125000000 4702107304873 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2772402263/5000000000 : ℝ)^4587 ≤ (936072716487/2000000000000 : ℝ)^3563 := by
    have hnat : (2772402263 : ℕ)^4587*2000000000000^3563 ≤ 936072716487^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772402263 5000000000 936072716487 2000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265635761/10000000000 : ℝ), (-19926343/125000000 : ℝ), (2772402263/5000000000 : ℝ)] ![(21896074775669/50000000000000 : ℝ), (4702107304873/50000000000000 : ℝ), (936072716487/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265635761/10000000000 : ℝ)|^4587 ≤ (21896074775669/50000000000000 : ℝ)^3563
        have hw : |(5265635761/10000000000 : ℝ)|=(5265635761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19926343/125000000 : ℝ)|^4587 ≤ (4702107304873/50000000000000 : ℝ)^3563
        have hw : |(-19926343/125000000 : ℝ)|=(19926343/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2772402263/5000000000 : ℝ)|^4587 ≤ (936072716487/2000000000000 : ℝ)^3563
        have hw : |(2772402263/5000000000 : ℝ)|=(2772402263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_6 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632818391/5000000000 : ℝ)*x 0 + (1386201083/2500000000 : ℝ)*x 1 + (-797053139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632818391/5000000000 : ℝ)^4587 ≤ (43792160482947/100000000000000 : ℝ)^3563 := by
    have hnat : (2632818391 : ℕ)^4587*100000000000000^3563 ≤ 43792160482947^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632818391 5000000000 43792160482947 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1386201083/2500000000 : ℝ)^4587 ≤ (46803633716169/100000000000000 : ℝ)^3563 := by
    have hnat : (1386201083 : ℕ)^4587*100000000000000^3563 ≤ 46803633716169^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386201083 2500000000 46803633716169 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797053139/5000000000 : ℝ)^4587 ≤ (9404205784559/100000000000000 : ℝ)^3563 := by
    have hnat : (797053139 : ℕ)^4587*100000000000000^3563 ≤ 9404205784559^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797053139 5000000000 9404205784559 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632818391/5000000000 : ℝ), (1386201083/2500000000 : ℝ), (-797053139/5000000000 : ℝ)] ![(43792160482947/100000000000000 : ℝ), (46803633716169/100000000000000 : ℝ), (9404205784559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632818391/5000000000 : ℝ)|^4587 ≤ (43792160482947/100000000000000 : ℝ)^3563
        have hw : |(2632818391/5000000000 : ℝ)|=(2632818391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1386201083/2500000000 : ℝ)|^4587 ≤ (46803633716169/100000000000000 : ℝ)^3563
        have hw : |(1386201083/2500000000 : ℝ)|=(1386201083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-797053139/5000000000 : ℝ)|^4587 ≤ (9404205784559/100000000000000 : ℝ)^3563
        have hw : |(-797053139/5000000000 : ℝ)|=(797053139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s1_7 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119070381/5000000000 : ℝ)*x 0 + (148644311/312500000 : ℝ)*x 1 + (150727449/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119070381/5000000000 : ℝ)^4587 ≤ (33115112056949/100000000000000 : ℝ)^3563 := by
    have hnat : (2119070381 : ℕ)^4587*100000000000000^3563 ≤ 33115112056949^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119070381 5000000000 33115112056949 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148644311/312500000 : ℝ)^4587 ≤ (38419734126907/100000000000000 : ℝ)^3563 := by
    have hnat : (148644311 : ℕ)^4587*100000000000000^3563 ≤ 38419734126907^3563*312500000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148644311 312500000 38419734126907 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150727449/400000000 : ℝ)^4587 ≤ (7116288451551/25000000000000 : ℝ)^3563 := by
    have hnat : (150727449 : ℕ)^4587*25000000000000^3563 ≤ 7116288451551^3563*400000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150727449 400000000 7116288451551 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119070381/5000000000 : ℝ), (148644311/312500000 : ℝ), (150727449/400000000 : ℝ)] ![(33115112056949/100000000000000 : ℝ), (38419734126907/100000000000000 : ℝ), (7116288451551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119070381/5000000000 : ℝ)|^4587 ≤ (33115112056949/100000000000000 : ℝ)^3563
        have hw : |(2119070381/5000000000 : ℝ)|=(2119070381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148644311/312500000 : ℝ)|^4587 ≤ (38419734126907/100000000000000 : ℝ)^3563
        have hw : |(148644311/312500000 : ℝ)|=(148644311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150727449/400000000 : ℝ)|^4587 ≤ (7116288451551/25000000000000 : ℝ)^3563
        have hw : |(150727449/400000000 : ℝ)|=(150727449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1545_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3133/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8777/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2249/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3133/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3133/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3133/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3133/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3133/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3133/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3243/100000 : ℝ) ^ (4585/1024 : ℝ) ≤ (21513288265283/100000000000000000000 : ℝ) := by
    have hpowers : (3243/100000 : ℝ)^4585 ≤ (21513288265283/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3243 : ℕ)^4585*100000000000000000000^1024 ≤ 21513288265283^1024*100000^4585 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3243 100000 21513288265283 100000000000000000000 4585 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3243/100000 : ℝ)) (X := (21513288265283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3133/12500 : ℝ) ^ (4585/1024 : ℝ) ≤ (203809587616640361/100000000000000000000 : ℝ) := by
    have hpowers : (3133/12500 : ℝ)^4585 ≤ (203809587616640361/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3133 : ℕ)^4585*100000000000000000000^1024 ≤ 203809587616640361^1024*12500^4585 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3133 12500 203809587616640361 100000000000000000000 4585 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3133/12500 : ℝ)) (X := (203809587616640361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000021513288265283/50000000000000000000 : ℝ) ≤ (2500000240235589/2500000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (50000021513288265283/50000000000000000000 : ℝ)^1024 ≤ (2500000240235589/2500000000000000 : ℝ)^4585 := by
      have hnat : (50000021513288265283 : ℕ)^1024*2500000000000000^4585 ≤ 2500000240235589^4585*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000021513288265283 50000000000000000000 2500000240235589 2500000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000240235589/2500000000000000 : ℝ)) (X := (50000021513288265283/50000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25050957775226226411/25000000000000000000 : ℝ) ≤ (10004548703026239/10000000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (25050957775226226411/25000000000000000000 : ℝ)^1024 ≤ (10004548703026239/10000000000000000 : ℝ)^4585 := by
      have hnat : (25050957775226226411 : ℕ)^1024*10000000000000000^4585 ≤ 10004548703026239^4585*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25050957775226226411 25000000000000000000 10004548703026239 10000000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004548703026239/10000000000000000 : ℝ)) (X := (25050957775226226411/25000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50203809587616640361/50000000000000000000 : ℝ) ≤ (5004548222555061/5000000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (50203809587616640361/50000000000000000000 : ℝ)^1024 ≤ (5004548222555061/5000000000000000 : ℝ)^4585 := by
      have hnat : (50203809587616640361 : ℕ)^1024*5000000000000000^4585 ≤ 5004548222555061^4585*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50203809587616640361 50000000000000000000 5004548222555061 5000000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004548222555061/5000000000000000 : ℝ)) (X := (50203809587616640361/50000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21513288265283/100000000000000000000 : ℝ) ≤ ((109090262156783542569/109105000000000000000 : ℝ)+2*(4547742083883/2182100000000000 : ℝ)*(3243/100000 : ℝ))^(4585/1024 : ℝ) := by
    rw [show (109090262156783542569/109105000000000000000 : ℝ)+2*(4547742083883/2182100000000000 : ℝ)*(3243/100000 : ℝ)=(2500000240235589/2500000000000000 : ℝ) by norm_num, show 1+2*(21513288265283/100000000000000000000 : ℝ)=(50000021513288265283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(203809587616640361/100000000000000000000 : ℝ)+(21513288265283/100000000000000000000 : ℝ) ≤ ((109090262156783542569/109105000000000000000 : ℝ)+(4547742083883/2182100000000000 : ℝ)*((3133/12500 : ℝ)+(3243/100000 : ℝ)))^(4585/1024 : ℝ) := by
    rw [show (109090262156783542569/109105000000000000000 : ℝ)+(4547742083883/2182100000000000 : ℝ)*((3133/12500 : ℝ)+(3243/100000 : ℝ))=(10004548703026239/10000000000000000 : ℝ) by norm_num, show 1+(203809587616640361/100000000000000000000 : ℝ)+(21513288265283/100000000000000000000 : ℝ)=(25050957775226226411/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(203809587616640361/100000000000000000000 : ℝ) ≤ ((109090262156783542569/109105000000000000000 : ℝ)+2*(4547742083883/2182100000000000 : ℝ)*(3133/12500 : ℝ))^(4585/1024 : ℝ) := by
    rw [show (109090262156783542569/109105000000000000000 : ℝ)+2*(4547742083883/2182100000000000 : ℝ)*(3133/12500 : ℝ)=(5004548222555061/5000000000000000 : ℝ) by norm_num, show 1+2*(203809587616640361/100000000000000000000 : ℝ)=(50203809587616640361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (109090262156783542569/109105000000000000000 : ℝ)*(X 1 0+X 2 0)+(4547742083883/2182100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (3243/100000 : ℝ)) (hi := (3133/12500 : ℝ)) (c := (109090262156783542569/109105000000000000000 : ℝ)) (alpha := (4547742083883/2182100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (109090262156783542569/109105000000000000000 : ℝ)*(X 0 1+X 2 1)+(4547742083883/2182100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (3243/100000 : ℝ)) (hi := (3133/12500 : ℝ)) (c := (109090262156783542569/109105000000000000000 : ℝ)) (alpha := (4547742083883/2182100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (109090262156783542569/109105000000000000000 : ℝ)*(X 0 2+X 1 2)+(4547742083883/2182100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (3243/100000 : ℝ)) (hi := (3133/12500 : ℝ)) (c := (109090262156783542569/109105000000000000000 : ℝ)) (alpha := (4547742083883/2182100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1796390353/10000000000 : ℝ)*X 0 0+(5549524087/10000000000 : ℝ)*X 0 1+(5114184087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1345183737/2500000000 : ℝ)*X 1 0+(-253090913/1250000000 : ℝ)*X 1 1+(639272903/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1345183601/2500000000 : ℝ)*X 2 0+(5114183687/10000000000 : ℝ)*X 2 1+(-101236371/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4237570119/10000000000 : ℝ)*X 0 0+(3757234793/10000000000 : ℝ)*X 0 1+(4767404439/10000000000 : ℝ)*X 0 2+(4237570119/10000000000 : ℝ)*X 1 0+(3757234793/10000000000 : ℝ)*X 1 1+(4767404439/10000000000 : ℝ)*X 1 2+(4237570119/10000000000 : ℝ)*X 2 0+(3757234793/10000000000 : ℝ)*X 2 1+(4767404439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-179663699/1000000000 : ℝ)*X 0 0+(319926989/625000000 : ℝ)*X 0 1+(5544804679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265635761/10000000000 : ℝ)*X 1 0+(-19926343/125000000 : ℝ)*X 1 1+(2772402263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632818391/5000000000 : ℝ)*X 2 0+(1386201083/2500000000 : ℝ)*X 2 1+(-797053139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2119070381/5000000000 : ℝ)*X 0 0+(148644311/312500000 : ℝ)*X 0 1+(150727449/400000000 : ℝ)*X 0 2+(2119070381/5000000000 : ℝ)*X 1 0+(148644311/312500000 : ℝ)*X 1 1+(150727449/400000000 : ℝ)*X 1 2+(2119070381/5000000000 : ℝ)*X 2 0+(148644311/312500000 : ℝ)*X 2 1+(150727449/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28268269591796737882748670267/2727625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (292380761/100000000000000 : ℝ)*(base1) + (871814023/50000000000000 : ℝ)*(base19) + (1511391147/100000000000000 : ℝ)*(base23) + (45509339/20000000000000 : ℝ)*(upper3) + (2993699/2500000000000 : ℝ)*(upper5) + (821752610293081/50000000000000 : ℝ)*(major0) + (821752610293081/50000000000000 : ℝ)*(major1) + (821752610293081/50000000000000 : ℝ)*(major2) + (57426594324553/2500000000000 : ℝ)*(sp0) + (143566760004687/6250000000000 : ℝ)*(sp1) + (574267098077973/25000000000000 : ℝ)*(sp2) + (494968053669127/50000000000000 : ℝ)*(sp3) + (6423101679/100000000000000 : ℝ)*(sp4) + (1896146907/50000000000000 : ℝ)*(sp7) + (989940192012829/100000000000000 : ℝ)*(f.failure) + (2297069903703039/100000000000000 : ℝ)*(f.sum) + (53046596250487/54552500000000000000000000000 : ℝ)*base66 + (14674227381245684911/5455250000000000000000000000000000 : ℝ)*base68 + (23534234474663434911/5455250000000000000000000000000000 : ℝ)*base70 + (1799964129428315089/5455250000000000000000000000000000 : ℝ)*base71 + (7148425785383/13638125000000000000000000000 : ℝ)*base74 + (15988825768880184911/5455250000000000000000000000000000 : ℝ)*base76 + (9287229553280315089/5455250000000000000000000000000000 : ℝ)*base77 + (48874001743402684911/5455250000000000000000000000000000 : ℝ)*base80 + (151200677866817/54552500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (7510741/5000000000000000000000 : ℝ)*base89 + (7510741/5000000000000000000000 : ℝ)*base91 + (7510741/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131290649995936060691192619/17047656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1033702077/100000000000000 : ℝ)*(base19) + (162799829/10000000000000 : ℝ)*(base23) + (36501/781250000000 : ℝ)*(upper2) + (24489697/12500000000000 : ℝ)*(upper3) + (146294769/50000000000000 : ℝ)*(upper5) + (2624433312779/156250000000 : ℝ)*(major0) + (2624433312779/156250000000 : ℝ)*(major1) + (2624433312779/156250000000 : ℝ)*(major2) + (531090947/10000000000000 : ℝ)*(sp1) + (11269038879/100000000000000 : ℝ)*(sp2) + (2347570574965939/100000000000000 : ℝ)*(sp4) + (293445528794299/12500000000000 : ℝ)*(sp5) + (234755767792877/10000000000000 : ℝ)*(sp6) + (101170380867817/10000000000000 : ℝ)*(sp7) + (101170380867817/10000000000000 : ℝ)*(f.failure) + (2347570574965939/100000000000000 : ℝ)*(f.sum) + (36336012417583/10910500000000000000000000000 : ℝ)*base65 + (46431049386848249/17047656250000000000000000000000 : ℝ)*base68 + (668998490670247629/68190625000000000000000000000000 : ℝ)*base69 + (47087434171280563/8523828125000000000000000000000 : ℝ)*base71 + (3761407946649/1363812500000000000000000000 : ℝ)*base74 + (124148866393700377/34095312500000000000000000000000 : ℝ)*base75 + (31960394792619969/4261914062500000000000000000000 : ℝ)*base77 + (292425871953383621/68190625000000000000000000000000 : ℝ)*base80 + (53989789711743/10910500000000000000000000000 : ℝ)*base81 + (5318207/500000000000000000000 : ℝ)*base90 + (5318207/500000000000000000000 : ℝ)*base92 + (5318207/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1545_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3133/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8777/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2249/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1545_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1545_s2_0 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-908682247/5000000000 : ℝ)*x 0 + (5320382/9765625 : ℝ)*x 1 + (5202003981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908682247/5000000000 : ℝ)^4587 ≤ (11132865688637/100000000000000 : ℝ)^3563 := by
    have hnat : (908682247 : ℕ)^4587*100000000000000^3563 ≤ 11132865688637^3563*5000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908682247 5000000000 11132865688637 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5320382/9765625 : ℝ)^4587 ≤ (22877544465243/50000000000000 : ℝ)^3563 := by
    have hnat : (5320382 : ℕ)^4587*50000000000000^3563 ≤ 22877544465243^3563*9765625^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5320382 9765625 22877544465243 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202003981/10000000000 : ℝ)^4587 ≤ (43112045367729/100000000000000 : ℝ)^3563 := by
    have hnat : (5202003981 : ℕ)^4587*100000000000000^3563 ≤ 43112045367729^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202003981 10000000000 43112045367729 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-908682247/5000000000 : ℝ), (5320382/9765625 : ℝ), (5202003981/10000000000 : ℝ)] ![(11132865688637/100000000000000 : ℝ), (22877544465243/50000000000000 : ℝ), (43112045367729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-908682247/5000000000 : ℝ)|^4587 ≤ (11132865688637/100000000000000 : ℝ)^3563
        have hw : |(-908682247/5000000000 : ℝ)|=(908682247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5320382/9765625 : ℝ)|^4587 ≤ (22877544465243/50000000000000 : ℝ)^3563
        have hw : |(5320382/9765625 : ℝ)|=(5320382/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202003981/10000000000 : ℝ)|^4587 ≤ (43112045367729/100000000000000 : ℝ)^3563
        have hw : |(5202003981/10000000000 : ℝ)|=(5202003981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_1 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83667261/156250000 : ℝ)*x 0 + (-24297599/125000000 : ℝ)*x 1 + (5202003911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83667261/156250000 : ℝ)^4587 ≤ (44748098761467/100000000000000 : ℝ)^3563 := by
    have hnat : (83667261 : ℕ)^4587*100000000000000^3563 ≤ 44748098761467^3563*156250000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83667261 156250000 44748098761467 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24297599/125000000 : ℝ)^4587 ≤ (1213985661157/10000000000000 : ℝ)^3563 := by
    have hnat : (24297599 : ℕ)^4587*10000000000000^3563 ≤ 1213985661157^3563*125000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24297599 125000000 1213985661157 10000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202003911/10000000000 : ℝ)^4587 ≤ (4311204462087/10000000000000 : ℝ)^3563 := by
    have hnat : (5202003911 : ℕ)^4587*10000000000000^3563 ≤ 4311204462087^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202003911 10000000000 4311204462087 10000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83667261/156250000 : ℝ), (-24297599/125000000 : ℝ), (5202003911/10000000000 : ℝ)] ![(44748098761467/100000000000000 : ℝ), (1213985661157/10000000000000 : ℝ), (4311204462087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83667261/156250000 : ℝ)|^4587 ≤ (44748098761467/100000000000000 : ℝ)^3563
        have hw : |(83667261/156250000 : ℝ)|=(83667261/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24297599/125000000 : ℝ)|^4587 ≤ (1213985661157/10000000000000 : ℝ)^3563
        have hw : |(-24297599/125000000 : ℝ)|=(24297599/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202003911/10000000000 : ℝ)|^4587 ≤ (4311204462087/10000000000000 : ℝ)^3563
        have hw : |(5202003911/10000000000 : ℝ)|=(5202003911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_2 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107094093/200000000 : ℝ)*x 0 + (5202003973/10000000000 : ℝ)*x 1 + (-1943807909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107094093/200000000 : ℝ)^4587 ≤ (44748098180507/100000000000000 : ℝ)^3563 := by
    have hnat : (107094093 : ℕ)^4587*100000000000000^3563 ≤ 44748098180507^3563*200000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107094093 200000000 44748098180507 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202003973/10000000000 : ℝ)^4587 ≤ (21556022641187/50000000000000 : ℝ)^3563 := by
    have hnat : (5202003973 : ℕ)^4587*50000000000000^3563 ≤ 21556022641187^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202003973 10000000000 21556022641187 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943807909/10000000000 : ℝ)^4587 ≤ (6069928261563/50000000000000 : ℝ)^3563 := by
    have hnat : (1943807909 : ℕ)^4587*50000000000000^3563 ≤ 6069928261563^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943807909 10000000000 6069928261563 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107094093/200000000 : ℝ), (5202003973/10000000000 : ℝ), (-1943807909/10000000000 : ℝ)] ![(44748098180507/100000000000000 : ℝ), (21556022641187/50000000000000 : ℝ), (6069928261563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107094093/200000000 : ℝ)|^4587 ≤ (44748098180507/100000000000000 : ℝ)^3563
        have hw : |(107094093/200000000 : ℝ)|=(107094093/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202003973/10000000000 : ℝ)|^4587 ≤ (21556022641187/50000000000000 : ℝ)^3563
        have hw : |(5202003973/10000000000 : ℝ)|=(5202003973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1943807909/10000000000 : ℝ)|^4587 ≤ (6069928261563/50000000000000 : ℝ)^3563
        have hw : |(-1943807909/10000000000 : ℝ)|=(1943807909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_3 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4252709773/10000000000 : ℝ)*x 0 + (496891611/1250000000 : ℝ)*x 1 + (4546110567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252709773/10000000000 : ℝ)^4587 ≤ (33261737097687/100000000000000 : ℝ)^3563 := by
    have hnat : (4252709773 : ℕ)^4587*100000000000000^3563 ≤ 33261737097687^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252709773 10000000000 33261737097687 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496891611/1250000000 : ℝ)^4587 ≤ (30493411428857/100000000000000 : ℝ)^3563 := by
    have hnat : (496891611 : ℕ)^4587*100000000000000^3563 ≤ 30493411428857^3563*1250000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496891611 1250000000 30493411428857 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4546110567/10000000000 : ℝ)^4587 ≤ (36244851450701/100000000000000 : ℝ)^3563 := by
    have hnat : (4546110567 : ℕ)^4587*100000000000000^3563 ≤ 36244851450701^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546110567 10000000000 36244851450701 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252709773/10000000000 : ℝ), (496891611/1250000000 : ℝ), (4546110567/10000000000 : ℝ)] ![(33261737097687/100000000000000 : ℝ), (30493411428857/100000000000000 : ℝ), (36244851450701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252709773/10000000000 : ℝ)|^4587 ≤ (33261737097687/100000000000000 : ℝ)^3563
        have hw : |(4252709773/10000000000 : ℝ)|=(4252709773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(496891611/1250000000 : ℝ)|^4587 ≤ (30493411428857/100000000000000 : ℝ)^3563
        have hw : |(496891611/1250000000 : ℝ)|=(496891611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4546110567/10000000000 : ℝ)|^4587 ≤ (36244851450701/100000000000000 : ℝ)^3563
        have hw : |(4546110567/10000000000 : ℝ)|=(4546110567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_4 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-227176123/1250000000 : ℝ)*x 0 + (5203497079/10000000000 : ℝ)*x 1 + (5446565199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227176123/1250000000 : ℝ)^4587 ≤ (5566608277519/50000000000000 : ℝ)^3563 := by
    have hnat : (227176123 : ℕ)^4587*50000000000000^3563 ≤ 5566608277519^3563*1250000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227176123 1250000000 5566608277519 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203497079/10000000000 : ℝ)^4587 ≤ (21563988258187/50000000000000 : ℝ)^3563 := by
    have hnat : (5203497079 : ℕ)^4587*50000000000000^3563 ≤ 21563988258187^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203497079 10000000000 21563988258187 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446565199/10000000000 : ℝ)^4587 ≤ (45738806908787/100000000000000 : ℝ)^3563 := by
    have hnat : (5446565199 : ℕ)^4587*100000000000000^3563 ≤ 45738806908787^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446565199 10000000000 45738806908787 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227176123/1250000000 : ℝ), (5203497079/10000000000 : ℝ), (5446565199/10000000000 : ℝ)] ![(5566608277519/50000000000000 : ℝ), (21563988258187/50000000000000 : ℝ), (45738806908787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227176123/1250000000 : ℝ)|^4587 ≤ (5566608277519/50000000000000 : ℝ)^3563
        have hw : |(-227176123/1250000000 : ℝ)|=(227176123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203497079/10000000000 : ℝ)|^4587 ≤ (21563988258187/50000000000000 : ℝ)^3563
        have hw : |(5203497079/10000000000 : ℝ)|=(5203497079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446565199/10000000000 : ℝ)|^4587 ≤ (45738806908787/100000000000000 : ℝ)^3563
        have hw : |(5446565199/10000000000 : ℝ)|=(5446565199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_5 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132244937/250000000 : ℝ)*x 0 + (-1699246779/10000000000 : ℝ)*x 1 + (5446564907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132244937/250000000 : ℝ)^4587 ≤ (2753188365379/6250000000000 : ℝ)^3563 := by
    have hnat : (132244937 : ℕ)^4587*6250000000000^3563 ≤ 2753188365379^3563*250000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132244937 250000000 2753188365379 6250000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1699246779/10000000000 : ℝ)^4587 ≤ (5105091193663/50000000000000 : ℝ)^3563 := by
    have hnat : (1699246779 : ℕ)^4587*50000000000000^3563 ≤ 5105091193663^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699246779 10000000000 5105091193663 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446564907/10000000000 : ℝ)^4587 ≤ (11434700937977/25000000000000 : ℝ)^3563 := by
    have hnat : (5446564907 : ℕ)^4587*25000000000000^3563 ≤ 11434700937977^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446564907 10000000000 11434700937977 25000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132244937/250000000 : ℝ), (-1699246779/10000000000 : ℝ), (5446564907/10000000000 : ℝ)] ![(2753188365379/6250000000000 : ℝ), (5105091193663/50000000000000 : ℝ), (11434700937977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132244937/250000000 : ℝ)|^4587 ≤ (2753188365379/6250000000000 : ℝ)^3563
        have hw : |(132244937/250000000 : ℝ)|=(132244937/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1699246779/10000000000 : ℝ)|^4587 ≤ (5105091193663/50000000000000 : ℝ)^3563
        have hw : |(-1699246779/10000000000 : ℝ)|=(1699246779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446564907/10000000000 : ℝ)|^4587 ≤ (11434700937977/25000000000000 : ℝ)^3563
        have hw : |(5446564907/10000000000 : ℝ)|=(5446564907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_6 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322449329/2500000000 : ℝ)*x 0 + (5446565337/10000000000 : ℝ)*x 1 + (-424811601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322449329/2500000000 : ℝ)^4587 ≤ (22025506043921/50000000000000 : ℝ)^3563 := by
    have hnat : (1322449329 : ℕ)^4587*50000000000000^3563 ≤ 22025506043921^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322449329 2500000000 22025506043921 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446565337/10000000000 : ℝ)^4587 ≤ (1429337762523/3125000000000 : ℝ)^3563 := by
    have hnat : (5446565337 : ℕ)^4587*3125000000000^3563 ≤ 1429337762523^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446565337 10000000000 1429337762523 3125000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424811601/2500000000 : ℝ)^4587 ≤ (10210179486503/100000000000000 : ℝ)^3563 := by
    have hnat : (424811601 : ℕ)^4587*100000000000000^3563 ≤ 10210179486503^3563*2500000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424811601 2500000000 10210179486503 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322449329/2500000000 : ℝ), (5446565337/10000000000 : ℝ), (-424811601/2500000000 : ℝ)] ![(22025506043921/50000000000000 : ℝ), (1429337762523/3125000000000 : ℝ), (10210179486503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322449329/2500000000 : ℝ)|^4587 ≤ (22025506043921/50000000000000 : ℝ)^3563
        have hw : |(1322449329/2500000000 : ℝ)|=(1322449329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446565337/10000000000 : ℝ)|^4587 ≤ (1429337762523/3125000000000 : ℝ)^3563
        have hw : |(5446565337/10000000000 : ℝ)|=(5446565337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424811601/2500000000 : ℝ)|^4587 ≤ (10210179486503/100000000000000 : ℝ)^3563
        have hw : |(-424811601/2500000000 : ℝ)|=(424811601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1545_s2_7 (p : ℝ) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170112491/400000000 : ℝ)*x 0 + (283915349/625000000 : ℝ)*x 1 + (3978628791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170112491/400000000 : ℝ)^4587 ≤ (1039461537737/3125000000000 : ℝ)^3563 := by
    have hnat : (170112491 : ℕ)^4587*3125000000000^3563 ≤ 1039461537737^3563*400000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170112491 400000000 1039461537737 3125000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283915349/625000000 : ℝ)^4587 ≤ (18104645273933/50000000000000 : ℝ)^3563 := by
    have hnat : (283915349 : ℕ)^4587*50000000000000^3563 ≤ 18104645273933^3563*625000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283915349 625000000 18104645273933 50000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3978628791/10000000000 : ℝ)^4587 ≤ (30527940231823/100000000000000 : ℝ)^3563 := by
    have hnat : (3978628791 : ℕ)^4587*100000000000000^3563 ≤ 30527940231823^3563*10000000000^4587 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978628791 10000000000 30527940231823 100000000000000 4587 3563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4587/1024 : ℝ)) 4587 3563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170112491/400000000 : ℝ), (283915349/625000000 : ℝ), (3978628791/10000000000 : ℝ)] ![(1039461537737/3125000000000 : ℝ), (18104645273933/50000000000000 : ℝ), (30527940231823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170112491/400000000 : ℝ)|^4587 ≤ (1039461537737/3125000000000 : ℝ)^3563
        have hw : |(170112491/400000000 : ℝ)|=(170112491/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283915349/625000000 : ℝ)|^4587 ≤ (18104645273933/50000000000000 : ℝ)^3563
        have hw : |(283915349/625000000 : ℝ)|=(283915349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3978628791/10000000000 : ℝ)|^4587 ≤ (30527940231823/100000000000000 : ℝ)^3563
        have hw : |(3978628791/10000000000 : ℝ)|=(3978628791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1545_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2249/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1067/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15883/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2249/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2249/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2249/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2249/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2249/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2249/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8777/100000 : ℝ) ^ (4585/1024 : ℝ) ≤ (928455053054347/50000000000000000000 : ℝ) := by
    have hpowers : (8777/100000 : ℝ)^4585 ≤ (928455053054347/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8777 : ℕ)^4585*50000000000000000000^1024 ≤ 928455053054347^1024*100000^4585 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8777 100000 928455053054347 50000000000000000000 4585 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8777/100000 : ℝ)) (X := (928455053054347/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2249/12500 : ℝ) ^ (4585/1024 : ℝ) ≤ (11548594000931921/25000000000000000000 : ℝ) := by
    have hpowers : (2249/12500 : ℝ)^4585 ≤ (11548594000931921/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2249 : ℕ)^4585*25000000000000000000^1024 ≤ 11548594000931921^1024*12500^4585 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 12500 11548594000931921 25000000000000000000 4585 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/12500 : ℝ)) (X := (11548594000931921/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000928455053054347/25000000000000000000 : ℝ) ≤ (1250010367767319/1250000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (25000928455053054347/25000000000000000000 : ℝ)^1024 ≤ (1250010367767319/1250000000000000 : ℝ)^4585 := by
      have hnat : (25000928455053054347 : ℕ)^1024*1250000000000000^4585 ≤ 1250010367767319^4585*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000928455053054347 25000000000000000000 1250010367767319 1250000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250010367767319/1250000000000000 : ℝ)) (X := (25000928455053054347/25000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024025643054918189/50000000000000000000 : ℝ) ≤ (2000214592532649/2000000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (50024025643054918189/50000000000000000000 : ℝ)^1024 ≤ (2000214592532649/2000000000000000 : ℝ)^4585 := by
      have hnat : (50024025643054918189 : ℕ)^1024*2000000000000000^4585 ≤ 2000214592532649^4585*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024025643054918189 50000000000000000000 2000214592532649 2000000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000214592532649/2000000000000000 : ℝ)) (X := (50024025643054918189/50000000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511548594000931921/12500000000000000000 : ℝ) ≤ (5001031491593969/5000000000000000 : ℝ) ^ (4585/1024 : ℝ) := by
    have hpowers : (12511548594000931921/12500000000000000000 : ℝ)^1024 ≤ (5001031491593969/5000000000000000 : ℝ)^4585 := by
      have hnat : (12511548594000931921 : ℕ)^1024*5000000000000000^4585 ≤ 5001031491593969^4585*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511548594000931921 12500000000000000000 5001031491593969 5000000000000000 1024 4585 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001031491593969/5000000000000000 : ℝ)) (X := (12511548594000931921/12500000000000000000 : ℝ)) (by norm_num) 4585 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(928455053054347/50000000000000000000 : ℝ) ≤ ((46066692745758147879/46075000000000000000 : ℝ)+2*(990020524693/921500000000000 : ℝ)*(8777/100000 : ℝ))^(4585/1024 : ℝ) := by
    rw [show (46066692745758147879/46075000000000000000 : ℝ)+2*(990020524693/921500000000000 : ℝ)*(8777/100000 : ℝ)=(1250010367767319/1250000000000000 : ℝ) by norm_num, show 1+2*(928455053054347/50000000000000000000 : ℝ)=(25000928455053054347/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11548594000931921/25000000000000000000 : ℝ)+(928455053054347/50000000000000000000 : ℝ) ≤ ((46066692745758147879/46075000000000000000 : ℝ)+(990020524693/921500000000000 : ℝ)*((2249/12500 : ℝ)+(8777/100000 : ℝ)))^(4585/1024 : ℝ) := by
    rw [show (46066692745758147879/46075000000000000000 : ℝ)+(990020524693/921500000000000 : ℝ)*((2249/12500 : ℝ)+(8777/100000 : ℝ))=(2000214592532649/2000000000000000 : ℝ) by norm_num, show 1+(11548594000931921/25000000000000000000 : ℝ)+(928455053054347/50000000000000000000 : ℝ)=(50024025643054918189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11548594000931921/25000000000000000000 : ℝ) ≤ ((46066692745758147879/46075000000000000000 : ℝ)+2*(990020524693/921500000000000 : ℝ)*(2249/12500 : ℝ))^(4585/1024 : ℝ) := by
    rw [show (46066692745758147879/46075000000000000000 : ℝ)+2*(990020524693/921500000000000 : ℝ)*(2249/12500 : ℝ)=(5001031491593969/5000000000000000 : ℝ) by norm_num, show 1+2*(11548594000931921/25000000000000000000 : ℝ)=(12511548594000931921/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46066692745758147879/46075000000000000000 : ℝ)*(X 1 0+X 2 0)+(990020524693/921500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (8777/100000 : ℝ)) (hi := (2249/12500 : ℝ)) (c := (46066692745758147879/46075000000000000000 : ℝ)) (alpha := (990020524693/921500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46066692745758147879/46075000000000000000 : ℝ)*(X 0 1+X 2 1)+(990020524693/921500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (8777/100000 : ℝ)) (hi := (2249/12500 : ℝ)) (c := (46066692745758147879/46075000000000000000 : ℝ)) (alpha := (990020524693/921500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46066692745758147879/46075000000000000000 : ℝ)*(X 0 2+X 1 2)+(990020524693/921500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4585/1024 : ℝ)) (lo := (8777/100000 : ℝ)) (hi := (2249/12500 : ℝ)) (c := (46066692745758147879/46075000000000000000 : ℝ)) (alpha := (990020524693/921500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-908682247/5000000000 : ℝ)*X 0 0+(5320382/9765625 : ℝ)*X 0 1+(5202003981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83667261/156250000 : ℝ)*X 1 0+(-24297599/125000000 : ℝ)*X 1 1+(5202003911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107094093/200000000 : ℝ)*X 2 0+(5202003973/10000000000 : ℝ)*X 2 1+(-1943807909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4252709773/10000000000 : ℝ)*X 0 0+(496891611/1250000000 : ℝ)*X 0 1+(4546110567/10000000000 : ℝ)*X 0 2+(4252709773/10000000000 : ℝ)*X 1 0+(496891611/1250000000 : ℝ)*X 1 1+(4546110567/10000000000 : ℝ)*X 1 2+(4252709773/10000000000 : ℝ)*X 2 0+(496891611/1250000000 : ℝ)*X 2 1+(4546110567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-227176123/1250000000 : ℝ)*X 0 0+(5203497079/10000000000 : ℝ)*X 0 1+(5446565199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132244937/250000000 : ℝ)*X 1 0+(-1699246779/10000000000 : ℝ)*X 1 1+(5446564907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322449329/2500000000 : ℝ)*X 2 0+(5446565337/10000000000 : ℝ)*X 2 1+(-424811601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170112491/400000000 : ℝ)*X 0 0+(283915349/625000000 : ℝ)*X 0 1+(3978628791/10000000000 : ℝ)*X 0 2+(170112491/400000000 : ℝ)*X 1 0+(283915349/625000000 : ℝ)*X 1 1+(3978628791/10000000000 : ℝ)*X 1 2+(170112491/400000000 : ℝ)*X 2 0+(283915349/625000000 : ℝ)*X 2 1+(3978628791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1545_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1793754636643740408117768309/230375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734598783/50000000000000 : ℝ)*(base19) + (40103773/3125000000000 : ℝ)*(base23) + (77586127/100000000000000 : ℝ)*(lower2) + (225962821/100000000000000 : ℝ)*(upper3) + (117634589/100000000000000 : ℝ)*(upper5) + (290768422238057/10000000000000 : ℝ)*(major0) + (290768422238057/10000000000000 : ℝ)*(major1) + (290768422238057/10000000000000 : ℝ)*(major2) + (507993839608107/12500000000000 : ℝ)*(sp0) + (4063967668814223/100000000000000 : ℝ)*(sp1) + (2031983927345527/50000000000000 : ℝ)*(sp2) + (1751389769934001/100000000000000 : ℝ)*(sp3) + (9210573467/50000000000000 : ℝ)*(sp4) + (927727407/10000000000000 : ℝ)*(sp7) + (1751399047208071/100000000000000 : ℝ)*(f.failure) + (406396913801179/10000000000000 : ℝ)*(f.sum) + (16447996788857/9215000000000000000000000000 : ℝ)*base65 + (1216659222118818897/460750000000000000000000000000000 : ℝ)*base68 + (4623108456171568897/460750000000000000000000000000000 : ℝ)*base70 + (582202470011431103/460750000000000000000000000000000 : ℝ)*base71 + (827751402641/4607500000000000000000000000 : ℝ)*base73 + (151420536955181103/460750000000000000000000000000000 : ℝ)*base75 + (2719990986749568897/460750000000000000000000000000000 : ℝ)*base78 + (2769700008159818897/460750000000000000000000000000000 : ℝ)*base80 + (10231904723963/9215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5165359/5000000000000000000000 : ℝ)*base89 + (5165359/5000000000000000000000 : ℝ)*base91 + (5165359/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5216292237156273483796769403/1151875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581347059/100000000000000 : ℝ)*(base19) + (85672699/12500000000000 : ℝ)*(base23) + (4484461/6250000000000 : ℝ)*(upper2) + (957311/100000000000000 : ℝ)*(lower3) + (2943540449158081/100000000000000 : ℝ)*(major0) + (2943540449158081/100000000000000 : ℝ)*(major1) + (2943540449158081/100000000000000 : ℝ)*(major2) + (6226130223/100000000000000 : ℝ)*(sp0) + (2435430549/20000000000000 : ℝ)*(sp1) + (19996241721/100000000000000 : ℝ)*(sp2) + (2057039012562791/50000000000000 : ℝ)*(sp4) + (4114071492756001/100000000000000 : ℝ)*(sp5) + (4114063569632493/100000000000000 : ℝ)*(sp6) + (1772996496109587/100000000000000 : ℝ)*(sp7) + (1772996496109587/100000000000000 : ℝ)*(f.failure) + (2057042125627903/50000000000000 : ℝ)*(f.sum) + (31466437896749/5759375000000000000000000000 : ℝ)*base66 + (49591971756777510199/4607500000000000000000000000000000 : ℝ)*base67 + (23285180286117510199/4607500000000000000000000000000000 : ℝ)*base69 + (34638463502265010199/4607500000000000000000000000000000 : ℝ)*base71 + (3063276318521/23037500000000000000000000000 : ℝ)*base74 + (44947783759360010199/4607500000000000000000000000000000 : ℝ)*base75 + (7832556807619989801/4607500000000000000000000000000000 : ℝ)*base78 + (7073191235337510199/4607500000000000000000000000000000 : ℝ)*base79 + (199145791488567/46075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13075877/5000000000000000000000 : ℝ)*base90 + (13075877/5000000000000000000000 : ℝ)*base92 + (13075877/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1545_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2249/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1545_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1545_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1545_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1545_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1545_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4585/1024 : ℝ) ≤ p) (hpb : p ≤ (4587/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83010329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1545_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1584_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:50.85013+00:00
-- url     : https://prove2.me/submissions/4cb8edf0-34b2-4dff-ad8f-846d9b1d8b74

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
theorem support_rectangle_w1584_s3_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55201683/312500000 : ℝ)*x 0 + (5425438843/10000000000 : ℝ)*x 1 + (5219233549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55201683/312500000 : ℝ)^4665 ≤ (10848164949469/100000000000000 : ℝ)^3641 := by
    have hnat : (55201683 : ℕ)^4665*100000000000000^3641 ≤ 10848164949469^3641*312500000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55201683 312500000 10848164949469 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425438843/10000000000 : ℝ)^4665 ≤ (4568219460009/10000000000000 : ℝ)^3641 := by
    have hnat : (5425438843 : ℕ)^4665*10000000000000^3641 ≤ 4568219460009^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425438843 10000000000 4568219460009 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219233549/10000000000 : ℝ)^4665 ≤ (679213131693/1562500000000 : ℝ)^3641 := by
    have hnat : (5219233549 : ℕ)^4665*1562500000000^3641 ≤ 679213131693^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219233549 10000000000 679213131693 1562500000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55201683/312500000 : ℝ), (5425438843/10000000000 : ℝ), (5219233549/10000000000 : ℝ)] ![(10848164949469/100000000000000 : ℝ), (4568219460009/10000000000000 : ℝ), (679213131693/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55201683/312500000 : ℝ)|^4665 ≤ (10848164949469/100000000000000 : ℝ)^3641
        have hw : |(-55201683/312500000 : ℝ)|=(55201683/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425438843/10000000000 : ℝ)|^4665 ≤ (4568219460009/10000000000000 : ℝ)^3641
        have hw : |(5425438843/10000000000 : ℝ)|=(5425438843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219233549/10000000000 : ℝ)|^4665 ≤ (679213131693/1562500000000 : ℝ)^3641
        have hw : |(5219233549/10000000000 : ℝ)|=(5219233549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347699579/10000000000 : ℝ)*x 0 + (-467987811/2500000000 : ℝ)*x 1 + (521923287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347699579/10000000000 : ℝ)^4665 ≤ (44845234977803/100000000000000 : ℝ)^3641 := by
    have hnat : (5347699579 : ℕ)^4665*100000000000000^3641 ≤ 44845234977803^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347699579 10000000000 44845234977803 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467987811/2500000000 : ℝ)^4665 ≤ (5842565913641/50000000000000 : ℝ)^3641 := by
    have hnat : (467987811 : ℕ)^4665*50000000000000^3641 ≤ 5842565913641^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467987811 2500000000 5842565913641 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521923287/1000000000 : ℝ)^4665 ≤ (43469633182657/100000000000000 : ℝ)^3641 := by
    have hnat : (521923287 : ℕ)^4665*100000000000000^3641 ≤ 43469633182657^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521923287 1000000000 43469633182657 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347699579/10000000000 : ℝ), (-467987811/2500000000 : ℝ), (521923287/1000000000 : ℝ)] ![(44845234977803/100000000000000 : ℝ), (5842565913641/50000000000000 : ℝ), (43469633182657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347699579/10000000000 : ℝ)|^4665 ≤ (44845234977803/100000000000000 : ℝ)^3641
        have hw : |(5347699579/10000000000 : ℝ)|=(5347699579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-467987811/2500000000 : ℝ)|^4665 ≤ (5842565913641/50000000000000 : ℝ)^3641
        have hw : |(-467987811/2500000000 : ℝ)|=(467987811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521923287/1000000000 : ℝ)|^4665 ≤ (43469633182657/100000000000000 : ℝ)^3641
        have hw : |(521923287/1000000000 : ℝ)|=(521923287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347699689/10000000000 : ℝ)*x 0 + (5219233053/10000000000 : ℝ)*x 1 + (-467987713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347699689/10000000000 : ℝ)^4665 ≤ (22422618079841/50000000000000 : ℝ)^3641 := by
    have hnat : (5347699689 : ℕ)^4665*50000000000000^3641 ≤ 22422618079841^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347699689 10000000000 22422618079841 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219233053/10000000000 : ℝ)^4665 ≤ (21734817567737/50000000000000 : ℝ)^3641 := by
    have hnat : (5219233053 : ℕ)^4665*50000000000000^3641 ≤ 21734817567737^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219233053 10000000000 21734817567737 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467987713/2500000000 : ℝ)^4665 ≤ (2921282173037/25000000000000 : ℝ)^3641 := by
    have hnat : (467987713 : ℕ)^4665*25000000000000^3641 ≤ 2921282173037^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467987713 2500000000 2921282173037 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347699689/10000000000 : ℝ), (5219233053/10000000000 : ℝ), (-467987713/2500000000 : ℝ)] ![(22422618079841/50000000000000 : ℝ), (21734817567737/50000000000000 : ℝ), (2921282173037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347699689/10000000000 : ℝ)|^4665 ≤ (22422618079841/50000000000000 : ℝ)^3641
        have hw : |(5347699689/10000000000 : ℝ)|=(5347699689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219233053/10000000000 : ℝ)|^4665 ≤ (21734817567737/50000000000000 : ℝ)^3641
        have hw : |(5219233053/10000000000 : ℝ)|=(5219233053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467987713/2500000000 : ℝ)|^4665 ≤ (2921282173037/25000000000000 : ℝ)^3641
        have hw : |(-467987713/2500000000 : ℝ)|=(467987713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529656037/1250000000 : ℝ)*x 0 + (3997248881/10000000000 : ℝ)*x 1 + (1122164221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529656037/1250000000 : ℝ)^4665 ≤ (6656324114471/20000000000000 : ℝ)^3641 := by
    have hnat : (529656037 : ℕ)^4665*20000000000000^3641 ≤ 6656324114471^3641*1250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529656037 1250000000 6656324114471 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3997248881/10000000000 : ℝ)^4665 ≤ (30885877328449/100000000000000 : ℝ)^3641 := by
    have hnat : (3997248881 : ℕ)^4665*100000000000000^3641 ≤ 30885877328449^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997248881 10000000000 30885877328449 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122164221/2500000000 : ℝ)^4665 ≤ (35832502077729/100000000000000 : ℝ)^3641 := by
    have hnat : (1122164221 : ℕ)^4665*100000000000000^3641 ≤ 35832502077729^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122164221 2500000000 35832502077729 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529656037/1250000000 : ℝ), (3997248881/10000000000 : ℝ), (1122164221/2500000000 : ℝ)] ![(6656324114471/20000000000000 : ℝ), (30885877328449/100000000000000 : ℝ), (35832502077729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529656037/1250000000 : ℝ)|^4665 ≤ (6656324114471/20000000000000 : ℝ)^3641
        have hw : |(529656037/1250000000 : ℝ)|=(529656037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3997248881/10000000000 : ℝ)|^4665 ≤ (30885877328449/100000000000000 : ℝ)^3641
        have hw : |(3997248881/10000000000 : ℝ)|=(3997248881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122164221/2500000000 : ℝ)|^4665 ≤ (35832502077729/100000000000000 : ℝ)^3641
        have hw : |(1122164221/2500000000 : ℝ)|=(1122164221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1766480871/10000000000 : ℝ)*x 0 + (522032477/1000000000 : ℝ)*x 1 + (2712169841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1766480871/10000000000 : ℝ)^4665 ≤ (10848377514029/100000000000000 : ℝ)^3641 := by
    have hnat : (1766480871 : ℕ)^4665*100000000000000^3641 ≤ 10848377514029^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766480871 10000000000 10848377514029 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522032477/1000000000 : ℝ)^4665 ≤ (43481285328497/100000000000000 : ℝ)^3641 := by
    have hnat : (522032477 : ℕ)^4665*100000000000000^3641 ≤ 43481285328497^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522032477 1000000000 43481285328497 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712169841/5000000000 : ℝ)^4665 ≤ (11417584282803/25000000000000 : ℝ)^3641 := by
    have hnat : (2712169841 : ℕ)^4665*25000000000000^3641 ≤ 11417584282803^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712169841 5000000000 11417584282803 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1766480871/10000000000 : ℝ), (522032477/1000000000 : ℝ), (2712169841/5000000000 : ℝ)] ![(10848377514029/100000000000000 : ℝ), (43481285328497/100000000000000 : ℝ), (11417584282803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1766480871/10000000000 : ℝ)|^4665 ≤ (10848377514029/100000000000000 : ℝ)^3641
        have hw : |(-1766480871/10000000000 : ℝ)|=(1766480871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522032477/1000000000 : ℝ)|^4665 ≤ (43481285328497/100000000000000 : ℝ)^3641
        have hw : |(522032477/1000000000 : ℝ)|=(522032477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712169841/5000000000 : ℝ)|^4665 ≤ (11417584282803/25000000000000 : ℝ)^3641
        have hw : |(2712169841/5000000000 : ℝ)|=(2712169841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293054493/10000000000 : ℝ)*x 0 + (-1666844133/10000000000 : ℝ)*x 1 + (5424340497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293054493/10000000000 : ℝ)^4665 ≤ (5532369326167/12500000000000 : ℝ)^3641 := by
    have hnat : (5293054493 : ℕ)^4665*12500000000000^3641 ≤ 5532369326167^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293054493 10000000000 5532369326167 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1666844133/10000000000 : ℝ)^4665 ≤ (5035349726639/50000000000000 : ℝ)^3641 := by
    have hnat : (1666844133 : ℕ)^4665*50000000000000^3641 ≤ 5035349726639^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666844133 10000000000 5035349726639 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424340497/10000000000 : ℝ)^4665 ≤ (22835172961487/50000000000000 : ℝ)^3641 := by
    have hnat : (5424340497 : ℕ)^4665*50000000000000^3641 ≤ 22835172961487^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424340497 10000000000 22835172961487 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293054493/10000000000 : ℝ), (-1666844133/10000000000 : ℝ), (5424340497/10000000000 : ℝ)] ![(5532369326167/12500000000000 : ℝ), (5035349726639/50000000000000 : ℝ), (22835172961487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293054493/10000000000 : ℝ)|^4665 ≤ (5532369326167/12500000000000 : ℝ)^3641
        have hw : |(5293054493/10000000000 : ℝ)|=(5293054493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1666844133/10000000000 : ℝ)|^4665 ≤ (5035349726639/50000000000000 : ℝ)^3641
        have hw : |(-1666844133/10000000000 : ℝ)|=(1666844133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424340497/10000000000 : ℝ)|^4665 ≤ (22835172961487/50000000000000 : ℝ)^3641
        have hw : |(5424340497/10000000000 : ℝ)|=(5424340497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058611029/2000000000 : ℝ)*x 0 + (16951061/31250000 : ℝ)*x 1 + (-1666844591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058611029/2000000000 : ℝ)^4665 ≤ (2766185099653/6250000000000 : ℝ)^3641 := by
    have hnat : (1058611029 : ℕ)^4665*6250000000000^3641 ≤ 2766185099653^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058611029 2000000000 2766185099653 6250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16951061/31250000 : ℝ)^4665 ≤ (45670335383647/100000000000000 : ℝ)^3641 := by
    have hnat : (16951061 : ℕ)^4665*100000000000000^3641 ≤ 45670335383647^3641*31250000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16951061 31250000 45670335383647 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1666844591/10000000000 : ℝ)^4665 ≤ (2517675749661/25000000000000 : ℝ)^3641 := by
    have hnat : (1666844591 : ℕ)^4665*25000000000000^3641 ≤ 2517675749661^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666844591 10000000000 2517675749661 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058611029/2000000000 : ℝ), (16951061/31250000 : ℝ), (-1666844591/10000000000 : ℝ)] ![(2766185099653/6250000000000 : ℝ), (45670335383647/100000000000000 : ℝ), (2517675749661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058611029/2000000000 : ℝ)|^4665 ≤ (2766185099653/6250000000000 : ℝ)^3641
        have hw : |(1058611029/2000000000 : ℝ)|=(1058611029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16951061/31250000 : ℝ)|^4665 ≤ (45670335383647/100000000000000 : ℝ)^3641
        have hw : |(16951061/31250000 : ℝ)|=(16951061/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1666844591/10000000000 : ℝ)|^4665 ≤ (2517675749661/25000000000000 : ℝ)^3641
        have hw : |(-1666844591/10000000000 : ℝ)|=(1666844591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s3_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118656683/5000000000 : ℝ)*x 0 + (1121514111/2500000000 : ℝ)*x 1 + (3999868911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118656683/5000000000 : ℝ)^4665 ≤ (16641137704719/50000000000000 : ℝ)^3641 := by
    have hnat : (2118656683 : ℕ)^4665*50000000000000^3641 ≤ 16641137704719^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118656683 5000000000 16641137704719 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121514111/2500000000 : ℝ)^4665 ≤ (35805906884757/100000000000000 : ℝ)^3641 := by
    have hnat : (1121514111 : ℕ)^4665*100000000000000^3641 ≤ 35805906884757^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121514111 2500000000 35805906884757 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3999868911/10000000000 : ℝ)^4665 ≤ (30911817688937/100000000000000 : ℝ)^3641 := by
    have hnat : (3999868911 : ℕ)^4665*100000000000000^3641 ≤ 30911817688937^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999868911 10000000000 30911817688937 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118656683/5000000000 : ℝ), (1121514111/2500000000 : ℝ), (3999868911/10000000000 : ℝ)] ![(16641137704719/50000000000000 : ℝ), (35805906884757/100000000000000 : ℝ), (30911817688937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118656683/5000000000 : ℝ)|^4665 ≤ (16641137704719/50000000000000 : ℝ)^3641
        have hw : |(2118656683/5000000000 : ℝ)|=(2118656683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121514111/2500000000 : ℝ)|^4665 ≤ (35805906884757/100000000000000 : ℝ)^3641
        have hw : |(1121514111/2500000000 : ℝ)|=(1121514111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3999868911/10000000000 : ℝ)|^4665 ≤ (30911817688937/100000000000000 : ℝ)^3641
        have hw : |(3999868911/10000000000 : ℝ)|=(3999868911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (493/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5569/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15513/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (493/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (493/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (493/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (493/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (493/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (493/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (681/6250 : ℝ) ^ (4663/1024 : ℝ) ≤ (4130405008352283/100000000000000000000 : ℝ) := by
    have hpowers : (681/6250 : ℝ)^4663 ≤ (4130405008352283/100000000000000000000 : ℝ)^1024 := by
      have hnat : (681 : ℕ)^4663*100000000000000000000^1024 ≤ 4130405008352283^1024*6250^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        681 6250 4130405008352283 100000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (681/6250 : ℝ)) (X := (4130405008352283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (493/3125 : ℝ) ^ (4663/1024 : ℝ) ≤ (1392482410645387/6250000000000000000 : ℝ) := by
    have hpowers : (493/3125 : ℝ)^4663 ≤ (1392482410645387/6250000000000000000 : ℝ)^1024 := by
      have hnat : (493 : ℕ)^4663*6250000000000000000^1024 ≤ 1392482410645387^1024*3125^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        493 3125 1392482410645387 6250000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (493/3125 : ℝ)) (X := (1392482410645387/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004130405008352283/50000000000000000000 : ℝ) ≤ (10000181402462019/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (50004130405008352283/50000000000000000000 : ℝ)^1024 ≤ (10000181402462019/10000000000000000 : ℝ)^4663 := by
      have hnat : (50004130405008352283 : ℕ)^1024*10000000000000000^4663 ≤ 10000181402462019^4663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004130405008352283 50000000000000000000 10000181402462019 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000181402462019/10000000000000000 : ℝ)) (X := (50004130405008352283/50000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001056404943147139/4000000000000000000 : ℝ) ≤ (10000579909501229/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (4001056404943147139/4000000000000000000 : ℝ)^1024 ≤ (10000579909501229/10000000000000000 : ℝ)^4663 := by
      have hnat : (4001056404943147139 : ℕ)^1024*10000000000000000^4663 ≤ 10000579909501229^4663*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001056404943147139 4000000000000000000 10000579909501229 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000579909501229/10000000000000000 : ℝ)) (X := (4001056404943147139/4000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126392482410645387/3125000000000000000 : ℝ) ≤ (10000978416540439/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (3126392482410645387/3125000000000000000 : ℝ)^1024 ≤ (10000978416540439/10000000000000000 : ℝ)^4663 := by
      have hnat : (3126392482410645387 : ℕ)^1024*10000000000000000^4663 ≤ 10000978416540439^4663*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126392482410645387 3125000000000000000 10000978416540439 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000978416540439/10000000000000000 : ℝ)) (X := (3126392482410645387/3125000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4130405008352283/100000000000000000000 : ℝ) ≤ ((121980502446540471/122000000000000000 : ℝ)+2*(39850703921/48800000000000 : ℝ)*(681/6250 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (121980502446540471/122000000000000000 : ℝ)+2*(39850703921/48800000000000 : ℝ)*(681/6250 : ℝ)=(10000181402462019/10000000000000000 : ℝ) by norm_num, show 1+2*(4130405008352283/100000000000000000000 : ℝ)=(50004130405008352283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1392482410645387/6250000000000000000 : ℝ)+(4130405008352283/100000000000000000000 : ℝ) ≤ ((121980502446540471/122000000000000000 : ℝ)+(39850703921/48800000000000 : ℝ)*((493/3125 : ℝ)+(681/6250 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (121980502446540471/122000000000000000 : ℝ)+(39850703921/48800000000000 : ℝ)*((493/3125 : ℝ)+(681/6250 : ℝ))=(10000579909501229/10000000000000000 : ℝ) by norm_num, show 1+(1392482410645387/6250000000000000000 : ℝ)+(4130405008352283/100000000000000000000 : ℝ)=(4001056404943147139/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1392482410645387/6250000000000000000 : ℝ) ≤ ((121980502446540471/122000000000000000 : ℝ)+2*(39850703921/48800000000000 : ℝ)*(493/3125 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (121980502446540471/122000000000000000 : ℝ)+2*(39850703921/48800000000000 : ℝ)*(493/3125 : ℝ)=(10000978416540439/10000000000000000 : ℝ) by norm_num, show 1+2*(1392482410645387/6250000000000000000 : ℝ)=(3126392482410645387/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (121980502446540471/122000000000000000 : ℝ)*(X 1 0+X 2 0)+(39850703921/48800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (493/3125 : ℝ)) (c := (121980502446540471/122000000000000000 : ℝ)) (alpha := (39850703921/48800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (121980502446540471/122000000000000000 : ℝ)*(X 0 1+X 2 1)+(39850703921/48800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (493/3125 : ℝ)) (c := (121980502446540471/122000000000000000 : ℝ)) (alpha := (39850703921/48800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (121980502446540471/122000000000000000 : ℝ)*(X 0 2+X 1 2)+(39850703921/48800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (493/3125 : ℝ)) (c := (121980502446540471/122000000000000000 : ℝ)) (alpha := (39850703921/48800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-55201683/312500000 : ℝ)*X 0 0+(5425438843/10000000000 : ℝ)*X 0 1+(5219233549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347699579/10000000000 : ℝ)*X 1 0+(-467987811/2500000000 : ℝ)*X 1 1+(521923287/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347699689/10000000000 : ℝ)*X 2 0+(5219233053/10000000000 : ℝ)*X 2 1+(-467987713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((529656037/1250000000 : ℝ)*X 0 0+(3997248881/10000000000 : ℝ)*X 0 1+(1122164221/2500000000 : ℝ)*X 0 2+(529656037/1250000000 : ℝ)*X 1 0+(3997248881/10000000000 : ℝ)*X 1 1+(1122164221/2500000000 : ℝ)*X 1 2+(529656037/1250000000 : ℝ)*X 2 0+(3997248881/10000000000 : ℝ)*X 2 1+(1122164221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1766480871/10000000000 : ℝ)*X 0 0+(522032477/1000000000 : ℝ)*X 0 1+(2712169841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293054493/10000000000 : ℝ)*X 1 0+(-1666844133/10000000000 : ℝ)*X 1 1+(5424340497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058611029/2000000000 : ℝ)*X 2 0+(16951061/31250000 : ℝ)*X 2 1+(-1666844591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118656683/5000000000 : ℝ)*X 0 0+(1121514111/2500000000 : ℝ)*X 0 1+(3999868911/10000000000 : ℝ)*X 0 2+(2118656683/5000000000 : ℝ)*X 1 0+(1121514111/2500000000 : ℝ)*X 1 1+(3999868911/10000000000 : ℝ)*X 1 2+(2118656683/5000000000 : ℝ)*X 2 0+(1121514111/2500000000 : ℝ)*X 2 1+(3999868911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60970276670714149527214329/6100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1883198519/100000000000000 : ℝ)*(base19) + (480402453/25000000000000 : ℝ)*(base23) + (3280401/10000000000000 : ℝ)*(lower2) + (15195577/12500000000000 : ℝ)*(upper3) + (487230311/100000000000000 : ℝ)*(upper5) + (3442278590189567/100000000000000 : ℝ)*(major0) + (3442278590189567/100000000000000 : ℝ)*(major1) + (840400046433/24414062500 : ℝ)*(major2) + (24247725792327/500000000000 : ℝ)*(sp0) + (4849565188952773/100000000000000 : ℝ)*(sp1) + (4849565150541479/100000000000000 : ℝ)*(sp2) + (2034981000709571/100000000000000 : ℝ)*(sp3) + (5478421473/25000000000000 : ℝ)*(sp4) + (1754869471/20000000000000 : ℝ)*(sp7) + (1017494887528463/50000000000000 : ℝ)*(f.failure) + (1212391768037823/25000000000000 : ℝ)*(f.sum) + (47793789597/976000000000000000000000000 : ℝ)*base66 + (81950080606413943/12200000000000000000000000000000 : ℝ)*base68 + (2712214293981007/3050000000000000000000000000000 : ℝ)*base69 + (86520356209186057/12200000000000000000000000000000 : ℝ)*base71 + (6506485935917/976000000000000000000000000 : ℝ)*base74 + (8952137282318993/3050000000000000000000000000000 : ℝ)*base76 + (15576336388583557/12200000000000000000000000000000 : ℝ)*base77 + (130161626800383557/12200000000000000000000000000000 : ℝ)*base79 + (7147805836633/2440000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (34566707/5000000000000000000000 : ℝ)*base89 + (34566707/5000000000000000000000 : ℝ)*base91 + (15433293/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111969818709677048021379/15250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22234733/100000000000000 : ℝ)*(base19) + (186784699/20000000000000 : ℝ)*(base23) + (267560169/100000000000000 : ℝ)*(upper3) + (39746789/25000000000000 : ℝ)*(lower4) + (13004169/25000000000000 : ℝ)*(upper5) + (17396045157033/500000000000 : ℝ)*(major0) + (17396045157033/500000000000 : ℝ)*(major1) + (17396045157033/500000000000 : ℝ)*(major2) + (3463882263/50000000000000 : ℝ)*(sp1) + (7658134337/100000000000000 : ℝ)*(sp2) + (4901595681600567/100000000000000 : ℝ)*(sp4) + (4901588731601309/100000000000000 : ℝ)*(sp5) + (980317417908547/20000000000000 : ℝ)*(sp6) + (1028411068234927/50000000000000 : ℝ)*(sp7) + (1028411068234927/50000000000000 : ℝ)*(f.failure) + (4901595681600567/100000000000000 : ℝ)*(f.sum) + (44246882581/30500000000000000000000000 : ℝ)*base66 + (2708141039043/61000000000000000000000000000 : ℝ)*base67 + (106172279202957/61000000000000000000000000000 : ℝ)*base70 + (40513450989957/61000000000000000000000000000 : ℝ)*base72 + (6530669087/6100000000000000000000000 : ℝ)*base74 + (1383163389641957/61000000000000000000000000000 : ℝ)*base76 + (204955840486957/61000000000000000000000000000 : ℝ)*base78 + (547382750691957/61000000000000000000000000000 : ℝ)*base80 + (6820746231/3050000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (32130003/5000000000000000000000 : ℝ)*base89 + (32130003/5000000000000000000000 : ℝ)*base91 + (32130003/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1584_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (493/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15513/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1584_s4_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-883322877/5000000000 : ℝ)*x 0 + (2712075361/5000000000 : ℝ)*x 1 + (5220394207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883322877/5000000000 : ℝ)^4665 ≤ (542483744881/5000000000000 : ℝ)^3641 := by
    have hnat : (883322877 : ℕ)^4665*5000000000000^3641 ≤ 542483744881^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883322877 5000000000 542483744881 5000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712075361/5000000000 : ℝ)^4665 ≤ (11417074686733/25000000000000 : ℝ)^3641 := by
    have hnat : (2712075361 : ℕ)^4665*25000000000000^3641 ≤ 11417074686733^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712075361 5000000000 11417074686733 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220394207/10000000000 : ℝ)^4665 ≤ (43482026344491/100000000000000 : ℝ)^3641 := by
    have hnat : (5220394207 : ℕ)^4665*100000000000000^3641 ≤ 43482026344491^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220394207 10000000000 43482026344491 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-883322877/5000000000 : ℝ), (2712075361/5000000000 : ℝ), (5220394207/10000000000 : ℝ)] ![(542483744881/5000000000000 : ℝ), (11417074686733/25000000000000 : ℝ), (43482026344491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-883322877/5000000000 : ℝ)|^4665 ≤ (542483744881/5000000000000 : ℝ)^3641
        have hw : |(-883322877/5000000000 : ℝ)|=(883322877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712075361/5000000000 : ℝ)|^4665 ≤ (11417074686733/25000000000000 : ℝ)^3641
        have hw : |(2712075361/5000000000 : ℝ)|=(2712075361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220394207/10000000000 : ℝ)|^4665 ≤ (43482026344491/100000000000000 : ℝ)^3641
        have hw : |(5220394207/10000000000 : ℝ)|=(5220394207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347357103/10000000000 : ℝ)*x 0 + (-935431183/5000000000 : ℝ)*x 1 + (2610196841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347357103/10000000000 : ℝ)^4665 ≤ (22420777663939/50000000000000 : ℝ)^3641 := by
    have hnat : (5347357103 : ℕ)^4665*50000000000000^3641 ≤ 22420777663939^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347357103 10000000000 22420777663939 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935431183/5000000000 : ℝ)^4665 ≤ (1459552990127/12500000000000 : ℝ)^3641 := by
    have hnat : (935431183 : ℕ)^4665*12500000000000^3641 ≤ 1459552990127^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935431183 5000000000 1459552990127 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610196841/5000000000 : ℝ)^4665 ≤ (43482020741799/100000000000000 : ℝ)^3641 := by
    have hnat : (2610196841 : ℕ)^4665*100000000000000^3641 ≤ 43482020741799^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610196841 5000000000 43482020741799 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347357103/10000000000 : ℝ), (-935431183/5000000000 : ℝ), (2610196841/5000000000 : ℝ)] ![(22420777663939/50000000000000 : ℝ), (1459552990127/12500000000000 : ℝ), (43482020741799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347357103/10000000000 : ℝ)|^4665 ≤ (22420777663939/50000000000000 : ℝ)^3641
        have hw : |(5347357103/10000000000 : ℝ)|=(5347357103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935431183/5000000000 : ℝ)|^4665 ≤ (1459552990127/12500000000000 : ℝ)^3641
        have hw : |(-935431183/5000000000 : ℝ)|=(935431183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610196841/5000000000 : ℝ)|^4665 ≤ (43482020741799/100000000000000 : ℝ)^3641
        have hw : |(2610196841/5000000000 : ℝ)|=(2610196841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347357389/10000000000 : ℝ)*x 0 + (2610196673/5000000000 : ℝ)*x 1 + (-187086243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347357389/10000000000 : ℝ)^4665 ≤ (11210389600177/25000000000000 : ℝ)^3641 := by
    have hnat : (5347357389 : ℕ)^4665*25000000000000^3641 ≤ 11210389600177^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347357389 10000000000 11210389600177 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610196673/5000000000 : ℝ)^4665 ≤ (10870504289019/25000000000000 : ℝ)^3641 := by
    have hnat : (2610196673 : ℕ)^4665*25000000000000^3641 ≤ 10870504289019^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610196673 5000000000 10870504289019 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187086243/1000000000 : ℝ)^4665 ≤ (11676424432791/100000000000000 : ℝ)^3641 := by
    have hnat : (187086243 : ℕ)^4665*100000000000000^3641 ≤ 11676424432791^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187086243 1000000000 11676424432791 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347357389/10000000000 : ℝ), (2610196673/5000000000 : ℝ), (-187086243/1000000000 : ℝ)] ![(11210389600177/25000000000000 : ℝ), (10870504289019/25000000000000 : ℝ), (11676424432791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347357389/10000000000 : ℝ)|^4665 ≤ (11210389600177/25000000000000 : ℝ)^3641
        have hw : |(5347357389/10000000000 : ℝ)|=(5347357389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610196673/5000000000 : ℝ)|^4665 ≤ (10870504289019/25000000000000 : ℝ)^3641
        have hw : |(2610196673/5000000000 : ℝ)|=(2610196673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187086243/1000000000 : ℝ)|^4665 ≤ (11676424432791/100000000000000 : ℝ)^3641
        have hw : |(-187086243/1000000000 : ℝ)|=(187086243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13241779/31250000 : ℝ)*x 0 + (2000076687/5000000000 : ℝ)*x 1 + (4485725981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13241779/31250000 : ℝ)^4665 ≤ (33282838106651/100000000000000 : ℝ)^3641 := by
    have hnat : (13241779 : ℕ)^4665*100000000000000^3641 ≤ 33282838106651^3641*31250000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13241779 31250000 33282838106651 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000076687/5000000000 : ℝ)^4665 ≤ (3864329298041/12500000000000 : ℝ)^3641 := by
    have hnat : (2000076687 : ℕ)^4665*12500000000000^3641 ≤ 3864329298041^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000076687 5000000000 3864329298041 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485725981/10000000000 : ℝ)^4665 ≤ (17901263743717/50000000000000 : ℝ)^3641 := by
    have hnat : (4485725981 : ℕ)^4665*50000000000000^3641 ≤ 17901263743717^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485725981 10000000000 17901263743717 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13241779/31250000 : ℝ), (2000076687/5000000000 : ℝ), (4485725981/10000000000 : ℝ)] ![(33282838106651/100000000000000 : ℝ), (3864329298041/12500000000000 : ℝ), (17901263743717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13241779/31250000 : ℝ)|^4665 ≤ (33282838106651/100000000000000 : ℝ)^3641
        have hw : |(13241779/31250000 : ℝ)|=(13241779/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000076687/5000000000 : ℝ)|^4665 ≤ (3864329298041/12500000000000 : ℝ)^3641
        have hw : |(2000076687/5000000000 : ℝ)|=(2000076687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485725981/10000000000 : ℝ)|^4665 ≤ (17901263743717/50000000000000 : ℝ)^3641
        have hw : |(4485725981/10000000000 : ℝ)|=(4485725981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-70666889/400000000 : ℝ)*x 0 + (5221459347/10000000000 : ℝ)*x 1 + (5423077621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70666889/400000000 : ℝ)^4665 ≤ (1084988318813/10000000000000 : ℝ)^3641 := by
    have hnat : (70666889 : ℕ)^4665*10000000000000^3641 ≤ 1084988318813^3641*400000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70666889 400000000 1084988318813 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221459347/10000000000 : ℝ)^4665 ≤ (43493393625573/100000000000000 : ℝ)^3641 := by
    have hnat : (5221459347 : ℕ)^4665*100000000000000^3641 ≤ 43493393625573^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221459347 10000000000 43493393625573 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423077621/10000000000 : ℝ)^4665 ≤ (9131344634401/20000000000000 : ℝ)^3641 := by
    have hnat : (5423077621 : ℕ)^4665*20000000000000^3641 ≤ 9131344634401^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423077621 10000000000 9131344634401 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70666889/400000000 : ℝ), (5221459347/10000000000 : ℝ), (5423077621/10000000000 : ℝ)] ![(1084988318813/10000000000000 : ℝ), (43493393625573/100000000000000 : ℝ), (9131344634401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70666889/400000000 : ℝ)|^4665 ≤ (1084988318813/10000000000000 : ℝ)^3641
        have hw : |(-70666889/400000000 : ℝ)|=(70666889/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221459347/10000000000 : ℝ)|^4665 ≤ (43493393625573/100000000000000 : ℝ)^3641
        have hw : |(5221459347/10000000000 : ℝ)|=(5221459347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423077621/10000000000 : ℝ)|^4665 ≤ (9131344634401/20000000000000 : ℝ)^3641
        have hw : |(5423077621/10000000000 : ℝ)|=(5423077621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293361859/10000000000 : ℝ)*x 0 + (-417044567/2500000000 : ℝ)*x 1 + (2711538863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293361859/10000000000 : ℝ)^4665 ≤ (44262247559267/100000000000000 : ℝ)^3641 := by
    have hnat : (5293361859 : ℕ)^4665*100000000000000^3641 ≤ 44262247559267^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293361859 10000000000 44262247559267 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417044567/2500000000 : ℝ)^4665 ≤ (5040514059951/50000000000000 : ℝ)^3641 := by
    have hnat : (417044567 : ℕ)^4665*50000000000000^3641 ≤ 5040514059951^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417044567 2500000000 5040514059951 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711538863/5000000000 : ℝ)^4665 ≤ (11414181076153/25000000000000 : ℝ)^3641 := by
    have hnat : (2711538863 : ℕ)^4665*25000000000000^3641 ≤ 11414181076153^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711538863 5000000000 11414181076153 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293361859/10000000000 : ℝ), (-417044567/2500000000 : ℝ), (2711538863/5000000000 : ℝ)] ![(44262247559267/100000000000000 : ℝ), (5040514059951/50000000000000 : ℝ), (11414181076153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293361859/10000000000 : ℝ)|^4665 ≤ (44262247559267/100000000000000 : ℝ)^3641
        have hw : |(5293361859/10000000000 : ℝ)|=(5293361859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417044567/2500000000 : ℝ)|^4665 ≤ (5040514059951/50000000000000 : ℝ)^3641
        have hw : |(-417044567/2500000000 : ℝ)|=(417044567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711538863/5000000000 : ℝ)|^4665 ≤ (11414181076153/25000000000000 : ℝ)^3641
        have hw : |(2711538863/5000000000 : ℝ)|=(2711538863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293362161/10000000000 : ℝ)*x 0 + (1084615483/2000000000 : ℝ)*x 1 + (-1668178283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293362161/10000000000 : ℝ)^4665 ≤ (8852450158951/20000000000000 : ℝ)^3641 := by
    have hnat : (5293362161 : ℕ)^4665*20000000000000^3641 ≤ 8852450158951^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293362161 10000000000 8852450158951 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084615483/2000000000 : ℝ)^4665 ≤ (22828360474969/50000000000000 : ℝ)^3641 := by
    have hnat : (1084615483 : ℕ)^4665*50000000000000^3641 ≤ 22828360474969^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084615483 2000000000 22828360474969 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1668178283/10000000000 : ℝ)^4665 ≤ (5040514118021/50000000000000 : ℝ)^3641 := by
    have hnat : (1668178283 : ℕ)^4665*50000000000000^3641 ≤ 5040514118021^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668178283 10000000000 5040514118021 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293362161/10000000000 : ℝ), (1084615483/2000000000 : ℝ), (-1668178283/10000000000 : ℝ)] ![(8852450158951/20000000000000 : ℝ), (22828360474969/50000000000000 : ℝ), (5040514118021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293362161/10000000000 : ℝ)|^4665 ≤ (8852450158951/20000000000000 : ℝ)^3641
        have hw : |(5293362161/10000000000 : ℝ)|=(5293362161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084615483/2000000000 : ℝ)|^4665 ≤ (22828360474969/50000000000000 : ℝ)^3641
        have hw : |(1084615483/2000000000 : ℝ)|=(1084615483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1668178283/10000000000 : ℝ)|^4665 ≤ (5040514118021/50000000000000 : ℝ)^3641
        have hw : |(-1668178283/10000000000 : ℝ)|=(1668178283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s4_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237432011/10000000000 : ℝ)*x 0 + (4483186449/10000000000 : ℝ)*x 1 + (4002711871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237432011/10000000000 : ℝ)^4665 ≤ (33283469410043/100000000000000 : ℝ)^3641 := by
    have hnat : (4237432011 : ℕ)^4665*100000000000000^3641 ≤ 33283469410043^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237432011 10000000000 33283469410043 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483186449/10000000000 : ℝ)^4665 ≤ (35776559934547/100000000000000 : ℝ)^3641 := by
    have hnat : (4483186449 : ℕ)^4665*100000000000000^3641 ≤ 35776559934547^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483186449 10000000000 35776559934547 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4002711871/10000000000 : ℝ)^4665 ≤ (15469985319203/50000000000000 : ℝ)^3641 := by
    have hnat : (4002711871 : ℕ)^4665*50000000000000^3641 ≤ 15469985319203^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002711871 10000000000 15469985319203 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237432011/10000000000 : ℝ), (4483186449/10000000000 : ℝ), (4002711871/10000000000 : ℝ)] ![(33283469410043/100000000000000 : ℝ), (35776559934547/100000000000000 : ℝ), (15469985319203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237432011/10000000000 : ℝ)|^4665 ≤ (33283469410043/100000000000000 : ℝ)^3641
        have hw : |(4237432011/10000000000 : ℝ)|=(4237432011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483186449/10000000000 : ℝ)|^4665 ≤ (35776559934547/100000000000000 : ℝ)^3641
        have hw : |(4483186449/10000000000 : ℝ)|=(4483186449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4002711871/10000000000 : ℝ)|^4665 ≤ (15469985319203/50000000000000 : ℝ)^3641
        have hw : |(4002711871/10000000000 : ℝ)|=(4002711871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15513/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11163/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15513/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15513/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15513/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15513/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15513/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15513/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5569/50000 : ℝ) ^ (4663/1024 : ℝ) ≤ (71327271116827/1562500000000000000 : ℝ) := by
    have hpowers : (5569/50000 : ℝ)^4663 ≤ (71327271116827/1562500000000000000 : ℝ)^1024 := by
      have hnat : (5569 : ℕ)^4663*1562500000000000000^1024 ≤ 71327271116827^1024*50000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5569 50000 71327271116827 1562500000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5569/50000 : ℝ)) (X := (71327271116827/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15513/100000 : ℝ) ^ (4663/1024 : ℝ) ≤ (161232507737589/781250000000000000 : ℝ) := by
    have hpowers : (15513/100000 : ℝ)^4663 ≤ (161232507737589/781250000000000000 : ℝ)^1024 := by
      have hnat : (15513 : ℕ)^4663*781250000000000000^1024 ≤ 161232507737589^1024*100000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15513 100000 161232507737589 781250000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15513/100000 : ℝ)) (X := (161232507737589/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781321327271116827/781250000000000000 : ℝ) ≤ (10000200486275821/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (781321327271116827/781250000000000000 : ℝ)^1024 ≤ (10000200486275821/10000000000000000 : ℝ)^4663 := by
      have hnat : (781321327271116827 : ℕ)^1024*10000000000000000^4663 ≤ 10000200486275821^4663*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781321327271116827 781250000000000000 10000200486275821 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000200486275821/10000000000000000 : ℝ)) (X := (781321327271116827/781250000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (312578758457318401/312500000000000000 : ℝ) ≤ (5000276699911387/5000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (312578758457318401/312500000000000000 : ℝ)^1024 ≤ (5000276699911387/5000000000000000 : ℝ)^4663 := by
      have hnat : (312578758457318401 : ℕ)^1024*5000000000000000^4663 ≤ 5000276699911387^4663*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312578758457318401 312500000000000000 5000276699911387 5000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000276699911387/5000000000000000 : ℝ)) (X := (312578758457318401/312500000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (390786232507737589/390625000000000000 : ℝ) ≤ (10000906313369727/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (390786232507737589/390625000000000000 : ℝ)^1024 ≤ (10000906313369727/10000000000000000 : ℝ)^4663 := by
      have hnat : (390786232507737589 : ℕ)^1024*10000000000000000^4663 ≤ 10000906313369727^4663*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390786232507737589 390625000000000000 10000906313369727 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000906313369727/10000000000000000 : ℝ)) (X := (390786232507737589/390625000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(71327271116827/1562500000000000000 : ℝ) ≤ ((43743015625284791847/43750000000000000000 : ℝ)+2*(352913546953/437500000000000 : ℝ)*(5569/50000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (43743015625284791847/43750000000000000000 : ℝ)+2*(352913546953/437500000000000 : ℝ)*(5569/50000 : ℝ)=(10000200486275821/10000000000000000 : ℝ) by norm_num, show 1+2*(71327271116827/1562500000000000000 : ℝ)=(781321327271116827/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(161232507737589/781250000000000000 : ℝ)+(71327271116827/1562500000000000000 : ℝ) ≤ ((43743015625284791847/43750000000000000000 : ℝ)+(352913546953/437500000000000 : ℝ)*((15513/100000 : ℝ)+(5569/50000 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (43743015625284791847/43750000000000000000 : ℝ)+(352913546953/437500000000000 : ℝ)*((15513/100000 : ℝ)+(5569/50000 : ℝ))=(5000276699911387/5000000000000000 : ℝ) by norm_num, show 1+(161232507737589/781250000000000000 : ℝ)+(71327271116827/1562500000000000000 : ℝ)=(312578758457318401/312500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(161232507737589/781250000000000000 : ℝ) ≤ ((43743015625284791847/43750000000000000000 : ℝ)+2*(352913546953/437500000000000 : ℝ)*(15513/100000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (43743015625284791847/43750000000000000000 : ℝ)+2*(352913546953/437500000000000 : ℝ)*(15513/100000 : ℝ)=(10000906313369727/10000000000000000 : ℝ) by norm_num, show 1+2*(161232507737589/781250000000000000 : ℝ)=(390786232507737589/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43743015625284791847/43750000000000000000 : ℝ)*(X 1 0+X 2 0)+(352913546953/437500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (15513/100000 : ℝ)) (c := (43743015625284791847/43750000000000000000 : ℝ)) (alpha := (352913546953/437500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43743015625284791847/43750000000000000000 : ℝ)*(X 0 1+X 2 1)+(352913546953/437500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (15513/100000 : ℝ)) (c := (43743015625284791847/43750000000000000000 : ℝ)) (alpha := (352913546953/437500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43743015625284791847/43750000000000000000 : ℝ)*(X 0 2+X 1 2)+(352913546953/437500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (15513/100000 : ℝ)) (c := (43743015625284791847/43750000000000000000 : ℝ)) (alpha := (352913546953/437500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-883322877/5000000000 : ℝ)*X 0 0+(2712075361/5000000000 : ℝ)*X 0 1+(5220394207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347357103/10000000000 : ℝ)*X 1 0+(-935431183/5000000000 : ℝ)*X 1 1+(2610196841/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347357389/10000000000 : ℝ)*X 2 0+(2610196673/5000000000 : ℝ)*X 2 1+(-187086243/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((13241779/31250000 : ℝ)*X 0 0+(2000076687/5000000000 : ℝ)*X 0 1+(4485725981/10000000000 : ℝ)*X 0 2+(13241779/31250000 : ℝ)*X 1 0+(2000076687/5000000000 : ℝ)*X 1 1+(4485725981/10000000000 : ℝ)*X 1 2+(13241779/31250000 : ℝ)*X 2 0+(2000076687/5000000000 : ℝ)*X 2 1+(4485725981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-70666889/400000000 : ℝ)*X 0 0+(5221459347/10000000000 : ℝ)*X 0 1+(5423077621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293361859/10000000000 : ℝ)*X 1 0+(-417044567/2500000000 : ℝ)*X 1 1+(2711538863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293362161/10000000000 : ℝ)*X 2 0+(1084615483/2000000000 : ℝ)*X 2 1+(-1668178283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4237432011/10000000000 : ℝ)*X 0 0+(4483186449/10000000000 : ℝ)*X 0 1+(4002711871/10000000000 : ℝ)*X 0 2+(4237432011/10000000000 : ℝ)*X 1 0+(4483186449/10000000000 : ℝ)*X 1 1+(4002711871/10000000000 : ℝ)*X 1 2+(4237432011/10000000000 : ℝ)*X 2 0+(4483186449/10000000000 : ℝ)*X 2 1+(4002711871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10560258754900336176079223901/1093750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87491469/6250000000000 : ℝ)*(base19) + (725401207/50000000000000 : ℝ)*(base23) + (28281273/25000000000000 : ℝ)*(lower2) + (147530687/50000000000000 : ℝ)*(upper3) + (58856349/50000000000000 : ℝ)*(upper5) + (43545444054333/1250000000000 : ℝ)*(major0) + (43545444054333/1250000000000 : ℝ)*(major1) + (1741817762173321/50000000000000 : ℝ)*(major2) + (1226956504163757/25000000000000 : ℝ)*(sp0) + (4907830357621543/100000000000000 : ℝ)*(sp1) + (4907830306682633/100000000000000 : ℝ)*(sp2) + (1029714979729659/50000000000000 : ℝ)*(sp3) + (2870415009/50000000000000 : ℝ)*(sp4) + (1801982489/20000000000000 : ℝ)*(sp7) + (2059438969371763/100000000000000 : ℝ)*(f.failure) + (4907831757485047/100000000000000 : ℝ)*(f.sum) + (41393379662251/10937500000000000000000000000 : ℝ)*base66 + (1219780878304606949/54687500000000000000000000000000 : ℝ)*base68 + (1204242829094786113/2187500000000000000000000000000000 : ℝ)*base70 + (947841414671794449/54687500000000000000000000000000 : ℝ)*base72 + (7773591848313/5468750000000000000000000000 : ℝ)*base74 + (30417958286594786113/2187500000000000000000000000000000 : ℝ)*base76 + (1249704848195426949/54687500000000000000000000000000 : ℝ)*base78 + (1519888637890739449/54687500000000000000000000000000 : ℝ)*base80 + (13049131594459/4375000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (158470407/10000000000000000000000 : ℝ)*base89 + (158470407/10000000000000000000000 : ℝ)*base91 + (41529593/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143489539730498215130842743/27343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (176321043/25000000000000 : ℝ)*(base19) + (506377361/50000000000000 : ℝ)*(base23) + (19498209/20000000000000 : ℝ)*(upper3) + (14501621/100000000000000 : ℝ)*(lower4) + (9069291/6250000000000 : ℝ)*(upper5) + (44007165029573/1250000000000 : ℝ)*(major0) + (44007165029573/1250000000000 : ℝ)*(major1) + (44007165029573/1250000000000 : ℝ)*(major2) + (13685866647/100000000000000 : ℝ)*(sp1) + (1340169829/10000000000000 : ℝ)*(sp2) + (1239967655202087/25000000000000 : ℝ)*(sp4) + (495985622965753/10000000000000 : ℝ)*(sp5) + (4959856206355337/100000000000000 : ℝ)*(sp6) + (416255121800549/20000000000000 : ℝ)*(sp7) + (416255121800549/20000000000000 : ℝ)*(f.failure) + (1239967655202087/25000000000000 : ℝ)*(f.sum) + (4117739883521/4375000000000000000000000000 : ℝ)*base66 + (31283169175253831/54687500000000000000000000000000 : ℝ)*base67 + (237491425472128831/54687500000000000000000000000000 : ℝ)*base69 + (454928673910683669/54687500000000000000000000000000 : ℝ)*base72 + (3747627381479/4375000000000000000000000000 : ℝ)*base73 + (269774562668496169/54687500000000000000000000000000 : ℝ)*base76 + (197677369941933669/54687500000000000000000000000000 : ℝ)*base78 + (209602331395058669/54687500000000000000000000000000 : ℝ)*base80 + (1031758100263/546875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6069361/2000000000000000000000 : ℝ)*base89 + (6069361/2000000000000000000000 : ℝ)*base91 + (6069361/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1584_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15513/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1584_s5_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1766664303/10000000000 : ℝ)*x 0 + (5424026253/10000000000 : ℝ)*x 1 + (2610253173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1766664303/10000000000 : ℝ)^4665 ≤ (43399283411/400000000000 : ℝ)^3641 := by
    have hnat : (1766664303 : ℕ)^4665*400000000000^3641 ≤ 43399283411^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766664303 10000000000 43399283411 400000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424026253/10000000000 : ℝ)^4665 ≤ (45666956062811/100000000000000 : ℝ)^3641 := by
    have hnat : (5424026253 : ℕ)^4665*100000000000000^3641 ≤ 45666956062811^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424026253 10000000000 45666956062811 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610253173/5000000000 : ℝ)^4665 ≤ (8696644614489/20000000000000 : ℝ)^3641 := by
    have hnat : (2610253173 : ℕ)^4665*20000000000000^3641 ≤ 8696644614489^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610253173 5000000000 8696644614489 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1766664303/10000000000 : ℝ), (5424026253/10000000000 : ℝ), (2610253173/5000000000 : ℝ)] ![(43399283411/400000000000 : ℝ), (45666956062811/100000000000000 : ℝ), (8696644614489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1766664303/10000000000 : ℝ)|^4665 ≤ (43399283411/400000000000 : ℝ)^3641
        have hw : |(-1766664303/10000000000 : ℝ)|=(1766664303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424026253/10000000000 : ℝ)|^4665 ≤ (45666956062811/100000000000000 : ℝ)^3641
        have hw : |(5424026253/10000000000 : ℝ)|=(5424026253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610253173/5000000000 : ℝ)|^4665 ≤ (8696644614489/20000000000000 : ℝ)^3641
        have hw : |(2610253173/5000000000 : ℝ)|=(2610253173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534732407/1000000000 : ℝ)*x 0 + (-1870756391/10000000000 : ℝ)*x 1 + (2610253173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534732407/1000000000 : ℝ)^4665 ≤ (11210300104091/25000000000000 : ℝ)^3641 := by
    have hnat : (534732407 : ℕ)^4665*25000000000000^3641 ≤ 11210300104091^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534732407 1000000000 11210300104091 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870756391/10000000000 : ℝ)^4665 ≤ (11675576500547/100000000000000 : ℝ)^3641 := by
    have hnat : (1870756391 : ℕ)^4665*100000000000000^3641 ≤ 11675576500547^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870756391 10000000000 11675576500547 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610253173/5000000000 : ℝ)^4665 ≤ (8696644614489/20000000000000 : ℝ)^3641 := by
    have hnat : (2610253173 : ℕ)^4665*20000000000000^3641 ≤ 8696644614489^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610253173 5000000000 8696644614489 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534732407/1000000000 : ℝ), (-1870756391/10000000000 : ℝ), (2610253173/5000000000 : ℝ)] ![(11210300104091/25000000000000 : ℝ), (11675576500547/100000000000000 : ℝ), (8696644614489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534732407/1000000000 : ℝ)|^4665 ≤ (11210300104091/25000000000000 : ℝ)^3641
        have hw : |(534732407/1000000000 : ℝ)|=(534732407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870756391/10000000000 : ℝ)|^4665 ≤ (11675576500547/100000000000000 : ℝ)^3641
        have hw : |(-1870756391/10000000000 : ℝ)|=(1870756391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610253173/5000000000 : ℝ)|^4665 ≤ (8696644614489/20000000000000 : ℝ)^3641
        have hw : |(2610253173/5000000000 : ℝ)|=(2610253173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534732407/1000000000 : ℝ)*x 0 + (2610253173/5000000000 : ℝ)*x 1 + (-1870756391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534732407/1000000000 : ℝ)^4665 ≤ (11210300104091/25000000000000 : ℝ)^3641 := by
    have hnat : (534732407 : ℕ)^4665*25000000000000^3641 ≤ 11210300104091^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534732407 1000000000 11210300104091 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610253173/5000000000 : ℝ)^4665 ≤ (8696644614489/20000000000000 : ℝ)^3641 := by
    have hnat : (2610253173 : ℕ)^4665*20000000000000^3641 ≤ 8696644614489^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610253173 5000000000 8696644614489 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870756391/10000000000 : ℝ)^4665 ≤ (11675576500547/100000000000000 : ℝ)^3641 := by
    have hnat : (1870756391 : ℕ)^4665*100000000000000^3641 ≤ 11675576500547^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870756391 10000000000 11675576500547 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534732407/1000000000 : ℝ), (2610253173/5000000000 : ℝ), (-1870756391/10000000000 : ℝ)] ![(11210300104091/25000000000000 : ℝ), (8696644614489/20000000000000 : ℝ), (11675576500547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534732407/1000000000 : ℝ)|^4665 ≤ (11210300104091/25000000000000 : ℝ)^3641
        have hw : |(534732407/1000000000 : ℝ)|=(534732407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610253173/5000000000 : ℝ)|^4665 ≤ (8696644614489/20000000000000 : ℝ)^3641
        have hw : |(2610253173/5000000000 : ℝ)|=(2610253173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870756391/10000000000 : ℝ)|^4665 ≤ (11675576500547/100000000000000 : ℝ)^3641
        have hw : |(-1870756391/10000000000 : ℝ)|=(1870756391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423738079/1000000000 : ℝ)*x 0 + (400043517/1000000000 : ℝ)*x 1 + (4485441789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423738079/1000000000 : ℝ)^4665 ≤ (33282953939169/100000000000000 : ℝ)^3641 := by
    have hnat : (423738079 : ℕ)^4665*100000000000000^3641 ≤ 33282953939169^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423738079 1000000000 33282953939169 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400043517/1000000000 : ℝ)^4665 ≤ (30917424727167/100000000000000 : ℝ)^3641 := by
    have hnat : (400043517 : ℕ)^4665*100000000000000^3641 ≤ 30917424727167^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400043517 1000000000 30917424727167 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485441789/10000000000 : ℝ)^4665 ≤ (8949905331233/25000000000000 : ℝ)^3641 := by
    have hnat : (4485441789 : ℕ)^4665*25000000000000^3641 ≤ 8949905331233^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485441789 10000000000 8949905331233 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423738079/1000000000 : ℝ), (400043517/1000000000 : ℝ), (4485441789/10000000000 : ℝ)] ![(33282953939169/100000000000000 : ℝ), (30917424727167/100000000000000 : ℝ), (8949905331233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423738079/1000000000 : ℝ)|^4665 ≤ (33282953939169/100000000000000 : ℝ)^3641
        have hw : |(423738079/1000000000 : ℝ)|=(423738079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400043517/1000000000 : ℝ)|^4665 ≤ (30917424727167/100000000000000 : ℝ)^3641
        have hw : |(400043517/1000000000 : ℝ)|=(400043517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485441789/10000000000 : ℝ)|^4665 ≤ (8949905331233/25000000000000 : ℝ)^3641
        have hw : |(4485441789/10000000000 : ℝ)|=(4485441789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-353338121/2000000000 : ℝ)*x 0 + (5221569619/10000000000 : ℝ)*x 1 + (5422955109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353338121/2000000000 : ℝ)^4665 ≤ (1085002781407/10000000000000 : ℝ)^3641 := by
    have hnat : (353338121 : ℕ)^4665*10000000000000^3641 ≤ 1085002781407^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353338121 2000000000 1085002781407 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221569619/10000000000 : ℝ)^4665 ≤ (4349457049669/10000000000000 : ℝ)^3641 := by
    have hnat : (5221569619 : ℕ)^4665*10000000000000^3641 ≤ 4349457049669^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221569619 10000000000 4349457049669 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422955109/10000000000 : ℝ)^4665 ≤ (45655401672097/100000000000000 : ℝ)^3641 := by
    have hnat : (5422955109 : ℕ)^4665*100000000000000^3641 ≤ 45655401672097^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422955109 10000000000 45655401672097 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353338121/2000000000 : ℝ), (5221569619/10000000000 : ℝ), (5422955109/10000000000 : ℝ)] ![(1085002781407/10000000000000 : ℝ), (4349457049669/10000000000000 : ℝ), (45655401672097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353338121/2000000000 : ℝ)|^4665 ≤ (1085002781407/10000000000000 : ℝ)^3641
        have hw : |(-353338121/2000000000 : ℝ)|=(353338121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221569619/10000000000 : ℝ)|^4665 ≤ (4349457049669/10000000000000 : ℝ)^3641
        have hw : |(5221569619/10000000000 : ℝ)|=(5221569619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422955109/10000000000 : ℝ)|^4665 ≤ (45655401672097/100000000000000 : ℝ)^3641
        have hw : |(5422955109/10000000000 : ℝ)|=(5422955109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330836989/625000000 : ℝ)*x 0 + (-333661521/2000000000 : ℝ)*x 1 + (43383641/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330836989/625000000 : ℝ)^4665 ≤ (553282107383/1250000000000 : ℝ)^3641 := by
    have hnat : (330836989 : ℕ)^4665*1250000000000^3641 ≤ 553282107383^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330836989 625000000 553282107383 1250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333661521/2000000000 : ℝ)^4665 ≤ (10082029550493/100000000000000 : ℝ)^3641 := by
    have hnat : (333661521 : ℕ)^4665*100000000000000^3641 ≤ 10082029550493^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333661521 2000000000 10082029550493 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43383641/80000000 : ℝ)^4665 ≤ (11413850461171/25000000000000 : ℝ)^3641 := by
    have hnat : (43383641 : ℕ)^4665*25000000000000^3641 ≤ 11413850461171^3641*80000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43383641 80000000 11413850461171 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330836989/625000000 : ℝ), (-333661521/2000000000 : ℝ), (43383641/80000000 : ℝ)] ![(553282107383/1250000000000 : ℝ), (10082029550493/100000000000000 : ℝ), (11413850461171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330836989/625000000 : ℝ)|^4665 ≤ (553282107383/1250000000000 : ℝ)^3641
        have hw : |(330836989/625000000 : ℝ)|=(330836989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333661521/2000000000 : ℝ)|^4665 ≤ (10082029550493/100000000000000 : ℝ)^3641
        have hw : |(-333661521/2000000000 : ℝ)|=(333661521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43383641/80000000 : ℝ)|^4665 ≤ (11413850461171/25000000000000 : ℝ)^3641
        have hw : |(43383641/80000000 : ℝ)|=(43383641/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646695913/5000000000 : ℝ)*x 0 + (5422955127/10000000000 : ℝ)*x 1 + (-4170769/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646695913/5000000000 : ℝ)^4665 ≤ (44262568612067/100000000000000 : ℝ)^3641 := by
    have hnat : (2646695913 : ℕ)^4665*100000000000000^3641 ≤ 44262568612067^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646695913 5000000000 44262568612067 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422955127/10000000000 : ℝ)^4665 ≤ (45655401866257/100000000000000 : ℝ)^3641 := by
    have hnat : (5422955127 : ℕ)^4665*100000000000000^3641 ≤ 45655401866257^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422955127 10000000000 45655401866257 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170769/25000000 : ℝ)^4665 ≤ (10082029511779/100000000000000 : ℝ)^3641 := by
    have hnat : (4170769 : ℕ)^4665*100000000000000^3641 ≤ 10082029511779^3641*25000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170769 25000000 10082029511779 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646695913/5000000000 : ℝ), (5422955127/10000000000 : ℝ), (-4170769/25000000 : ℝ)] ![(44262568612067/100000000000000 : ℝ), (45655401866257/100000000000000 : ℝ), (10082029511779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646695913/5000000000 : ℝ)|^4665 ≤ (44262568612067/100000000000000 : ℝ)^3641
        have hw : |(2646695913/5000000000 : ℝ)|=(2646695913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422955127/10000000000 : ℝ)|^4665 ≤ (45655401866257/100000000000000 : ℝ)^3641
        have hw : |(5422955127/10000000000 : ℝ)|=(5422955127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4170769/25000000 : ℝ)|^4665 ≤ (10082029511779/100000000000000 : ℝ)^3641
        have hw : |(-4170769/25000000 : ℝ)|=(4170769/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s5_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847488689/2000000000 : ℝ)*x 0 + (1120726981/2500000000 : ℝ)*x 1 + (800597559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847488689/2000000000 : ℝ)^4665 ≤ (33283584478203/100000000000000 : ℝ)^3641 := by
    have hnat : (847488689 : ℕ)^4665*100000000000000^3641 ≤ 33283584478203^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847488689 2000000000 33283584478203 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120726981/2500000000 : ℝ)^4665 ≤ (4471714022023/12500000000000 : ℝ)^3641 := by
    have hnat : (1120726981 : ℕ)^4665*12500000000000^3641 ≤ 4471714022023^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120726981 2500000000 4471714022023 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800597559/2000000000 : ℝ)^4665 ≤ (6188540665501/20000000000000 : ℝ)^3641 := by
    have hnat : (800597559 : ℕ)^4665*20000000000000^3641 ≤ 6188540665501^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800597559 2000000000 6188540665501 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847488689/2000000000 : ℝ), (1120726981/2500000000 : ℝ), (800597559/2000000000 : ℝ)] ![(33283584478203/100000000000000 : ℝ), (4471714022023/12500000000000 : ℝ), (6188540665501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847488689/2000000000 : ℝ)|^4665 ≤ (33283584478203/100000000000000 : ℝ)^3641
        have hw : |(847488689/2000000000 : ℝ)|=(847488689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120726981/2500000000 : ℝ)|^4665 ≤ (4471714022023/12500000000000 : ℝ)^3641
        have hw : |(1120726981/2500000000 : ℝ)|=(1120726981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(800597559/2000000000 : ℝ)|^4665 ≤ (6188540665501/20000000000000 : ℝ)^3641
        have hw : |(800597559/2000000000 : ℝ)|=(800597559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11163/100000 : ℝ) ^ (4663/1024 : ℝ) ≤ (461179062467491/10000000000000000000 : ℝ) := by
    have hpowers : (11163/100000 : ℝ)^4663 ≤ (461179062467491/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11163 : ℕ)^4663*10000000000000000000^1024 ≤ 461179062467491^1024*100000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11163 100000 461179062467491 10000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11163/100000 : ℝ)) (X := (461179062467491/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4663/1024 : ℝ) ≤ (5118674741025569/25000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4663 ≤ (5118674741025569/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4663*25000000000000000000^1024 ≤ 5118674741025569^1024*50000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 5118674741025569 25000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (5118674741025569/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000461179062467491/5000000000000000000 : ℝ) ≤ (2000040508716667/2000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (5000461179062467491/5000000000000000000 : ℝ)^1024 ≤ (2000040508716667/2000000000000000 : ℝ)^4663 := by
      have hnat : (5000461179062467491 : ℕ)^1024*2000000000000000^4663 ≤ 2000040508716667^4663*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000461179062467491 5000000000000000000 2000040508716667 2000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000040508716667/2000000000000000 : ℝ)) (X := (5000461179062467491/5000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012543244794388593/50000000000000000000 : ℝ) ≤ (2500137712047651/2500000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (50012543244794388593/50000000000000000000 : ℝ)^1024 ≤ (2500137712047651/2500000000000000 : ℝ)^4663 := by
      have hnat : (50012543244794388593 : ℕ)^1024*2500000000000000^4663 ≤ 2500137712047651^4663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012543244794388593 50000000000000000000 2500137712047651 2500000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500137712047651/2500000000000000 : ℝ)) (X := (50012543244794388593/50000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505118674741025569/12500000000000000000 : ℝ) ≤ (10000899152797873/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (12505118674741025569/12500000000000000000 : ℝ)^1024 ≤ (10000899152797873/10000000000000000 : ℝ)^4663 := by
      have hnat : (12505118674741025569 : ℕ)^1024*10000000000000000^4663 ≤ 10000899152797873^4663*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505118674741025569 12500000000000000000 10000899152797873 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000899152797873/10000000000000000 : ℝ)) (X := (12505118674741025569/12500000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461179062467491/10000000000000000000 : ℝ) ≤ ((14407699782416289837/14410000000000000000 : ℝ)+2*(348304607269/432300000000000 : ℝ)*(11163/100000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (14407699782416289837/14410000000000000000 : ℝ)+2*(348304607269/432300000000000 : ℝ)*(11163/100000 : ℝ)=(2000040508716667/2000000000000000 : ℝ) by norm_num, show 1+2*(461179062467491/10000000000000000000 : ℝ)=(5000461179062467491/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5118674741025569/25000000000000000000 : ℝ)+(461179062467491/10000000000000000000 : ℝ) ≤ ((14407699782416289837/14410000000000000000 : ℝ)+(348304607269/432300000000000 : ℝ)*((7743/50000 : ℝ)+(11163/100000 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (14407699782416289837/14410000000000000000 : ℝ)+(348304607269/432300000000000 : ℝ)*((7743/50000 : ℝ)+(11163/100000 : ℝ))=(2500137712047651/2500000000000000 : ℝ) by norm_num, show 1+(5118674741025569/25000000000000000000 : ℝ)+(461179062467491/10000000000000000000 : ℝ)=(50012543244794388593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5118674741025569/25000000000000000000 : ℝ) ≤ ((14407699782416289837/14410000000000000000 : ℝ)+2*(348304607269/432300000000000 : ℝ)*(7743/50000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (14407699782416289837/14410000000000000000 : ℝ)+2*(348304607269/432300000000000 : ℝ)*(7743/50000 : ℝ)=(10000899152797873/10000000000000000 : ℝ) by norm_num, show 1+2*(5118674741025569/25000000000000000000 : ℝ)=(12505118674741025569/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14407699782416289837/14410000000000000000 : ℝ)*(X 1 0+X 2 0)+(348304607269/432300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (14407699782416289837/14410000000000000000 : ℝ)) (alpha := (348304607269/432300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14407699782416289837/14410000000000000000 : ℝ)*(X 0 1+X 2 1)+(348304607269/432300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (14407699782416289837/14410000000000000000 : ℝ)) (alpha := (348304607269/432300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14407699782416289837/14410000000000000000 : ℝ)*(X 0 2+X 1 2)+(348304607269/432300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (14407699782416289837/14410000000000000000 : ℝ)) (alpha := (348304607269/432300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1766664303/10000000000 : ℝ)*X 0 0+(5424026253/10000000000 : ℝ)*X 0 1+(2610253173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534732407/1000000000 : ℝ)*X 1 0+(-1870756391/10000000000 : ℝ)*X 1 1+(2610253173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534732407/1000000000 : ℝ)*X 2 0+(2610253173/5000000000 : ℝ)*X 2 1+(-1870756391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((423738079/1000000000 : ℝ)*X 0 0+(400043517/1000000000 : ℝ)*X 0 1+(4485441789/10000000000 : ℝ)*X 0 2+(423738079/1000000000 : ℝ)*X 1 0+(400043517/1000000000 : ℝ)*X 1 1+(4485441789/10000000000 : ℝ)*X 1 2+(423738079/1000000000 : ℝ)*X 2 0+(400043517/1000000000 : ℝ)*X 2 1+(4485441789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-353338121/2000000000 : ℝ)*X 0 0+(5221569619/10000000000 : ℝ)*X 0 1+(5422955109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330836989/625000000 : ℝ)*X 1 0+(-333661521/2000000000 : ℝ)*X 1 1+(43383641/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646695913/5000000000 : ℝ)*X 2 0+(5422955127/10000000000 : ℝ)*X 2 1+(-4170769/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((847488689/2000000000 : ℝ)*X 0 0+(1120726981/2500000000 : ℝ)*X 0 1+(800597559/2000000000 : ℝ)*X 0 2+(847488689/2000000000 : ℝ)*X 1 0+(1120726981/2500000000 : ℝ)*X 1 1+(800597559/2000000000 : ℝ)*X 1 2+(847488689/2000000000 : ℝ)*X 2 0+(1120726981/2500000000 : ℝ)*X 2 1+(800597559/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2250387608455872359640103691/720500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32820791/6250000000000 : ℝ)*(base19) + (489916831/100000000000000 : ℝ)*(base23) + (9415521/50000000000000 : ℝ)*(lower2) + (19276649/25000000000000 : ℝ)*(upper3) + (51883209/100000000000000 : ℝ)*(upper5) + (348768839356019/10000000000000 : ℝ)*(major0) + (348768839356019/10000000000000 : ℝ)*(major1) + (3487688393560191/100000000000000 : ℝ)*(major2) + (307095823060571/6250000000000 : ℝ)*(sp0) + (245677061634371/5000000000000 : ℝ)*(sp1) + (982708253580649/20000000000000 : ℝ)*(sp2) + (2061831015714871/100000000000000 : ℝ)*(sp3) + (8588850941/100000000000000 : ℝ)*(sp4) + (488684139/12500000000000 : ℝ)*(sp7) + (128864682824249/6250000000000 : ℝ)*(f.failure) + (1228385439455019/25000000000000 : ℝ)*(f.sum) + (31608793712579/43230000000000000000000000000 : ℝ)*base65 + (790905192462091097/144100000000000000000000000000000 : ℝ)*base68 + (6714858666376160309/393000000000000000000000000000000 : ℝ)*base70 + (665255307590591097/144100000000000000000000000000000 : ℝ)*base72 + (171283457307749/43230000000000000000000000000 : ℝ)*base73 + (50687985511160309/393000000000000000000000000000000 : ℝ)*base76 + (5746169339169463291/432300000000000000000000000000000 : ℝ)*base78 + (5240666317920136709/432300000000000000000000000000000 : ℝ)*base79 + (136735260613/86460000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11328661/625000000000000000000 : ℝ)*base89 + (11328661/625000000000000000000 : ℝ)*base91 + (5078661/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8572873847564407780410426419/720500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373957697/20000000000000 : ℝ)*(base19) + (80736507/4000000000000 : ℝ)*(base23) + (38503731/6250000000000 : ℝ)*(lower1) + (15480987/6250000000000 : ℝ)*(upper3) + (65284699/100000000000000 : ℝ)*(lower4) + (30363703/12500000000000 : ℝ)*(upper5) + (3524618206664629/100000000000000 : ℝ)*(major0) + (3524618206664629/100000000000000 : ℝ)*(major1) + (3524618206664629/100000000000000 : ℝ)*(major2) + (287276963/12500000000000 : ℝ)*(sp2) + (4965569101436053/100000000000000 : ℝ)*(sp4) + (4965567231647567/100000000000000 : ℝ)*(sp5) + (4965564784807673/100000000000000 : ℝ)*(sp6) + (416733383055263/20000000000000 : ℝ)*(sp7) + (416733383055263/20000000000000 : ℝ)*(f.failure) + (4965569101436053/100000000000000 : ℝ)*(f.sum) + (44405377434449/21615000000000000000000000000 : ℝ)*base66 + (98835889742060673581/4323000000000000000000000000000000 : ℝ)*base68 + (42395974111734326419/4323000000000000000000000000000000 : ℝ)*base69 + (81218383041728673581/4323000000000000000000000000000000 : ℝ)*base72 + (43169778173587/10807500000000000000000000000 : ℝ)*base74 + (56182631689919673581/4323000000000000000000000000000000 : ℝ)*base76 + (3768310344038673581/4323000000000000000000000000000000 : ℝ)*base78 + (6657962606835326419/4323000000000000000000000000000000 : ℝ)*base79 + (65103827622593/10807500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2948093/2000000000000000000000 : ℝ)*base90 + (2948093/2000000000000000000000 : ℝ)*base92 + (2948093/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1584_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1584_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (493/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1584_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1584_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1584_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (493/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1584_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

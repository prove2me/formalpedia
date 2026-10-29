-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1547_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:22.736428+00:00
-- url     : https://prove2.me/submissions/80bed368-c76d-4928-9bc5-ab3207e0b6b5

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
theorem support_rectangle_w1547_s3_0 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1817194547/10000000000 : ℝ)*x 0 + (5430905073/10000000000 : ℝ)*x 1 + (5217246417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1817194547/10000000000 : ℝ)^4591 ≤ (5568822453359/50000000000000 : ℝ)^3567 := by
    have hnat : (1817194547 : ℕ)^4591*50000000000000^3567 ≤ 5568822453359^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817194547 10000000000 5568822453359 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430905073/10000000000 : ℝ)^4591 ≤ (11394634586681/25000000000000 : ℝ)^3567 := by
    have hnat : (5430905073 : ℕ)^4591*25000000000000^3567 ≤ 11394634586681^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430905073 10000000000 11394634586681 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217246417/10000000000 : ℝ)^4591 ≤ (338154818279/781250000000 : ℝ)^3567 := by
    have hnat : (5217246417 : ℕ)^4591*781250000000^3567 ≤ 338154818279^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217246417 10000000000 338154818279 781250000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1817194547/10000000000 : ℝ), (5430905073/10000000000 : ℝ), (5217246417/10000000000 : ℝ)] ![(5568822453359/50000000000000 : ℝ), (11394634586681/25000000000000 : ℝ), (338154818279/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1817194547/10000000000 : ℝ)|^4591 ≤ (5568822453359/50000000000000 : ℝ)^3567
        have hw : |(-1817194547/10000000000 : ℝ)|=(1817194547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430905073/10000000000 : ℝ)|^4591 ≤ (11394634586681/25000000000000 : ℝ)^3567
        have hw : |(5430905073/10000000000 : ℝ)|=(5430905073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217246417/10000000000 : ℝ)|^4591 ≤ (338154818279/781250000000 : ℝ)^3567
        have hw : |(5217246417/10000000000 : ℝ)|=(5217246417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_1 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350155471/10000000000 : ℝ)*x 0 + (-481648847/2500000000 : ℝ)*x 1 + (5217246399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350155471/10000000000 : ℝ)^4591 ≤ (5588521625069/12500000000000 : ℝ)^3567 := by
    have hnat : (5350155471 : ℕ)^4591*12500000000000^3567 ≤ 5588521625069^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350155471 10000000000 5588521625069 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481648847/2500000000 : ℝ)^4591 ≤ (12008010445497/100000000000000 : ℝ)^3567 := by
    have hnat : (481648847 : ℕ)^4591*100000000000000^3567 ≤ 12008010445497^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481648847 2500000000 12008010445497 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217246399/10000000000 : ℝ)^4591 ≤ (43283816547509/100000000000000 : ℝ)^3567 := by
    have hnat : (5217246399 : ℕ)^4591*100000000000000^3567 ≤ 43283816547509^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217246399 10000000000 43283816547509 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350155471/10000000000 : ℝ), (-481648847/2500000000 : ℝ), (5217246399/10000000000 : ℝ)] ![(5588521625069/12500000000000 : ℝ), (12008010445497/100000000000000 : ℝ), (43283816547509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350155471/10000000000 : ℝ)|^4591 ≤ (5588521625069/12500000000000 : ℝ)^3567
        have hw : |(5350155471/10000000000 : ℝ)|=(5350155471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-481648847/2500000000 : ℝ)|^4591 ≤ (12008010445497/100000000000000 : ℝ)^3567
        have hw : |(-481648847/2500000000 : ℝ)|=(481648847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217246399/10000000000 : ℝ)|^4591 ≤ (43283816547509/100000000000000 : ℝ)^3567
        have hw : |(5217246399/10000000000 : ℝ)|=(5217246399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_2 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350155523/10000000000 : ℝ)*x 0 + (1304311593/2500000000 : ℝ)*x 1 + (-1926595353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350155523/10000000000 : ℝ)^4591 ≤ (4470817355983/10000000000000 : ℝ)^3567 := by
    have hnat : (5350155523 : ℕ)^4591*10000000000000^3567 ≤ 4470817355983^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350155523 10000000000 4470817355983 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304311593/2500000000 : ℝ)^4591 ≤ (10820954064801/25000000000000 : ℝ)^3567 := by
    have hnat : (1304311593 : ℕ)^4591*25000000000000^3567 ≤ 10820954064801^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304311593 2500000000 10820954064801 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926595353/10000000000 : ℝ)^4591 ≤ (6004005082363/50000000000000 : ℝ)^3567 := by
    have hnat : (1926595353 : ℕ)^4591*50000000000000^3567 ≤ 6004005082363^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926595353 10000000000 6004005082363 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350155523/10000000000 : ℝ), (1304311593/2500000000 : ℝ), (-1926595353/10000000000 : ℝ)] ![(4470817355983/10000000000000 : ℝ), (10820954064801/25000000000000 : ℝ), (6004005082363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350155523/10000000000 : ℝ)|^4591 ≤ (4470817355983/10000000000000 : ℝ)^3567
        have hw : |(5350155523/10000000000 : ℝ)|=(5350155523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304311593/2500000000 : ℝ)|^4591 ≤ (10820954064801/25000000000000 : ℝ)^3567
        have hw : |(1304311593/2500000000 : ℝ)|=(1304311593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926595353/10000000000 : ℝ)|^4591 ≤ (6004005082363/50000000000000 : ℝ)^3567
        have hw : |(-1926595353/10000000000 : ℝ)|=(1926595353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_3 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126769891/5000000000 : ℝ)*x 0 + (200564203/500000000 : ℝ)*x 1 + (450774583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126769891/5000000000 : ℝ)^4591 ≤ (33279261998037/100000000000000 : ℝ)^3567 := by
    have hnat : (2126769891 : ℕ)^4591*100000000000000^3567 ≤ 33279261998037^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126769891 5000000000 33279261998037 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200564203/500000000 : ℝ)^4591 ≤ (3085997844593/10000000000000 : ℝ)^3567 := by
    have hnat : (200564203 : ℕ)^4591*10000000000000^3567 ≤ 3085997844593^3567*500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200564203 500000000 3085997844593 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450774583/1000000000 : ℝ)^4591 ≤ (17930379768887/50000000000000 : ℝ)^3567 := by
    have hnat : (450774583 : ℕ)^4591*50000000000000^3567 ≤ 17930379768887^3567*1000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450774583 1000000000 17930379768887 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126769891/5000000000 : ℝ), (200564203/500000000 : ℝ), (450774583/1000000000 : ℝ)] ![(33279261998037/100000000000000 : ℝ), (3085997844593/10000000000000 : ℝ), (17930379768887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126769891/5000000000 : ℝ)|^4591 ≤ (33279261998037/100000000000000 : ℝ)^3567
        have hw : |(2126769891/5000000000 : ℝ)|=(2126769891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200564203/500000000 : ℝ)|^4591 ≤ (3085997844593/10000000000000 : ℝ)^3567
        have hw : |(200564203/500000000 : ℝ)|=(200564203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450774583/1000000000 : ℝ)|^4591 ≤ (17930379768887/50000000000000 : ℝ)^3567
        have hw : |(450774583/1000000000 : ℝ)|=(450774583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_4 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-908611733/5000000000 : ℝ)*x 0 + (2609188097/5000000000 : ℝ)*x 1 + (5429767049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908611733/5000000000 : ℝ)^4591 ≤ (11137873035661/100000000000000 : ℝ)^3567 := by
    have hnat : (908611733 : ℕ)^4591*100000000000000^3567 ≤ 11137873035661^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908611733 5000000000 11137873035661 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609188097/5000000000 : ℝ)^4591 ≤ (43295880830889/100000000000000 : ℝ)^3567 := by
    have hnat : (2609188097 : ℕ)^4591*100000000000000^3567 ≤ 43295880830889^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609188097 5000000000 43295880830889 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429767049/10000000000 : ℝ)^4591 ≤ (9113249223089/20000000000000 : ℝ)^3567 := by
    have hnat : (5429767049 : ℕ)^4591*20000000000000^3567 ≤ 9113249223089^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429767049 10000000000 9113249223089 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-908611733/5000000000 : ℝ), (2609188097/5000000000 : ℝ), (5429767049/10000000000 : ℝ)] ![(11137873035661/100000000000000 : ℝ), (43295880830889/100000000000000 : ℝ), (9113249223089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-908611733/5000000000 : ℝ)|^4591 ≤ (11137873035661/100000000000000 : ℝ)^3567
        have hw : |(-908611733/5000000000 : ℝ)|=(908611733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609188097/5000000000 : ℝ)|^4591 ≤ (43295880830889/100000000000000 : ℝ)^3567
        have hw : |(2609188097/5000000000 : ℝ)|=(2609188097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429767049/10000000000 : ℝ)|^4591 ≤ (9113249223089/20000000000000 : ℝ)^3567
        have hw : |(5429767049/10000000000 : ℝ)|=(5429767049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_5 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293788971/10000000000 : ℝ)*x 0 + (-1714074831/10000000000 : ℝ)*x 1 + (5429767427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293788971/10000000000 : ℝ)^4591 ≤ (44102850437257/100000000000000 : ℝ)^3567 := by
    have hnat : (5293788971 : ℕ)^4591*100000000000000^3567 ≤ 44102850437257^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293788971 10000000000 44102850437257 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714074831/10000000000 : ℝ)^4591 ≤ (41323597379/400000000000 : ℝ)^3567 := by
    have hnat : (1714074831 : ℕ)^4591*400000000000^3567 ≤ 41323597379^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714074831 10000000000 41323597379 400000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429767427/10000000000 : ℝ)^4591 ≤ (11391562549561/25000000000000 : ℝ)^3567 := by
    have hnat : (5429767427 : ℕ)^4591*25000000000000^3567 ≤ 11391562549561^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429767427 10000000000 11391562549561 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293788971/10000000000 : ℝ), (-1714074831/10000000000 : ℝ), (5429767427/10000000000 : ℝ)] ![(44102850437257/100000000000000 : ℝ), (41323597379/400000000000 : ℝ), (11391562549561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293788971/10000000000 : ℝ)|^4591 ≤ (44102850437257/100000000000000 : ℝ)^3567
        have hw : |(5293788971/10000000000 : ℝ)|=(5293788971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714074831/10000000000 : ℝ)|^4591 ≤ (41323597379/400000000000 : ℝ)^3567
        have hw : |(-1714074831/10000000000 : ℝ)|=(1714074831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429767427/10000000000 : ℝ)|^4591 ≤ (11391562549561/25000000000000 : ℝ)^3567
        have hw : |(5429767427/10000000000 : ℝ)|=(5429767427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_6 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293789699/10000000000 : ℝ)*x 0 + (108595341/200000000 : ℝ)*x 1 + (-1714074349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293789699/10000000000 : ℝ)^4591 ≤ (5512857280423/12500000000000 : ℝ)^3567 := by
    have hnat : (5293789699 : ℕ)^4591*12500000000000^3567 ≤ 5512857280423^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293789699 10000000000 5512857280423 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108595341/200000000 : ℝ)^4591 ≤ (22783123063123/50000000000000 : ℝ)^3567 := by
    have hnat : (108595341 : ℕ)^4591*50000000000000^3567 ≤ 22783123063123^3567*200000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108595341 200000000 22783123063123 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1714074349/10000000000 : ℝ)^4591 ≤ (2066179121143/20000000000000 : ℝ)^3567 := by
    have hnat : (1714074349 : ℕ)^4591*20000000000000^3567 ≤ 2066179121143^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714074349 10000000000 2066179121143 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293789699/10000000000 : ℝ), (108595341/200000000 : ℝ), (-1714074349/10000000000 : ℝ)] ![(5512857280423/12500000000000 : ℝ), (22783123063123/50000000000000 : ℝ), (2066179121143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293789699/10000000000 : ℝ)|^4591 ≤ (5512857280423/12500000000000 : ℝ)^3567
        have hw : |(5293789699/10000000000 : ℝ)|=(5293789699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108595341/200000000 : ℝ)|^4591 ≤ (22783123063123/50000000000000 : ℝ)^3567
        have hw : |(108595341/200000000 : ℝ)|=(108595341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1714074349/10000000000 : ℝ)|^4591 ≤ (2066179121143/20000000000000 : ℝ)^3567
        have hw : |(-1714074349/10000000000 : ℝ)|=(1714074349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s3_7 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063401887/2500000000 : ℝ)*x 0 + (563140231/1250000000 : ℝ)*x 1 + (1003482009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063401887/2500000000 : ℝ)^4591 ≤ (33279944399919/100000000000000 : ℝ)^3567 := by
    have hnat : (1063401887 : ℕ)^4591*100000000000000^3567 ≤ 33279944399919^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063401887 2500000000 33279944399919 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563140231/1250000000 : ℝ)^4591 ≤ (35833894416539/100000000000000 : ℝ)^3567 := by
    have hnat : (563140231 : ℕ)^4591*100000000000000^3567 ≤ 35833894416539^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563140231 1250000000 35833894416539 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003482009/2500000000 : ℝ)^4591 ≤ (7721540294677/25000000000000 : ℝ)^3567 := by
    have hnat : (1003482009 : ℕ)^4591*25000000000000^3567 ≤ 7721540294677^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003482009 2500000000 7721540294677 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063401887/2500000000 : ℝ), (563140231/1250000000 : ℝ), (1003482009/2500000000 : ℝ)] ![(33279944399919/100000000000000 : ℝ), (35833894416539/100000000000000 : ℝ), (7721540294677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063401887/2500000000 : ℝ)|^4591 ≤ (33279944399919/100000000000000 : ℝ)^3567
        have hw : |(1063401887/2500000000 : ℝ)|=(1063401887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563140231/1250000000 : ℝ)|^4591 ≤ (35833894416539/100000000000000 : ℝ)^3567
        have hw : |(563140231/1250000000 : ℝ)|=(563140231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003482009/2500000000 : ℝ)|^4591 ≤ (7721540294677/25000000000000 : ℝ)^3567
        have hw : |(1003482009/2500000000 : ℝ)|=(1003482009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1547_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1553/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10683/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10683/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10683/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10683/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10683/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10683/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10683/100000 : ℝ) ^ (4589/1024 : ℝ) ≤ (4437535305670661/100000000000000000000 : ℝ) := by
    have hpowers : (10683/100000 : ℝ)^4589 ≤ (4437535305670661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10683 : ℕ)^4589*100000000000000000000^1024 ≤ 4437535305670661^1024*100000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10683 100000 4437535305670661 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10683/100000 : ℝ)) (X := (4437535305670661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15877/100000 : ℝ) ^ (4589/1024 : ℝ) ≤ (5239833521659863/20000000000000000000 : ℝ) := by
    have hpowers : (15877/100000 : ℝ)^4589 ≤ (5239833521659863/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15877 : ℕ)^4589*20000000000000000000^1024 ≤ 5239833521659863^1024*100000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15877 100000 5239833521659863 20000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15877/100000 : ℝ)) (X := (5239833521659863/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004437535305670661/50000000000000000000 : ℝ) ≤ (2500049508384323/2500000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50004437535305670661/50000000000000000000 : ℝ)^1024 ≤ (2500049508384323/2500000000000000 : ℝ)^4589 := by
      have hnat : (50004437535305670661 : ℕ)^1024*2500000000000000^4589 ≤ 2500049508384323^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004437535305670661 50000000000000000000 2500049508384323 2500000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500049508384323/2500000000000000 : ℝ)) (X := (50004437535305670661/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503829587864246247/12500000000000000000 : ℝ) ≤ (10000683553086487/10000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (12503829587864246247/12500000000000000000 : ℝ)^1024 ≤ (10000683553086487/10000000000000000 : ℝ)^4589 := by
      have hnat : (12503829587864246247 : ℕ)^1024*10000000000000000^4589 ≤ 10000683553086487^4589*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503829587864246247 12500000000000000000 10000683553086487 10000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683553086487/10000000000000000 : ℝ)) (X := (12503829587864246247/12500000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005239833521659863/10000000000000000000 : ℝ) ≤ (5000584536317841/5000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (10005239833521659863/10000000000000000000 : ℝ)^1024 ≤ (5000584536317841/5000000000000000 : ℝ)^4589 := by
      have hnat : (10005239833521659863 : ℕ)^1024*5000000000000000^4589 ≤ 5000584536317841^4589*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005239833521659863 10000000000000000000 5000584536317841 5000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000584536317841/5000000000000000 : ℝ)) (X := (10005239833521659863/10000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4437535305670661/100000000000000000000 : ℝ) ≤ ((25965327487752297139/25970000000000000000 : ℝ)+2*(97103909839/103880000000000 : ℝ)*(10683/100000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (25965327487752297139/25970000000000000000 : ℝ)+2*(97103909839/103880000000000 : ℝ)*(10683/100000 : ℝ)=(2500049508384323/2500000000000000 : ℝ) by norm_num, show 1+2*(4437535305670661/100000000000000000000 : ℝ)=(50004437535305670661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5239833521659863/20000000000000000000 : ℝ)+(4437535305670661/100000000000000000000 : ℝ) ≤ ((25965327487752297139/25970000000000000000 : ℝ)+(97103909839/103880000000000 : ℝ)*((15877/100000 : ℝ)+(10683/100000 : ℝ)))^(4589/1024 : ℝ) := by
    rw [show (25965327487752297139/25970000000000000000 : ℝ)+(97103909839/103880000000000 : ℝ)*((15877/100000 : ℝ)+(10683/100000 : ℝ))=(10000683553086487/10000000000000000 : ℝ) by norm_num, show 1+(5239833521659863/20000000000000000000 : ℝ)+(4437535305670661/100000000000000000000 : ℝ)=(12503829587864246247/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5239833521659863/20000000000000000000 : ℝ) ≤ ((25965327487752297139/25970000000000000000 : ℝ)+2*(97103909839/103880000000000 : ℝ)*(15877/100000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (25965327487752297139/25970000000000000000 : ℝ)+2*(97103909839/103880000000000 : ℝ)*(15877/100000 : ℝ)=(5000584536317841/5000000000000000 : ℝ) by norm_num, show 1+2*(5239833521659863/20000000000000000000 : ℝ)=(10005239833521659863/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25965327487752297139/25970000000000000000 : ℝ)*(X 1 0+X 2 0)+(97103909839/103880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (10683/100000 : ℝ)) (hi := (15877/100000 : ℝ)) (c := (25965327487752297139/25970000000000000000 : ℝ)) (alpha := (97103909839/103880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25965327487752297139/25970000000000000000 : ℝ)*(X 0 1+X 2 1)+(97103909839/103880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (10683/100000 : ℝ)) (hi := (15877/100000 : ℝ)) (c := (25965327487752297139/25970000000000000000 : ℝ)) (alpha := (97103909839/103880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25965327487752297139/25970000000000000000 : ℝ)*(X 0 2+X 1 2)+(97103909839/103880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (10683/100000 : ℝ)) (hi := (15877/100000 : ℝ)) (c := (25965327487752297139/25970000000000000000 : ℝ)) (alpha := (97103909839/103880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1817194547/10000000000 : ℝ)*X 0 0+(5430905073/10000000000 : ℝ)*X 0 1+(5217246417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350155471/10000000000 : ℝ)*X 1 0+(-481648847/2500000000 : ℝ)*X 1 1+(5217246399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350155523/10000000000 : ℝ)*X 2 0+(1304311593/2500000000 : ℝ)*X 2 1+(-1926595353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2126769891/5000000000 : ℝ)*X 0 0+(200564203/500000000 : ℝ)*X 0 1+(450774583/1000000000 : ℝ)*X 0 2+(2126769891/5000000000 : ℝ)*X 1 0+(200564203/500000000 : ℝ)*X 1 1+(450774583/1000000000 : ℝ)*X 1 2+(2126769891/5000000000 : ℝ)*X 2 0+(200564203/500000000 : ℝ)*X 2 1+(450774583/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-908611733/5000000000 : ℝ)*X 0 0+(2609188097/5000000000 : ℝ)*X 0 1+(5429767049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293788971/10000000000 : ℝ)*X 1 0+(-1714074831/10000000000 : ℝ)*X 1 1+(5429767427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293789699/10000000000 : ℝ)*X 2 0+(108595341/200000000 : ℝ)*X 2 1+(-1714074349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1063401887/2500000000 : ℝ)*X 0 0+(563140231/1250000000 : ℝ)*X 0 1+(1003482009/2500000000 : ℝ)*X 0 2+(1063401887/2500000000 : ℝ)*X 1 0+(563140231/1250000000 : ℝ)*X 1 1+(1003482009/2500000000 : ℝ)*X 1 2+(1063401887/2500000000 : ℝ)*X 2 0+(563140231/1250000000 : ℝ)*X 2 1+(1003482009/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9516107766048982640803405167/1298500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1256352127/100000000000000 : ℝ)*(base19) + (613930271/50000000000000 : ℝ)*(base23) + (4947691/12500000000000 : ℝ)*(lower2) + (158645773/100000000000000 : ℝ)*(upper3) + (72699739/50000000000000 : ℝ)*(upper5) + (3347337032896249/100000000000000 : ℝ)*(major0) + (3347337032896249/100000000000000 : ℝ)*(major1) + (3347337032896249/100000000000000 : ℝ)*(major2) + (4680382267684869/100000000000000 : ℝ)*(sp0) + (4680401424022199/100000000000000 : ℝ)*(sp1) + (4680401452513783/100000000000000 : ℝ)*(sp2) + (2014262173055507/100000000000000 : ℝ)*(sp3) + (20412689457/100000000000000 : ℝ)*(sp4) + (8968078029/100000000000000 : ℝ)*(sp7) + (62945973160423/3125000000000 : ℝ)*(f.failure) + (2340201340187163/50000000000000 : ℝ)*(f.sum) + (2719236787077/5194000000000000000000000000 : ℝ)*base65 + (3831285925394718389/2597000000000000000000000000000000 : ℝ)*base68 + (17029764492344281611/2597000000000000000000000000000000 : ℝ)*base69 + (16220099165769281611/2597000000000000000000000000000000 : ℝ)*base71 + (4254880600711/5194000000000000000000000000 : ℝ)*base73 + (27288416124750718389/2597000000000000000000000000000000 : ℝ)*base76 + (17399727256109281611/2597000000000000000000000000000000 : ℝ)*base77 + (28122933958548281611/2597000000000000000000000000000000 : ℝ)*base79 + (22733685266641/5194000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (52253/62500000000000000000 : ℝ)*base89 + (52253/62500000000000000000 : ℝ)*base91 + (52253/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4571043619254460740888883809/1298500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61621317/50000000000000 : ℝ)*(base23) + (44044699/20000000000000 : ℝ)*(lower2) + (8790113/10000000000000 : ℝ)*(upper4) + (7548297/12500000000000 : ℝ)*(lower5) + (3383224038646941/100000000000000 : ℝ)*(major0) + (3383224038646941/100000000000000 : ℝ)*(major1) + (3383224038646941/100000000000000 : ℝ)*(major2) + (525877337/6250000000000 : ℝ)*(sp1) + (2711122267/20000000000000 : ℝ)*(sp2) + (2945553207/100000000000000 : ℝ)*(sp3) + (4730581694301831/100000000000000 : ℝ)*(sp4) + (4730573280264439/100000000000000 : ℝ)*(sp5) + (4730568015447861/100000000000000 : ℝ)*(sp6) + (407172664019439/20000000000000 : ℝ)*(sp7) + (1017933132825201/50000000000000 : ℝ)*(f.failure) + (4730581694301831/100000000000000 : ℝ)*(f.sum) + (10767263269827/5194000000000000000000000000 : ℝ)*base65 + (12830666413852151799/2597000000000000000000000000000000 : ℝ)*base67 + (23976225454517151799/2597000000000000000000000000000000 : ℝ)*base69 + (7588947471175151799/2597000000000000000000000000000000 : ℝ)*base71 + (5260733085749/5194000000000000000000000000 : ℝ)*base73 + (12892714724743151799/2597000000000000000000000000000000 : ℝ)*base75 + (18299071188804151799/2597000000000000000000000000000000 : ℝ)*base77 + (54173360014620151799/2597000000000000000000000000000000 : ℝ)*base79 + (1277900491563/1038800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3446589/1000000000000000000000 : ℝ)*base90 + (3446589/1000000000000000000000 : ℝ)*base92 + (3446589/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1547_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1553/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1547_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1547_s4_0 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-908744593/5000000000 : ℝ)*x 0 + (5428950147/10000000000 : ℝ)*x 1 + (1043801227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908744593/5000000000 : ℝ)^4591 ≤ (5569984614819/50000000000000 : ℝ)^3567 := by
    have hnat : (908744593 : ℕ)^4591*50000000000000^3567 ≤ 5569984614819^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908744593 5000000000 5569984614819 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428950147/10000000000 : ℝ)^4591 ≤ (11389355725337/25000000000000 : ℝ)^3567 := by
    have hnat : (5428950147 : ℕ)^4591*25000000000000^3567 ≤ 11389355725337^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428950147 10000000000 11389355725337 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043801227/2000000000 : ℝ)^4591 ≤ (21651303925911/50000000000000 : ℝ)^3567 := by
    have hnat : (1043801227 : ℕ)^4591*50000000000000^3567 ≤ 21651303925911^3567*2000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043801227 2000000000 21651303925911 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-908744593/5000000000 : ℝ), (5428950147/10000000000 : ℝ), (1043801227/2000000000 : ℝ)] ![(5569984614819/50000000000000 : ℝ), (11389355725337/25000000000000 : ℝ), (21651303925911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-908744593/5000000000 : ℝ)|^4591 ≤ (5569984614819/50000000000000 : ℝ)^3567
        have hw : |(-908744593/5000000000 : ℝ)|=(908744593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428950147/10000000000 : ℝ)|^4591 ≤ (11389355725337/25000000000000 : ℝ)^3567
        have hw : |(5428950147/10000000000 : ℝ)|=(5428950147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043801227/2000000000 : ℝ)|^4591 ≤ (21651303925911/50000000000000 : ℝ)^3567
        have hw : |(1043801227/2000000000 : ℝ)|=(1043801227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_1 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668704939/1250000000 : ℝ)*x 0 + (-24061811/125000000 : ℝ)*x 1 + (521900583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668704939/1250000000 : ℝ)^4591 ≤ (22351311877873/50000000000000 : ℝ)^3567 := by
    have hnat : (668704939 : ℕ)^4591*50000000000000^3567 ≤ 22351311877873^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668704939 1250000000 22351311877873 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24061811/125000000 : ℝ)^4591 ≤ (374836613619/3125000000000 : ℝ)^3567 := by
    have hnat : (24061811 : ℕ)^4591*3125000000000^3567 ≤ 374836613619^3567*125000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24061811 125000000 374836613619 3125000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521900583/1000000000 : ℝ)^4591 ≤ (5412825574341/12500000000000 : ℝ)^3567 := by
    have hnat : (521900583 : ℕ)^4591*12500000000000^3567 ≤ 5412825574341^3567*1000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521900583 1000000000 5412825574341 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668704939/1250000000 : ℝ), (-24061811/125000000 : ℝ), (521900583/1000000000 : ℝ)] ![(22351311877873/50000000000000 : ℝ), (374836613619/3125000000000 : ℝ), (5412825574341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668704939/1250000000 : ℝ)|^4591 ≤ (22351311877873/50000000000000 : ℝ)^3567
        have hw : |(668704939/1250000000 : ℝ)|=(668704939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24061811/125000000 : ℝ)|^4591 ≤ (374836613619/3125000000000 : ℝ)^3567
        have hw : |(-24061811/125000000 : ℝ)|=(24061811/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521900583/1000000000 : ℝ)|^4591 ≤ (5412825574341/12500000000000 : ℝ)^3567
        have hw : |(521900583/1000000000 : ℝ)|=(521900583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_2 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337409903/2500000000 : ℝ)*x 0 + (2609503097/5000000000 : ℝ)*x 1 + (-962472131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337409903/2500000000 : ℝ)^4591 ≤ (44702624831251/100000000000000 : ℝ)^3567 := by
    have hnat : (1337409903 : ℕ)^4591*100000000000000^3567 ≤ 44702624831251^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337409903 2500000000 44702624831251 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609503097/5000000000 : ℝ)^4591 ≤ (21651304240941/50000000000000 : ℝ)^3567 := by
    have hnat : (2609503097 : ℕ)^4591*50000000000000^3567 ≤ 21651304240941^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609503097 5000000000 21651304240941 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962472131/5000000000 : ℝ)^4591 ≤ (11994766679409/100000000000000 : ℝ)^3567 := by
    have hnat : (962472131 : ℕ)^4591*100000000000000^3567 ≤ 11994766679409^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962472131 5000000000 11994766679409 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337409903/2500000000 : ℝ), (2609503097/5000000000 : ℝ), (-962472131/5000000000 : ℝ)] ![(44702624831251/100000000000000 : ℝ), (21651304240941/50000000000000 : ℝ), (11994766679409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337409903/2500000000 : ℝ)|^4591 ≤ (44702624831251/100000000000000 : ℝ)^3567
        have hw : |(1337409903/2500000000 : ℝ)|=(1337409903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609503097/5000000000 : ℝ)|^4591 ≤ (21651304240941/50000000000000 : ℝ)^3567
        have hw : |(2609503097/5000000000 : ℝ)|=(2609503097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-962472131/5000000000 : ℝ)|^4591 ≤ (11994766679409/100000000000000 : ℝ)^3567
        have hw : |(-962472131/5000000000 : ℝ)|=(962472131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_3 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126862259/5000000000 : ℝ)*x 0 + (501947421/1250000000 : ℝ)*x 1 + (4503409101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126862259/5000000000 : ℝ)^4591 ≤ (33281122292161/100000000000000 : ℝ)^3567 := by
    have hnat : (2126862259 : ℕ)^4591*100000000000000^3567 ≤ 33281122292161^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126862259 5000000000 33281122292161 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501947421/1250000000 : ℝ)^4591 ≤ (7725629120239/25000000000000 : ℝ)^3567 := by
    have hnat : (501947421 : ℕ)^4591*25000000000000^3567 ≤ 7725629120239^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501947421 1250000000 7725629120239 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503409101/10000000000 : ℝ)^4591 ≤ (8954090304357/25000000000000 : ℝ)^3567 := by
    have hnat : (4503409101 : ℕ)^4591*25000000000000^3567 ≤ 8954090304357^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503409101 10000000000 8954090304357 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126862259/5000000000 : ℝ), (501947421/1250000000 : ℝ), (4503409101/10000000000 : ℝ)] ![(33281122292161/100000000000000 : ℝ), (7725629120239/25000000000000 : ℝ), (8954090304357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126862259/5000000000 : ℝ)|^4591 ≤ (33281122292161/100000000000000 : ℝ)^3567
        have hw : |(2126862259/5000000000 : ℝ)|=(2126862259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501947421/1250000000 : ℝ)|^4591 ≤ (7725629120239/25000000000000 : ℝ)^3567
        have hw : |(501947421/1250000000 : ℝ)|=(501947421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503409101/10000000000 : ℝ)|^4591 ≤ (8954090304357/25000000000000 : ℝ)^3567
        have hw : |(4503409101/10000000000 : ℝ)|=(4503409101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_4 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1817517023/10000000000 : ℝ)*x 0 + (1305024137/2500000000 : ℝ)*x 1 + (5427851613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1817517023/10000000000 : ℝ)^4591 ≤ (11140188833373/100000000000000 : ℝ)^3567 := by
    have hnat : (1817517023 : ℕ)^4591*100000000000000^3567 ≤ 11140188833373^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817517023 10000000000 11140188833373 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305024137/2500000000 : ℝ)^4591 ≤ (21657126358599/50000000000000 : ℝ)^3567 := by
    have hnat : (1305024137 : ℕ)^4591*50000000000000^3567 ≤ 21657126358599^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305024137 2500000000 21657126358599 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427851613/10000000000 : ℝ)^4591 ≤ (45545558430679/100000000000000 : ℝ)^3567 := by
    have hnat : (5427851613 : ℕ)^4591*100000000000000^3567 ≤ 45545558430679^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427851613 10000000000 45545558430679 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1817517023/10000000000 : ℝ), (1305024137/2500000000 : ℝ), (5427851613/10000000000 : ℝ)] ![(11140188833373/100000000000000 : ℝ), (21657126358599/50000000000000 : ℝ), (45545558430679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1817517023/10000000000 : ℝ)|^4591 ≤ (11140188833373/100000000000000 : ℝ)^3567
        have hw : |(-1817517023/10000000000 : ℝ)|=(1817517023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305024137/2500000000 : ℝ)|^4591 ≤ (21657126358599/50000000000000 : ℝ)^3567
        have hw : |(1305024137/2500000000 : ℝ)|=(1305024137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427851613/10000000000 : ℝ)|^4591 ≤ (45545558430679/100000000000000 : ℝ)^3567
        have hw : |(5427851613/10000000000 : ℝ)|=(5427851613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_5 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294254163/10000000000 : ℝ)*x 0 + (-1716098839/10000000000 : ℝ)*x 1 + (1085570323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294254163/10000000000 : ℝ)^4591 ≤ (44107838615151/100000000000000 : ℝ)^3567 := by
    have hnat : (5294254163 : ℕ)^4591*100000000000000^3567 ≤ 44107838615151^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294254163 10000000000 44107838615151 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716098839/10000000000 : ℝ)^4591 ≤ (10346602912879/100000000000000 : ℝ)^3567 := by
    have hnat : (1716098839 : ℕ)^4591*100000000000000^3567 ≤ 10346602912879^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716098839 10000000000 10346602912879 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085570323/2000000000 : ℝ)^4591 ≤ (45545558452279/100000000000000 : ℝ)^3567 := by
    have hnat : (1085570323 : ℕ)^4591*100000000000000^3567 ≤ 45545558452279^3567*2000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085570323 2000000000 45545558452279 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294254163/10000000000 : ℝ), (-1716098839/10000000000 : ℝ), (1085570323/2000000000 : ℝ)] ![(44107838615151/100000000000000 : ℝ), (10346602912879/100000000000000 : ℝ), (45545558452279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294254163/10000000000 : ℝ)|^4591 ≤ (44107838615151/100000000000000 : ℝ)^3567
        have hw : |(5294254163/10000000000 : ℝ)|=(5294254163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716098839/10000000000 : ℝ)|^4591 ≤ (10346602912879/100000000000000 : ℝ)^3567
        have hw : |(-1716098839/10000000000 : ℝ)|=(1716098839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085570323/2000000000 : ℝ)|^4591 ≤ (45545558452279/100000000000000 : ℝ)^3567
        have hw : |(1085570323/2000000000 : ℝ)|=(1085570323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_6 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294253993/10000000000 : ℝ)*x 0 + (5427851671/10000000000 : ℝ)*x 1 + (-429024749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294253993/10000000000 : ℝ)^4591 ≤ (22053918396123/50000000000000 : ℝ)^3567 := by
    have hnat : (5294253993 : ℕ)^4591*50000000000000^3567 ≤ 22053918396123^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294253993 10000000000 22053918396123 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427851671/10000000000 : ℝ)^4591 ≤ (45545559057077/100000000000000 : ℝ)^3567 := by
    have hnat : (5427851671 : ℕ)^4591*100000000000000^3567 ≤ 45545559057077^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427851671 10000000000 45545559057077 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429024749/2500000000 : ℝ)^4591 ≤ (10346604131193/100000000000000 : ℝ)^3567 := by
    have hnat : (429024749 : ℕ)^4591*100000000000000^3567 ≤ 10346604131193^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429024749 2500000000 10346604131193 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294253993/10000000000 : ℝ), (5427851671/10000000000 : ℝ), (-429024749/2500000000 : ℝ)] ![(22053918396123/50000000000000 : ℝ), (45545559057077/100000000000000 : ℝ), (10346604131193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294253993/10000000000 : ℝ)|^4591 ≤ (22053918396123/50000000000000 : ℝ)^3567
        have hw : |(5294253993/10000000000 : ℝ)|=(5294253993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427851671/10000000000 : ℝ)|^4591 ≤ (45545559057077/100000000000000 : ℝ)^3567
        have hw : |(5427851671/10000000000 : ℝ)|=(5427851671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429024749/2500000000 : ℝ)|^4591 ≤ (10346604131193/100000000000000 : ℝ)^3567
        have hw : |(-429024749/2500000000 : ℝ)|=(429024749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s4_7 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531723647/1250000000 : ℝ)*x 0 + (1125218811/2500000000 : ℝ)*x 1 + (4018131831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531723647/1250000000 : ℝ)^4591 ≤ (33281773404613/100000000000000 : ℝ)^3567 := by
    have hnat : (531723647 : ℕ)^4591*100000000000000^3567 ≤ 33281773404613^3567*1250000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531723647 1250000000 33281773404613 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125218811/2500000000 : ℝ)^4591 ≤ (3579042591811/10000000000000 : ℝ)^3567 := by
    have hnat : (1125218811 : ℕ)^4591*10000000000000^3567 ≤ 3579042591811^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125218811 2500000000 3579042591811 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018131831/10000000000 : ℝ)^4591 ≤ (15463900330899/50000000000000 : ℝ)^3567 := by
    have hnat : (4018131831 : ℕ)^4591*50000000000000^3567 ≤ 15463900330899^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018131831 10000000000 15463900330899 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531723647/1250000000 : ℝ), (1125218811/2500000000 : ℝ), (4018131831/10000000000 : ℝ)] ![(33281773404613/100000000000000 : ℝ), (3579042591811/10000000000000 : ℝ), (15463900330899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531723647/1250000000 : ℝ)|^4591 ≤ (33281773404613/100000000000000 : ℝ)^3567
        have hw : |(531723647/1250000000 : ℝ)|=(531723647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125218811/2500000000 : ℝ)|^4591 ≤ (3579042591811/10000000000000 : ℝ)^3567
        have hw : |(1125218811/2500000000 : ℝ)|=(1125218811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018131831/10000000000 : ℝ)|^4591 ≤ (15463900330899/50000000000000 : ℝ)^3567
        have hw : |(4018131831/10000000000 : ℝ)|=(4018131831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1547_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1553/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (69/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1553/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1553/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1553/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1553/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1553/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1553/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5501/50000 : ℝ) ^ (4589/1024 : ℝ) ≤ (202519836575271/4000000000000000000 : ℝ) := by
    have hpowers : (5501/50000 : ℝ)^4589 ≤ (202519836575271/4000000000000000000 : ℝ)^1024 := by
      have hnat : (5501 : ℕ)^4589*4000000000000000000^1024 ≤ 202519836575271^1024*50000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5501 50000 202519836575271 4000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5501/50000 : ℝ)) (X := (202519836575271/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1553/10000 : ℝ) ^ (4589/1024 : ℝ) ≤ (23728982260240641/100000000000000000000 : ℝ) := by
    have hpowers : (1553/10000 : ℝ)^4589 ≤ (23728982260240641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1553 : ℕ)^4589*100000000000000000000^1024 ≤ 23728982260240641^1024*10000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1553 10000 23728982260240641 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1553/10000 : ℝ)) (X := (23728982260240641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000202519836575271/2000000000000000000 : ℝ) ≤ (5000112972410331/5000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (2000202519836575271/2000000000000000000 : ℝ)^1024 ≤ (5000112972410331/5000000000000000 : ℝ)^4589 := by
      have hnat : (2000202519836575271 : ℕ)^1024*5000000000000000^4589 ≤ 5000112972410331^4589*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000202519836575271 2000000000000000000 5000112972410331 5000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000112972410331/5000000000000000 : ℝ)) (X := (2000202519836575271/2000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251799498635913901/6250000000000000000 : ℝ) ≤ (10000642398974581/10000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (6251799498635913901/6250000000000000000 : ℝ)^1024 ≤ (10000642398974581/10000000000000000 : ℝ)^4589 := by
      have hnat : (6251799498635913901 : ℕ)^1024*10000000000000000^4589 ≤ 10000642398974581^4589*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251799498635913901 6250000000000000000 10000642398974581 10000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000642398974581/10000000000000000 : ℝ)) (X := (6251799498635913901/6250000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023728982260240641/50000000000000000000 : ℝ) ≤ (20002117706257/20000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50023728982260240641/50000000000000000000 : ℝ)^1024 ≤ (20002117706257/20000000000000 : ℝ)^4589 := by
      have hnat : (50023728982260240641 : ℕ)^1024*20000000000000^4589 ≤ 20002117706257^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023728982260240641 50000000000000000000 20002117706257 20000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20002117706257/20000000000000 : ℝ)) (X := (50023728982260240641/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(202519836575271/4000000000000000000 : ℝ) ≤ ((2263592971047256193/2264000000000000000 : ℝ)+2*(416454153919/452800000000000 : ℝ)*(5501/50000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (2263592971047256193/2264000000000000000 : ℝ)+2*(416454153919/452800000000000 : ℝ)*(5501/50000 : ℝ)=(5000112972410331/5000000000000000 : ℝ) by norm_num, show 1+2*(202519836575271/4000000000000000000 : ℝ)=(2000202519836575271/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23728982260240641/100000000000000000000 : ℝ)+(202519836575271/4000000000000000000 : ℝ) ≤ ((2263592971047256193/2264000000000000000 : ℝ)+(416454153919/452800000000000 : ℝ)*((1553/10000 : ℝ)+(5501/50000 : ℝ)))^(4589/1024 : ℝ) := by
    rw [show (2263592971047256193/2264000000000000000 : ℝ)+(416454153919/452800000000000 : ℝ)*((1553/10000 : ℝ)+(5501/50000 : ℝ))=(10000642398974581/10000000000000000 : ℝ) by norm_num, show 1+(23728982260240641/100000000000000000000 : ℝ)+(202519836575271/4000000000000000000 : ℝ)=(6251799498635913901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23728982260240641/100000000000000000000 : ℝ) ≤ ((2263592971047256193/2264000000000000000 : ℝ)+2*(416454153919/452800000000000 : ℝ)*(1553/10000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (2263592971047256193/2264000000000000000 : ℝ)+2*(416454153919/452800000000000 : ℝ)*(1553/10000 : ℝ)=(20002117706257/20000000000000 : ℝ) by norm_num, show 1+2*(23728982260240641/100000000000000000000 : ℝ)=(50023728982260240641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2263592971047256193/2264000000000000000 : ℝ)*(X 1 0+X 2 0)+(416454153919/452800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (1553/10000 : ℝ)) (c := (2263592971047256193/2264000000000000000 : ℝ)) (alpha := (416454153919/452800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2263592971047256193/2264000000000000000 : ℝ)*(X 0 1+X 2 1)+(416454153919/452800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (1553/10000 : ℝ)) (c := (2263592971047256193/2264000000000000000 : ℝ)) (alpha := (416454153919/452800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2263592971047256193/2264000000000000000 : ℝ)*(X 0 2+X 1 2)+(416454153919/452800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (1553/10000 : ℝ)) (c := (2263592971047256193/2264000000000000000 : ℝ)) (alpha := (416454153919/452800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-908744593/5000000000 : ℝ)*X 0 0+(5428950147/10000000000 : ℝ)*X 0 1+(1043801227/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668704939/1250000000 : ℝ)*X 1 0+(-24061811/125000000 : ℝ)*X 1 1+(521900583/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337409903/2500000000 : ℝ)*X 2 0+(2609503097/5000000000 : ℝ)*X 2 1+(-962472131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2126862259/5000000000 : ℝ)*X 0 0+(501947421/1250000000 : ℝ)*X 0 1+(4503409101/10000000000 : ℝ)*X 0 2+(2126862259/5000000000 : ℝ)*X 1 0+(501947421/1250000000 : ℝ)*X 1 1+(4503409101/10000000000 : ℝ)*X 1 2+(2126862259/5000000000 : ℝ)*X 2 0+(501947421/1250000000 : ℝ)*X 2 1+(4503409101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1817517023/10000000000 : ℝ)*X 0 0+(1305024137/2500000000 : ℝ)*X 0 1+(5427851613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294254163/10000000000 : ℝ)*X 1 0+(-1716098839/10000000000 : ℝ)*X 1 1+(1085570323/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294253993/10000000000 : ℝ)*X 2 0+(5427851671/10000000000 : ℝ)*X 2 1+(-429024749/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((531723647/1250000000 : ℝ)*X 0 0+(1125218811/2500000000 : ℝ)*X 0 1+(4018131831/10000000000 : ℝ)*X 0 2+(531723647/1250000000 : ℝ)*X 1 0+(1125218811/2500000000 : ℝ)*X 1 1+(4018131831/10000000000 : ℝ)*X 1 2+(531723647/1250000000 : ℝ)*X 2 0+(1125218811/2500000000 : ℝ)*X 2 1+(4018131831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158801582067505580904463659/28300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240869693/100000000000000 : ℝ)*(base19) + (101164573/25000000000000 : ℝ)*(base23) + (9398339/50000000000000 : ℝ)*(lower2) + (161373177/100000000000000 : ℝ)*(upper5) + (1703271276875979/50000000000000 : ℝ)*(major0) + (1703271276875979/50000000000000 : ℝ)*(major1) + (1703271276875979/50000000000000 : ℝ)*(major2) + (4763177489262627/100000000000000 : ℝ)*(sp0) + (4763175806312099/100000000000000 : ℝ)*(sp1) + (952637251297557/20000000000000 : ℝ)*(sp2) + (512474371891977/25000000000000 : ℝ)*(sp3) + (183437669/2000000000000 : ℝ)*(sp4) + (5306982143/50000000000000 : ℝ)*(sp5) + (385872239/50000000000000 : ℝ)*(sp7) + (409979651862477/20000000000000 : ℝ)*(f.failure) + (4763186661146077/100000000000000 : ℝ)*(f.sum) + (3207945711701/11320000000000000000000000000 : ℝ)*base65 + (617076048865192947/113200000000000000000000000000000 : ℝ)*base67 + (551202718901992947/113200000000000000000000000000000 : ℝ)*base69 + (163505696489592947/113200000000000000000000000000000 : ℝ)*base71 + (3511998625061/11320000000000000000000000000 : ℝ)*base73 + (1510206226543992947/113200000000000000000000000000000 : ℝ)*base75 + (647179738384792947/113200000000000000000000000000000 : ℝ)*base77 + (155372849712007053/113200000000000000000000000000000 : ℝ)*base80 + (32040867486219/11320000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3445353/400000000000000000000 : ℝ)*base90 + (3445353/400000000000000000000 : ℝ)*base92 + (3445353/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (351212780396571022567566003/28300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1666114667/100000000000000 : ℝ)*(base19) + (390228687/25000000000000 : ℝ)*(base23) + (19695709/10000000000000 : ℝ)*(upper3) + (54744469/100000000000000 : ℝ)*(lower4) + (309425603/100000000000000 : ℝ)*(upper5) + (860606728873057/25000000000000 : ℝ)*(major0) + (860606728873057/25000000000000 : ℝ)*(major1) + (860606728873057/25000000000000 : ℝ)*(major2) + (13545351931/50000000000000 : ℝ)*(sp1) + (43848909/200000000000 : ℝ)*(sp2) + (962672324903807/20000000000000 : ℝ)*(sp4) + (962666573540101/20000000000000 : ℝ)*(sp5) + (2406669069574893/50000000000000 : ℝ)*(sp6) + (2071491792787227/100000000000000 : ℝ)*(sp7) + (2071491792787227/100000000000000 : ℝ)*(f.failure) + (962672324903807/20000000000000 : ℝ)*(f.sum) + (19454011291637/5660000000000000000000000000 : ℝ)*base66 + (278608954392792999/56600000000000000000000000000000 : ℝ)*base68 + (112780945651192999/56600000000000000000000000000000 : ℝ)*base70 + (403457406626592999/56600000000000000000000000000000 : ℝ)*base72 + (8864406427603/5660000000000000000000000000 : ℝ)*base73 + (594259033320807001/56600000000000000000000000000000 : ℝ)*base75 + (503976329286007001/56600000000000000000000000000000 : ℝ)*base77 + (10708375584392999/56600000000000000000000000000000 : ℝ)*base80 + (13409168840077/5660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5323103/2000000000000000000000 : ℝ)*base90 + (5323103/2000000000000000000000 : ℝ)*base92 + (5323103/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1547_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1553/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1547_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1547_s5_0 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-454379927/2500000000 : ℝ)*x 0 + (2714369301/5000000000 : ℝ)*x 1 + (5219197539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454379927/2500000000 : ℝ)^4591 ≤ (5570105007581/50000000000000 : ℝ)^3567 := by
    have hnat : (454379927 : ℕ)^4591*50000000000000^3567 ≤ 5570105007581^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454379927 2500000000 5570105007581 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714369301/5000000000 : ℝ)^4591 ≤ (45555138103323/100000000000000 : ℝ)^3567 := by
    have hnat : (2714369301 : ℕ)^4591*100000000000000^3567 ≤ 45555138103323^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714369301 5000000000 45555138103323 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219197539/10000000000 : ℝ)^4591 ≤ (676635185393/1562500000000 : ℝ)^3567 := by
    have hnat : (5219197539 : ℕ)^4591*1562500000000^3567 ≤ 676635185393^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219197539 10000000000 676635185393 1562500000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-454379927/2500000000 : ℝ), (2714369301/5000000000 : ℝ), (5219197539/10000000000 : ℝ)] ![(5570105007581/50000000000000 : ℝ), (45555138103323/100000000000000 : ℝ), (676635185393/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-454379927/2500000000 : ℝ)|^4591 ≤ (5570105007581/50000000000000 : ℝ)^3567
        have hw : |(-454379927/2500000000 : ℝ)|=(454379927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714369301/5000000000 : ℝ)|^4591 ≤ (45555138103323/100000000000000 : ℝ)^3567
        have hw : |(2714369301/5000000000 : ℝ)|=(2714369301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219197539/10000000000 : ℝ)|^4591 ≤ (676635185393/1562500000000 : ℝ)^3567
        have hw : |(5219197539/10000000000 : ℝ)|=(5219197539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_1 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349584831/10000000000 : ℝ)*x 0 + (-1924763269/10000000000 : ℝ)*x 1 + (521919729/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349584831/10000000000 : ℝ)^4591 ≤ (22351017829693/50000000000000 : ℝ)^3567 := by
    have hnat : (5349584831 : ℕ)^4591*50000000000000^3567 ≤ 22351017829693^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349584831 10000000000 22351017829693 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924763269/10000000000 : ℝ)^4591 ≤ (2998328780893/25000000000000 : ℝ)^3567 := by
    have hnat : (1924763269 : ℕ)^4591*25000000000000^3567 ≤ 2998328780893^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924763269 10000000000 2998328780893 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521919729/1000000000 : ℝ)^4591 ≤ (21652324603027/50000000000000 : ℝ)^3567 := by
    have hnat : (521919729 : ℕ)^4591*50000000000000^3567 ≤ 21652324603027^3567*1000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521919729 1000000000 21652324603027 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349584831/10000000000 : ℝ), (-1924763269/10000000000 : ℝ), (521919729/1000000000 : ℝ)] ![(22351017829693/50000000000000 : ℝ), (2998328780893/25000000000000 : ℝ), (21652324603027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349584831/10000000000 : ℝ)|^4591 ≤ (22351017829693/50000000000000 : ℝ)^3567
        have hw : |(5349584831/10000000000 : ℝ)|=(5349584831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924763269/10000000000 : ℝ)|^4591 ≤ (2998328780893/25000000000000 : ℝ)^3567
        have hw : |(-1924763269/10000000000 : ℝ)|=(1924763269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521919729/1000000000 : ℝ)|^4591 ≤ (21652324603027/50000000000000 : ℝ)^3567
        have hw : |(521919729/1000000000 : ℝ)|=(521919729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_2 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349584887/10000000000 : ℝ)*x 0 + (1304799299/2500000000 : ℝ)*x 1 + (-1924763319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349584887/10000000000 : ℝ)^4591 ≤ (11175509065417/25000000000000 : ℝ)^3567 := by
    have hnat : (5349584887 : ℕ)^4591*25000000000000^3567 ≤ 11175509065417^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349584887 10000000000 11175509065417 25000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304799299/2500000000 : ℝ)^4591 ≤ (21652324101109/50000000000000 : ℝ)^3567 := by
    have hnat : (1304799299 : ℕ)^4591*50000000000000^3567 ≤ 21652324101109^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304799299 2500000000 21652324101109 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924763319/10000000000 : ℝ)^4591 ≤ (2398663104913/20000000000000 : ℝ)^3567 := by
    have hnat : (1924763319 : ℕ)^4591*20000000000000^3567 ≤ 2398663104913^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924763319 10000000000 2398663104913 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349584887/10000000000 : ℝ), (1304799299/2500000000 : ℝ), (-1924763319/10000000000 : ℝ)] ![(11175509065417/25000000000000 : ℝ), (21652324101109/50000000000000 : ℝ), (2398663104913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349584887/10000000000 : ℝ)|^4591 ≤ (11175509065417/25000000000000 : ℝ)^3567
        have hw : |(5349584887/10000000000 : ℝ)|=(5349584887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304799299/2500000000 : ℝ)|^4591 ≤ (21652324101109/50000000000000 : ℝ)^3567
        have hw : |(1304799299/2500000000 : ℝ)|=(1304799299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1924763319/10000000000 : ℝ)|^4591 ≤ (2398663104913/20000000000000 : ℝ)^3567
        have hw : |(-1924763319/10000000000 : ℝ)|=(1924763319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_3 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850748913/2000000000 : ℝ)*x 0 + (1004011301/2500000000 : ℝ)*x 1 + (1125734653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850748913/2000000000 : ℝ)^4591 ≤ (33281324167129/100000000000000 : ℝ)^3567 := by
    have hnat : (850748913 : ℕ)^4591*100000000000000^3567 ≤ 33281324167129^3567*2000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850748913 2000000000 33281324167129 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004011301/2500000000 : ℝ)^4591 ≤ (30907130613813/100000000000000 : ℝ)^3567 := by
    have hnat : (1004011301 : ℕ)^4591*100000000000000^3567 ≤ 30907130613813^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004011301 2500000000 30907130613813 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125734653/2500000000 : ℝ)^4591 ≤ (3581154520937/10000000000000 : ℝ)^3567 := by
    have hnat : (1125734653 : ℕ)^4591*10000000000000^3567 ≤ 3581154520937^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125734653 2500000000 3581154520937 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850748913/2000000000 : ℝ), (1004011301/2500000000 : ℝ), (1125734653/2500000000 : ℝ)] ![(33281324167129/100000000000000 : ℝ), (30907130613813/100000000000000 : ℝ), (3581154520937/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850748913/2000000000 : ℝ)|^4591 ≤ (33281324167129/100000000000000 : ℝ)^3567
        have hw : |(850748913/2000000000 : ℝ)|=(850748913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004011301/2500000000 : ℝ)|^4591 ≤ (30907130613813/100000000000000 : ℝ)^3567
        have hw : |(1004011301/2500000000 : ℝ)|=(1004011301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125734653/2500000000 : ℝ)|^4591 ≤ (3581154520937/10000000000000 : ℝ)^3567
        have hw : |(1125734653/2500000000 : ℝ)|=(1125734653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_4 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1817546609/10000000000 : ℝ)*x 0 + (1305071041/2500000000 : ℝ)*x 1 + (2713822237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1817546609/10000000000 : ℝ)^4591 ≤ (278510555897/2500000000000 : ℝ)^3567 := by
    have hnat : (1817546609 : ℕ)^4591*2500000000000^3567 ≤ 278510555897^3567*10000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817546609 10000000000 278510555897 2500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305071041/2500000000 : ℝ)^4591 ≤ (4331625639823/10000000000000 : ℝ)^3567 := by
    have hnat : (1305071041 : ℕ)^4591*10000000000000^3567 ≤ 4331625639823^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305071041 2500000000 4331625639823 10000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713822237/5000000000 : ℝ)^4591 ≤ (5692915168687/12500000000000 : ℝ)^3567 := by
    have hnat : (2713822237 : ℕ)^4591*12500000000000^3567 ≤ 5692915168687^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713822237 5000000000 5692915168687 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1817546609/10000000000 : ℝ), (1305071041/2500000000 : ℝ), (2713822237/5000000000 : ℝ)] ![(278510555897/2500000000000 : ℝ), (4331625639823/10000000000000 : ℝ), (5692915168687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1817546609/10000000000 : ℝ)|^4591 ≤ (278510555897/2500000000000 : ℝ)^3567
        have hw : |(-1817546609/10000000000 : ℝ)|=(1817546609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305071041/2500000000 : ℝ)|^4591 ≤ (4331625639823/10000000000000 : ℝ)^3567
        have hw : |(1305071041/2500000000 : ℝ)|=(1305071041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713822237/5000000000 : ℝ)|^4591 ≤ (5692915168687/12500000000000 : ℝ)^3567
        have hw : |(2713822237/5000000000 : ℝ)|=(2713822237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_5 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647152783/5000000000 : ℝ)*x 0 + (-858158219/5000000000 : ℝ)*x 1 + (2713822113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647152783/5000000000 : ℝ)^4591 ≤ (44108389808851/100000000000000 : ℝ)^3567 := by
    have hnat : (2647152783 : ℕ)^4591*100000000000000^3567 ≤ 44108389808851^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647152783 5000000000 44108389808851 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858158219/5000000000 : ℝ)^4591 ≤ (10348291503867/100000000000000 : ℝ)^3567 := by
    have hnat : (858158219 : ℕ)^4591*100000000000000^3567 ≤ 10348291503867^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858158219 5000000000 10348291503867 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713822113/5000000000 : ℝ)^4591 ≤ (9108663734227/20000000000000 : ℝ)^3567 := by
    have hnat : (2713822113 : ℕ)^4591*20000000000000^3567 ≤ 9108663734227^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713822113 5000000000 9108663734227 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647152783/5000000000 : ℝ), (-858158219/5000000000 : ℝ), (2713822113/5000000000 : ℝ)] ![(44108389808851/100000000000000 : ℝ), (10348291503867/100000000000000 : ℝ), (9108663734227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647152783/5000000000 : ℝ)|^4591 ≤ (44108389808851/100000000000000 : ℝ)^3567
        have hw : |(2647152783/5000000000 : ℝ)|=(2647152783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-858158219/5000000000 : ℝ)|^4591 ≤ (10348291503867/100000000000000 : ℝ)^3567
        have hw : |(-858158219/5000000000 : ℝ)|=(858158219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713822113/5000000000 : ℝ)|^4591 ≤ (9108663734227/20000000000000 : ℝ)^3567
        have hw : |(2713822113/5000000000 : ℝ)|=(2713822113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_6 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323576317/2500000000 : ℝ)*x 0 + (1356911083/2500000000 : ℝ)*x 1 + (-858158351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323576317/2500000000 : ℝ)^4591 ≤ (44108386613397/100000000000000 : ℝ)^3567 := by
    have hnat : (1323576317 : ℕ)^4591*100000000000000^3567 ≤ 44108386613397^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323576317 2500000000 44108386613397 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356911083/2500000000 : ℝ)^4591 ≤ (45543319815919/100000000000000 : ℝ)^3567 := by
    have hnat : (1356911083 : ℕ)^4591*100000000000000^3567 ≤ 45543319815919^3567*2500000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356911083 2500000000 45543319815919 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (858158351/5000000000 : ℝ)^4591 ≤ (10348293552571/100000000000000 : ℝ)^3567 := by
    have hnat : (858158351 : ℕ)^4591*100000000000000^3567 ≤ 10348293552571^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858158351 5000000000 10348293552571 100000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323576317/2500000000 : ℝ), (1356911083/2500000000 : ℝ), (-858158351/5000000000 : ℝ)] ![(44108386613397/100000000000000 : ℝ), (45543319815919/100000000000000 : ℝ), (10348293552571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323576317/2500000000 : ℝ)|^4591 ≤ (44108386613397/100000000000000 : ℝ)^3567
        have hw : |(1323576317/2500000000 : ℝ)|=(1323576317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356911083/2500000000 : ℝ)|^4591 ≤ (45543319815919/100000000000000 : ℝ)^3567
        have hw : |(1356911083/2500000000 : ℝ)|=(1356911083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-858158351/5000000000 : ℝ)|^4591 ≤ (10348293552571/100000000000000 : ℝ)^3567
        have hw : |(-858158351/5000000000 : ℝ)|=(858158351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1547_s5_7 (p : ℝ) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170152349/400000000 : ℝ)*x 0 + (2250207207/5000000000 : ℝ)*x 1 + (31395219/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170152349/400000000 : ℝ)^4591 ≤ (16640985132767/50000000000000 : ℝ)^3567 := by
    have hnat : (170152349 : ℕ)^4591*50000000000000^3567 ≤ 16640985132767^3567*400000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170152349 400000000 16640985132767 50000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250207207/5000000000 : ℝ)^4591 ≤ (4473213692743/12500000000000 : ℝ)^3567 := by
    have hnat : (2250207207 : ℕ)^4591*12500000000000^3567 ≤ 4473213692743^3567*5000000000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250207207 5000000000 4473213692743 12500000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31395219/78125000 : ℝ)^4591 ≤ (6186464036437/20000000000000 : ℝ)^3567 := by
    have hnat : (31395219 : ℕ)^4591*20000000000000^3567 ≤ 6186464036437^3567*78125000^4591 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31395219 78125000 6186464036437 20000000000000 4591 3567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4591/1024 : ℝ)) 4591 3567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170152349/400000000 : ℝ), (2250207207/5000000000 : ℝ), (31395219/78125000 : ℝ)] ![(16640985132767/50000000000000 : ℝ), (4473213692743/12500000000000 : ℝ), (6186464036437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170152349/400000000 : ℝ)|^4591 ≤ (16640985132767/50000000000000 : ℝ)^3567
        have hw : |(170152349/400000000 : ℝ)|=(170152349/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250207207/5000000000 : ℝ)|^4591 ≤ (4473213692743/12500000000000 : ℝ)^3567
        have hw : |(2250207207/5000000000 : ℝ)|=(2250207207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31395219/78125000 : ℝ)|^4591 ≤ (6186464036437/20000000000000 : ℝ)^3567
        have hw : |(31395219/78125000 : ℝ)|=(31395219/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1547_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    (2761/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (69/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (69/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (69/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (69/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (69/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (69/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (69/625 : ℝ) ^ (4589/1024 : ℝ) ≤ (1028367246011783/20000000000000000000 : ℝ) := by
    have hpowers : (69/625 : ℝ)^4589 ≤ (1028367246011783/20000000000000000000 : ℝ)^1024 := by
      have hnat : (69 : ℕ)^4589*20000000000000000000^1024 ≤ 1028367246011783^1024*625^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69 625 1028367246011783 20000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69/625 : ℝ)) (X := (1028367246011783/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4589/1024 : ℝ) ≤ (23456311625170143/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4589 ≤ (23456311625170143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4589*100000000000000000000^1024 ≤ 23456311625170143^1024*10000^4589 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 23456311625170143 100000000000000000000 4589 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (23456311625170143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001028367246011783/10000000000000000000 : ℝ) ≤ (10000229463063573/10000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (10001028367246011783/10000000000000000000 : ℝ)^1024 ≤ (10000229463063573/10000000000000000 : ℝ)^4589 := by
      have hnat : (10001028367246011783 : ℕ)^1024*10000000000000000^4589 ≤ 10000229463063573^4589*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001028367246011783 10000000000000000000 10000229463063573 10000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000229463063573/10000000000000000 : ℝ)) (X := (10001028367246011783/10000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014299073927614529/50000000000000000000 : ℝ) ≤ (2500159518691059/2500000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50014299073927614529/50000000000000000000 : ℝ)^1024 ≤ (2500159518691059/2500000000000000 : ℝ)^4589 := by
      have hnat : (50014299073927614529 : ℕ)^1024*2500000000000000^4589 ≤ 2500159518691059^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014299073927614529 50000000000000000000 2500159518691059 2500000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500159518691059/2500000000000000 : ℝ)) (X := (50014299073927614529/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023456311625170143/50000000000000000000 : ℝ) ≤ (10001046686464899/10000000000000000 : ℝ) ^ (4589/1024 : ℝ) := by
    have hpowers : (50023456311625170143/50000000000000000000 : ℝ)^1024 ≤ (10001046686464899/10000000000000000 : ℝ)^4589 := by
      have hnat : (50023456311625170143 : ℕ)^1024*10000000000000000^4589 ≤ 10001046686464899^4589*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023456311625170143 50000000000000000000 10001046686464899 10000000000000000 1024 4589 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001046686464899/10000000000000000 : ℝ)) (X := (50023456311625170143/50000000000000000000 : ℝ)) (by norm_num) 4589 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1028367246011783/20000000000000000000 : ℝ) ≤ ((4449199896428226081/4450000000000000000 : ℝ)+2*(408611700663/445000000000000 : ℝ)*(69/625 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (4449199896428226081/4450000000000000000 : ℝ)+2*(408611700663/445000000000000 : ℝ)*(69/625 : ℝ)=(10000229463063573/10000000000000000 : ℝ) by norm_num, show 1+2*(1028367246011783/20000000000000000000 : ℝ)=(10001028367246011783/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23456311625170143/100000000000000000000 : ℝ)+(1028367246011783/20000000000000000000 : ℝ) ≤ ((4449199896428226081/4450000000000000000 : ℝ)+(408611700663/445000000000000 : ℝ)*((1549/10000 : ℝ)+(69/625 : ℝ)))^(4589/1024 : ℝ) := by
    rw [show (4449199896428226081/4450000000000000000 : ℝ)+(408611700663/445000000000000 : ℝ)*((1549/10000 : ℝ)+(69/625 : ℝ))=(2500159518691059/2500000000000000 : ℝ) by norm_num, show 1+(23456311625170143/100000000000000000000 : ℝ)+(1028367246011783/20000000000000000000 : ℝ)=(50014299073927614529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23456311625170143/100000000000000000000 : ℝ) ≤ ((4449199896428226081/4450000000000000000 : ℝ)+2*(408611700663/445000000000000 : ℝ)*(1549/10000 : ℝ))^(4589/1024 : ℝ) := by
    rw [show (4449199896428226081/4450000000000000000 : ℝ)+2*(408611700663/445000000000000 : ℝ)*(1549/10000 : ℝ)=(10001046686464899/10000000000000000 : ℝ) by norm_num, show 1+2*(23456311625170143/100000000000000000000 : ℝ)=(50023456311625170143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4449199896428226081/4450000000000000000 : ℝ)*(X 1 0+X 2 0)+(408611700663/445000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (69/625 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4449199896428226081/4450000000000000000 : ℝ)) (alpha := (408611700663/445000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4449199896428226081/4450000000000000000 : ℝ)*(X 0 1+X 2 1)+(408611700663/445000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (69/625 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4449199896428226081/4450000000000000000 : ℝ)) (alpha := (408611700663/445000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4449199896428226081/4450000000000000000 : ℝ)*(X 0 2+X 1 2)+(408611700663/445000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4589/1024 : ℝ)) (lo := (69/625 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4449199896428226081/4450000000000000000 : ℝ)) (alpha := (408611700663/445000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-454379927/2500000000 : ℝ)*X 0 0+(2714369301/5000000000 : ℝ)*X 0 1+(5219197539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349584831/10000000000 : ℝ)*X 1 0+(-1924763269/10000000000 : ℝ)*X 1 1+(521919729/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349584887/10000000000 : ℝ)*X 2 0+(1304799299/2500000000 : ℝ)*X 2 1+(-1924763319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((850748913/2000000000 : ℝ)*X 0 0+(1004011301/2500000000 : ℝ)*X 0 1+(1125734653/2500000000 : ℝ)*X 0 2+(850748913/2000000000 : ℝ)*X 1 0+(1004011301/2500000000 : ℝ)*X 1 1+(1125734653/2500000000 : ℝ)*X 1 2+(850748913/2000000000 : ℝ)*X 2 0+(1004011301/2500000000 : ℝ)*X 2 1+(1125734653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1817546609/10000000000 : ℝ)*X 0 0+(1305071041/2500000000 : ℝ)*X 0 1+(2713822237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647152783/5000000000 : ℝ)*X 1 0+(-858158219/5000000000 : ℝ)*X 1 1+(2713822113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323576317/2500000000 : ℝ)*X 2 0+(1356911083/2500000000 : ℝ)*X 2 1+(-858158351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170152349/400000000 : ℝ)*X 0 0+(2250207207/5000000000 : ℝ)*X 0 1+(31395219/78125000 : ℝ)*X 0 2+(170152349/400000000 : ℝ)*X 1 0+(2250207207/5000000000 : ℝ)*X 1 1+(31395219/78125000 : ℝ)*X 1 2+(170152349/400000000 : ℝ)*X 2 0+(2250207207/5000000000 : ℝ)*X 2 1+(31395219/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1547_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6814689435828044614405083/2500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1753228973/100000000000000 : ℝ)*(base19) + (1444125401/100000000000000 : ℝ)*(base23) + (61364067/20000000000000 : ℝ)*(upper3) + (192082889/100000000000000 : ℝ)*(upper4) + (15446501/100000000000000 : ℝ)*(upper5) + (3413116229005803/100000000000000 : ℝ)*(major0) + (3413116229005803/100000000000000 : ℝ)*(major1) + (3413116229005803/100000000000000 : ℝ)*(major2) + (2386179293131867/50000000000000 : ℝ)*(sp0) + (4772376623761109/100000000000000 : ℝ)*(sp1) + (4772376932864681/100000000000000 : ℝ)*(sp2) + (32091306510999/1562500000000 : ℝ)*(sp3) + (4947681587/25000000000000 : ℝ)*(sp4) + (10373455053/100000000000000 : ℝ)*(sp7) + (513463497539747/25000000000000 : ℝ)*(f.failure) + (2386189188495041/50000000000000 : ℝ)*(f.sum) + (1500994449549/250000000000000000000000000 : ℝ)*base66 + (53261715410687213/5000000000000000000000000000000 : ℝ)*base68 + (15912636810687213/5000000000000000000000000000000 : ℝ)*base70 + (40294280500687213/5000000000000000000000000000000 : ℝ)*base72 + (1249326925549/250000000000000000000000000 : ℝ)*base74 + (70082851970687213/5000000000000000000000000000000 : ℝ)*base76 + (31391972840687213/5000000000000000000000000000000 : ℝ)*base78 + (28672823090687213/5000000000000000000000000000000 : ℝ)*base80 + (1187805606549/250000000000000000000000000 : ℝ)*base82 + (2821383/500000000000000000000 : ℝ)*base90 + (2821383/500000000000000000000 : ℝ)*base92 + (2821383/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1245105463724738351096311359/222500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (772428663/100000000000000 : ℝ)*(base19) + (193175249/25000000000000 : ℝ)*(base23) + (146056079/100000000000000 : ℝ)*(lower1) + (791179/20000000000000 : ℝ)*(upper3) + (16601791/10000000000000 : ℝ)*(lower4) + (90087957/100000000000000 : ℝ)*(upper5) + (3448972549880587/100000000000000 : ℝ)*(major0) + (3448972549880587/100000000000000 : ℝ)*(major1) + (3448972549880587/100000000000000 : ℝ)*(major2) + (80184953/2000000000000 : ℝ)*(sp1) + (60281428290979/1250000000000 : ℝ)*(sp4) + (4822509481602007/100000000000000 : ℝ)*(sp5) + (1205628372644331/25000000000000 : ℝ)*(sp6) + (129714415621887/6250000000000 : ℝ)*(sp7) + (129714415621887/6250000000000 : ℝ)*(f.failure) + (60281428290979/1250000000000 : ℝ)*(f.sum) + (75572403609181/22250000000000000000000000000 : ℝ)*base65 + (2873507145679200453/445000000000000000000000000000000 : ℝ)*base68 + (169441188400799547/445000000000000000000000000000000 : ℝ)*base69 + (1818616756240799547/445000000000000000000000000000000 : ℝ)*base71 + (21714048002181/22250000000000000000000000000 : ℝ)*base73 + (3876101439510799547/445000000000000000000000000000000 : ℝ)*base75 + (752719505840799547/445000000000000000000000000000000 : ℝ)*base77 + (1714639519839200453/445000000000000000000000000000000 : ℝ)*base80 + (112110722243181/22250000000000000000000000000 : ℝ)*base81 + (1199843/125000000000000000000 : ℝ)*base90 + (1199843/125000000000000000000 : ℝ)*base92 + (1199843/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1547_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2761/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1547_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1547_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2761/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1547_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1547_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1547_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4589/1024 : ℝ) ≤ p) (hpb : p ≤ (4591/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33236211/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2761/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1547_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

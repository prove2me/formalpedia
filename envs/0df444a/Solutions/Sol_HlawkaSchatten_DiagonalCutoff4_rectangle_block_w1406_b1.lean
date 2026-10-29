-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1406_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:55.862996+00:00
-- url     : https://prove2.me/submissions/769ed330-1524-4210-abf8-0622ac1a1477

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
theorem support_rectangle_w1406_s3_0 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988734773/10000000000 : ℝ)*x 0 + (2709838983/5000000000 : ℝ)*x 1 + (2618446563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988734773/10000000000 : ℝ)^2183 ≤ (3031087528371/25000000000000 : ℝ)^1671 := by
    have hnat : (1988734773 : ℕ)^2183*25000000000000^1671 ≤ 3031087528371^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988734773 10000000000 3031087528371 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709838983/5000000000 : ℝ)^2183 ≤ (44922308404461/100000000000000 : ℝ)^1671 := by
    have hnat : (2709838983 : ℕ)^2183*100000000000000^1671 ≤ 44922308404461^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709838983 5000000000 44922308404461 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618446563/5000000000 : ℝ)^2183 ≤ (21476670733271/50000000000000 : ℝ)^1671 := by
    have hnat : (2618446563 : ℕ)^2183*50000000000000^1671 ≤ 21476670733271^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618446563 5000000000 21476670733271 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988734773/10000000000 : ℝ), (2709838983/5000000000 : ℝ), (2618446563/5000000000 : ℝ)] ![(3031087528371/25000000000000 : ℝ), (44922308404461/100000000000000 : ℝ), (21476670733271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988734773/10000000000 : ℝ)|^2183 ≤ (3031087528371/25000000000000 : ℝ)^1671
        have hw : |(-1988734773/10000000000 : ℝ)|=(1988734773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709838983/5000000000 : ℝ)|^2183 ≤ (44922308404461/100000000000000 : ℝ)^1671
        have hw : |(2709838983/5000000000 : ℝ)|=(2709838983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618446563/5000000000 : ℝ)|^2183 ≤ (21476670733271/50000000000000 : ℝ)^1671
        have hw : |(2618446563/5000000000 : ℝ)|=(2618446563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_1 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350444997/10000000000 : ℝ)*x 0 + (-416403033/2000000000 : ℝ)*x 1 + (654611633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350444997/10000000000 : ℝ)^2183 ≤ (11043523732209/25000000000000 : ℝ)^1671 := by
    have hnat : (5350444997 : ℕ)^2183*25000000000000^1671 ≤ 11043523732209^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350444997 10000000000 11043523732209 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416403033/2000000000 : ℝ)^2183 ≤ (3218141061129/25000000000000 : ℝ)^1671 := by
    have hnat : (416403033 : ℕ)^2183*25000000000000^1671 ≤ 3218141061129^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416403033 2000000000 3218141061129 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654611633/1250000000 : ℝ)^2183 ≤ (42953340802199/100000000000000 : ℝ)^1671 := by
    have hnat : (654611633 : ℕ)^2183*100000000000000^1671 ≤ 42953340802199^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654611633 1250000000 42953340802199 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350444997/10000000000 : ℝ), (-416403033/2000000000 : ℝ), (654611633/1250000000 : ℝ)] ![(11043523732209/25000000000000 : ℝ), (3218141061129/25000000000000 : ℝ), (42953340802199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350444997/10000000000 : ℝ)|^2183 ≤ (11043523732209/25000000000000 : ℝ)^1671
        have hw : |(5350444997/10000000000 : ℝ)|=(5350444997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416403033/2000000000 : ℝ)|^2183 ≤ (3218141061129/25000000000000 : ℝ)^1671
        have hw : |(-416403033/2000000000 : ℝ)|=(416403033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654611633/1250000000 : ℝ)|^2183 ≤ (42953340802199/100000000000000 : ℝ)^1671
        have hw : |(654611633/1250000000 : ℝ)|=(654611633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_2 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675222491/5000000000 : ℝ)*x 0 + (1047378627/2000000000 : ℝ)*x 1 + (-2082015091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675222491/5000000000 : ℝ)^2183 ≤ (5521761845881/12500000000000 : ℝ)^1671 := by
    have hnat : (2675222491 : ℕ)^2183*12500000000000^1671 ≤ 5521761845881^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675222491 5000000000 5521761845881 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047378627/2000000000 : ℝ)^2183 ≤ (42953341562979/100000000000000 : ℝ)^1671 := by
    have hnat : (1047378627 : ℕ)^2183*100000000000000^1671 ≤ 42953341562979^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047378627 2000000000 42953341562979 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082015091/10000000000 : ℝ)^2183 ≤ (6436281823403/50000000000000 : ℝ)^1671 := by
    have hnat : (2082015091 : ℕ)^2183*50000000000000^1671 ≤ 6436281823403^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082015091 10000000000 6436281823403 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675222491/5000000000 : ℝ), (1047378627/2000000000 : ℝ), (-2082015091/10000000000 : ℝ)] ![(5521761845881/12500000000000 : ℝ), (42953341562979/100000000000000 : ℝ), (6436281823403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675222491/5000000000 : ℝ)|^2183 ≤ (5521761845881/12500000000000 : ℝ)^1671
        have hw : |(2675222491/5000000000 : ℝ)|=(2675222491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047378627/2000000000 : ℝ)|^2183 ≤ (42953341562979/100000000000000 : ℝ)^1671
        have hw : |(1047378627/2000000000 : ℝ)|=(1047378627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082015091/10000000000 : ℝ)|^2183 ≤ (6436281823403/50000000000000 : ℝ)^1671
        have hw : |(-2082015091/10000000000 : ℝ)|=(2082015091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_3 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (17237683/40000000 : ℝ)*x 0 + (1029355773/2500000000 : ℝ)*x 1 + (4509518039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17237683/40000000 : ℝ)^2183 ≤ (33296886351941/100000000000000 : ℝ)^1671 := by
    have hnat : (17237683 : ℕ)^2183*100000000000000^1671 ≤ 33296886351941^1671*40000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17237683 40000000 33296886351941 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029355773/2500000000 : ℝ)^2183 ≤ (1254889390719/4000000000000 : ℝ)^1671 := by
    have hnat : (1029355773 : ℕ)^2183*4000000000000^1671 ≤ 1254889390719^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029355773 2500000000 1254889390719 4000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509518039/10000000000 : ℝ)^2183 ≤ (4416359858593/12500000000000 : ℝ)^1671 := by
    have hnat : (4509518039 : ℕ)^2183*12500000000000^1671 ≤ 4416359858593^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509518039 10000000000 4416359858593 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17237683/40000000 : ℝ), (1029355773/2500000000 : ℝ), (4509518039/10000000000 : ℝ)] ![(33296886351941/100000000000000 : ℝ), (1254889390719/4000000000000 : ℝ), (4416359858593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17237683/40000000 : ℝ)|^2183 ≤ (33296886351941/100000000000000 : ℝ)^1671
        have hw : |(17237683/40000000 : ℝ)|=(17237683/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029355773/2500000000 : ℝ)|^2183 ≤ (1254889390719/4000000000000 : ℝ)^1671
        have hw : |(1029355773/2500000000 : ℝ)|=(1029355773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509518039/10000000000 : ℝ)|^2183 ≤ (4416359858593/12500000000000 : ℝ)^1671
        have hw : |(4509518039/10000000000 : ℝ)|=(4509518039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_4 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988751347/10000000000 : ℝ)*x 0 + (2618815093/5000000000 : ℝ)*x 1 + (5418936391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988751347/10000000000 : ℝ)^2183 ≤ (3031120529347/25000000000000 : ℝ)^1671 := by
    have hnat : (1988751347 : ℕ)^2183*25000000000000^1671 ≤ 3031120529347^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988751347 10000000000 3031120529347 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618815093/5000000000 : ℝ)^2183 ≤ (5370154923331/12500000000000 : ℝ)^1671 := by
    have hnat : (2618815093 : ℕ)^2183*12500000000000^1671 ≤ 5370154923331^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618815093 5000000000 5370154923331 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418936391/10000000000 : ℝ)^2183 ≤ (22457139236437/50000000000000 : ℝ)^1671 := by
    have hnat : (5418936391 : ℕ)^2183*50000000000000^1671 ≤ 22457139236437^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418936391 10000000000 22457139236437 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988751347/10000000000 : ℝ), (2618815093/5000000000 : ℝ), (5418936391/10000000000 : ℝ)] ![(3031120529347/25000000000000 : ℝ), (5370154923331/12500000000000 : ℝ), (22457139236437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988751347/10000000000 : ℝ)|^2183 ≤ (3031120529347/25000000000000 : ℝ)^1671
        have hw : |(-1988751347/10000000000 : ℝ)|=(1988751347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618815093/5000000000 : ℝ)|^2183 ≤ (5370154923331/12500000000000 : ℝ)^1671
        have hw : |(2618815093/5000000000 : ℝ)|=(2618815093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418936391/10000000000 : ℝ)|^2183 ≤ (22457139236437/50000000000000 : ℝ)^1671
        have hw : |(5418936391/10000000000 : ℝ)|=(5418936391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_5 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212121427/400000000 : ℝ)*x 0 + (-1899971291/10000000000 : ℝ)*x 1 + (2709468377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212121427/400000000 : ℝ)^2183 ≤ (43663439891013/100000000000000 : ℝ)^1671 := by
    have hnat : (212121427 : ℕ)^2183*100000000000000^1671 ≤ 43663439891013^1671*400000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212121427 400000000 43663439891013 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899971291/10000000000 : ℝ)^2183 ≤ (11422277691197/100000000000000 : ℝ)^1671 := by
    have hnat : (1899971291 : ℕ)^2183*100000000000000^1671 ≤ 11422277691197^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899971291 10000000000 11422277691197 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709468377/5000000000 : ℝ)^2183 ≤ (44914282403433/100000000000000 : ℝ)^1671 := by
    have hnat : (2709468377 : ℕ)^2183*100000000000000^1671 ≤ 44914282403433^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709468377 5000000000 44914282403433 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212121427/400000000 : ℝ), (-1899971291/10000000000 : ℝ), (2709468377/5000000000 : ℝ)] ![(43663439891013/100000000000000 : ℝ), (11422277691197/100000000000000 : ℝ), (44914282403433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212121427/400000000 : ℝ)|^2183 ≤ (43663439891013/100000000000000 : ℝ)^1671
        have hw : |(212121427/400000000 : ℝ)|=(212121427/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1899971291/10000000000 : ℝ)|^2183 ≤ (11422277691197/100000000000000 : ℝ)^1671
        have hw : |(-1899971291/10000000000 : ℝ)|=(1899971291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709468377/5000000000 : ℝ)|^2183 ≤ (44914282403433/100000000000000 : ℝ)^1671
        have hw : |(2709468377/5000000000 : ℝ)|=(2709468377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_6 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303036529/10000000000 : ℝ)*x 0 + (2709468043/5000000000 : ℝ)*x 1 + (-949985521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303036529/10000000000 : ℝ)^2183 ≤ (21831724538529/50000000000000 : ℝ)^1671 := by
    have hnat : (5303036529 : ℕ)^2183*50000000000000^1671 ≤ 21831724538529^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303036529 10000000000 21831724538529 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709468043/5000000000 : ℝ)^2183 ≤ (44914275170339/100000000000000 : ℝ)^1671 := by
    have hnat : (2709468043 : ℕ)^2183*100000000000000^1671 ≤ 44914275170339^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709468043 5000000000 44914275170339 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949985521/5000000000 : ℝ)^2183 ≤ (5711137867793/50000000000000 : ℝ)^1671 := by
    have hnat : (949985521 : ℕ)^2183*50000000000000^1671 ≤ 5711137867793^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949985521 5000000000 5711137867793 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303036529/10000000000 : ℝ), (2709468043/5000000000 : ℝ), (-949985521/5000000000 : ℝ)] ![(21831724538529/50000000000000 : ℝ), (44914275170339/100000000000000 : ℝ), (5711137867793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303036529/10000000000 : ℝ)|^2183 ≤ (21831724538529/50000000000000 : ℝ)^1671
        have hw : |(5303036529/10000000000 : ℝ)|=(5303036529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709468043/5000000000 : ℝ)|^2183 ≤ (44914275170339/100000000000000 : ℝ)^1671
        have hw : |(2709468043/5000000000 : ℝ)|=(2709468043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949985521/5000000000 : ℝ)|^2183 ≤ (5711137867793/50000000000000 : ℝ)^1671
        have hw : |(-949985521/5000000000 : ℝ)|=(949985521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s3_7 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4309456571/10000000000 : ℝ)*x 0 + (4507936661/10000000000 : ℝ)*x 1 + (2059506329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309456571/10000000000 : ℝ)^2183 ≤ (16648623964251/50000000000000 : ℝ)^1671 := by
    have hnat : (4309456571 : ℕ)^2183*50000000000000^1671 ≤ 16648623964251^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309456571 10000000000 16648623964251 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507936661/10000000000 : ℝ)^2183 ≤ (35314693822071/100000000000000 : ℝ)^1671 := by
    have hnat : (4507936661 : ℕ)^2183*100000000000000^1671 ≤ 35314693822071^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507936661 10000000000 35314693822071 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059506329/5000000000 : ℝ)^2183 ≤ (31388058229461/100000000000000 : ℝ)^1671 := by
    have hnat : (2059506329 : ℕ)^2183*100000000000000^1671 ≤ 31388058229461^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059506329 5000000000 31388058229461 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309456571/10000000000 : ℝ), (4507936661/10000000000 : ℝ), (2059506329/5000000000 : ℝ)] ![(16648623964251/50000000000000 : ℝ), (35314693822071/100000000000000 : ℝ), (31388058229461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309456571/10000000000 : ℝ)|^2183 ≤ (16648623964251/50000000000000 : ℝ)^1671
        have hw : |(4309456571/10000000000 : ℝ)|=(4309456571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507936661/10000000000 : ℝ)|^2183 ≤ (35314693822071/100000000000000 : ℝ)^1671
        have hw : |(4507936661/10000000000 : ℝ)|=(4507936661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2059506329/5000000000 : ℝ)|^2183 ≤ (31388058229461/100000000000000 : ℝ)^1671
        have hw : |(2059506329/5000000000 : ℝ)|=(2059506329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1406_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1109/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (187/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10241/100000 : ℝ) ^ (4365/1024 : ℝ) ≤ (6044926757531787/100000000000000000000 : ℝ) := by
    have hpowers : (10241/100000 : ℝ)^4365 ≤ (6044926757531787/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10241 : ℕ)^4365*100000000000000000000^1024 ≤ 6044926757531787^1024*100000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10241 100000 6044926757531787 100000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10241/100000 : ℝ)) (X := (6044926757531787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15873/100000 : ℝ) ^ (4365/1024 : ℝ) ≤ (3914289433770807/10000000000000000000 : ℝ) := by
    have hpowers : (15873/100000 : ℝ)^4365 ≤ (3914289433770807/10000000000000000000 : ℝ)^1024 := by
      have hnat : (15873 : ℕ)^4365*10000000000000000000^1024 ≤ 3914289433770807^1024*100000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15873 100000 3914289433770807 10000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15873/100000 : ℝ)) (X := (3914289433770807/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006044926757531787/50000000000000000000 : ℝ) ≤ (2500070901702397/2500000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50006044926757531787/50000000000000000000 : ℝ)^1024 ≤ (2500070901702397/2500000000000000 : ℝ)^4365 := by
      have hnat : (50006044926757531787 : ℕ)^1024*2500000000000000^4365 ≤ 2500070901702397^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006044926757531787 50000000000000000000 2500070901702397 2500000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070901702397/2500000000000000 : ℝ)) (X := (50006044926757531787/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045187821095239857/100000000000000000000 : ℝ) ≤ (10001059892985339/10000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (100045187821095239857/100000000000000000000 : ℝ)^1024 ≤ (10001059892985339/10000000000000000 : ℝ)^4365 := by
      have hnat : (100045187821095239857 : ℕ)^1024*10000000000000000^4365 ≤ 10001059892985339^4365*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045187821095239857 100000000000000000000 10001059892985339 10000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001059892985339/10000000000000000 : ℝ)) (X := (100045187821095239857/100000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003914289433770807/5000000000000000000 : ℝ) ≤ (1000183617916109/1000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (5003914289433770807/5000000000000000000 : ℝ)^1024 ≤ (1000183617916109/1000000000000000 : ℝ)^4365 := by
      have hnat : (5003914289433770807 : ℕ)^1024*1000000000000000^4365 ≤ 1000183617916109^4365*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003914289433770807 5000000000000000000 1000183617916109 1000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000183617916109/1000000000000000 : ℝ)) (X := (5003914289433770807/5000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6044926757531787/100000000000000000000 : ℝ) ≤ ((2559349880913630347/2560000000000000000 : ℝ)+2*(776286175751/563200000000000 : ℝ)*(10241/100000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (2559349880913630347/2560000000000000000 : ℝ)+2*(776286175751/563200000000000 : ℝ)*(10241/100000 : ℝ)=(2500070901702397/2500000000000000 : ℝ) by norm_num, show 1+2*(6044926757531787/100000000000000000000 : ℝ)=(50006044926757531787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3914289433770807/10000000000000000000 : ℝ)+(6044926757531787/100000000000000000000 : ℝ) ≤ ((2559349880913630347/2560000000000000000 : ℝ)+(776286175751/563200000000000 : ℝ)*((15873/100000 : ℝ)+(10241/100000 : ℝ)))^(4365/1024 : ℝ) := by
    rw [show (2559349880913630347/2560000000000000000 : ℝ)+(776286175751/563200000000000 : ℝ)*((15873/100000 : ℝ)+(10241/100000 : ℝ))=(10001059892985339/10000000000000000 : ℝ) by norm_num, show 1+(3914289433770807/10000000000000000000 : ℝ)+(6044926757531787/100000000000000000000 : ℝ)=(100045187821095239857/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3914289433770807/10000000000000000000 : ℝ) ≤ ((2559349880913630347/2560000000000000000 : ℝ)+2*(776286175751/563200000000000 : ℝ)*(15873/100000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (2559349880913630347/2560000000000000000 : ℝ)+2*(776286175751/563200000000000 : ℝ)*(15873/100000 : ℝ)=(1000183617916109/1000000000000000 : ℝ) by norm_num, show 1+2*(3914289433770807/10000000000000000000 : ℝ)=(5003914289433770807/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2559349880913630347/2560000000000000000 : ℝ)*(X 1 0+X 2 0)+(776286175751/563200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (10241/100000 : ℝ)) (hi := (15873/100000 : ℝ)) (c := (2559349880913630347/2560000000000000000 : ℝ)) (alpha := (776286175751/563200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2559349880913630347/2560000000000000000 : ℝ)*(X 0 1+X 2 1)+(776286175751/563200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (10241/100000 : ℝ)) (hi := (15873/100000 : ℝ)) (c := (2559349880913630347/2560000000000000000 : ℝ)) (alpha := (776286175751/563200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2559349880913630347/2560000000000000000 : ℝ)*(X 0 2+X 1 2)+(776286175751/563200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (10241/100000 : ℝ)) (hi := (15873/100000 : ℝ)) (c := (2559349880913630347/2560000000000000000 : ℝ)) (alpha := (776286175751/563200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1988734773/10000000000 : ℝ)*X 0 0+(2709838983/5000000000 : ℝ)*X 0 1+(2618446563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350444997/10000000000 : ℝ)*X 1 0+(-416403033/2000000000 : ℝ)*X 1 1+(654611633/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675222491/5000000000 : ℝ)*X 2 0+(1047378627/2000000000 : ℝ)*X 2 1+(-2082015091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17237683/40000000 : ℝ)*X 0 0+(1029355773/2500000000 : ℝ)*X 0 1+(4509518039/10000000000 : ℝ)*X 0 2+(17237683/40000000 : ℝ)*X 1 0+(1029355773/2500000000 : ℝ)*X 1 1+(4509518039/10000000000 : ℝ)*X 1 2+(17237683/40000000 : ℝ)*X 2 0+(1029355773/2500000000 : ℝ)*X 2 1+(4509518039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1988751347/10000000000 : ℝ)*X 0 0+(2618815093/5000000000 : ℝ)*X 0 1+(5418936391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212121427/400000000 : ℝ)*X 1 0+(-1899971291/10000000000 : ℝ)*X 1 1+(2709468377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303036529/10000000000 : ℝ)*X 2 0+(2709468043/5000000000 : ℝ)*X 2 1+(-949985521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309456571/10000000000 : ℝ)*X 0 0+(4507936661/10000000000 : ℝ)*X 0 1+(2059506329/5000000000 : ℝ)*X 0 2+(4309456571/10000000000 : ℝ)*X 1 0+(4507936661/10000000000 : ℝ)*X 1 1+(2059506329/5000000000 : ℝ)*X 1 2+(4309456571/10000000000 : ℝ)*X 2 0+(4507936661/10000000000 : ℝ)*X 2 1+(2059506329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (215269463175089286401924049/64000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (689015317/100000000000000 : ℝ)*(base19) + (38998183/6250000000000 : ℝ)*(base23) + (14867391/20000000000000 : ℝ)*(upper3) + (26595241/100000000000000 : ℝ)*(upper4) + (120726741/100000000000000 : ℝ)*(upper5) + (2005336974305489/50000000000000 : ℝ)*(major0) + (2005336974305489/50000000000000 : ℝ)*(major1) + (2005336974305489/50000000000000 : ℝ)*(major2) + (5470923108867807/100000000000000 : ℝ)*(sp0) + (5470934500970107/100000000000000 : ℝ)*(sp1) + (170966705187953/3125000000000 : ℝ)*(sp2) + (63760196544099/2500000000000 : ℝ)*(sp3) + (12081117617/100000000000000 : ℝ)*(sp4) + (2366676527/50000000000000 : ℝ)*(sp7) + (1275206297558507/50000000000000 : ℝ)*(f.failure) + (341933449374089/6250000000000 : ℝ)*(f.sum) + (1079047697029/1280000000000000000000000000 : ℝ)*base65 + (893682681277475317/128000000000000000000000000000000 : ℝ)*base68 + (267112769341475317/128000000000000000000000000000000 : ℝ)*base70 + (1666032322524683/128000000000000000000000000000000 : ℝ)*base71 + (9955255579771/1280000000000000000000000000 : ℝ)*base74 + (1263739062973475317/128000000000000000000000000000000 : ℝ)*base76 + (357793470018524683/128000000000000000000000000000000 : ℝ)*base77 + (1430342858685475317/128000000000000000000000000000000 : ℝ)*base80 + (9235471230331/1280000000000000000000000000 : ℝ)*base82 + (52680709/5000000000000000000000 : ℝ)*base89 + (52680709/5000000000000000000000 : ℝ)*base91 + (52680709/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3271823418408700551928039461/704000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (645895421/25000000000000 : ℝ)*(base19) + (186476039/5000000000000 : ℝ)*(base23) + (440934629/100000000000000 : ℝ)*(upper3) + (3148887/6250000000000 : ℝ)*(lower4) + (127587451/50000000000000 : ℝ)*(upper5) + (2021683094732837/50000000000000 : ℝ)*(major0) + (2021683094732837/50000000000000 : ℝ)*(major1) + (2021683094732837/50000000000000 : ℝ)*(major2) + (12947911499/25000000000000 : ℝ)*(sp1) + (13998689247/20000000000000 : ℝ)*(sp2) + (5515530428901943/100000000000000 : ℝ)*(sp4) + (689434506709283/12500000000000 : ℝ)*(sp5) + (344716044120933/6250000000000 : ℝ)*(sp6) + (321400224389189/12500000000000 : ℝ)*(sp7) + (321400224389189/12500000000000 : ℝ)*(f.failure) + (5515530428901943/100000000000000 : ℝ)*(f.sum) + (124662478608893/14080000000000000000000000000 : ℝ)*base66 + (21475417525714001171/1408000000000000000000000000000000 : ℝ)*base68 + (4819239038546001171/1408000000000000000000000000000000 : ℝ)*base70 + (27408057535186001171/1408000000000000000000000000000000 : ℝ)*base72 + (91504911257853/14080000000000000000000000000 : ℝ)*base74 + (16697075065042001171/1408000000000000000000000000000000 : ℝ)*base76 + (17142157012946001171/1408000000000000000000000000000000 : ℝ)*base78 + (9196611571794001171/1408000000000000000000000000000000 : ℝ)*base80 + (12417199542787/14080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (24405643/1250000000000000000000 : ℝ)*base89 + (24405643/1250000000000000000000 : ℝ)*base91 + (24405643/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1406_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (187/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1406_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1406_s4_0 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989758821/10000000000 : ℝ)*x 0 + (1352757213/2500000000 : ℝ)*x 1 + (81951069/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989758821/10000000000 : ℝ)^2183 ≤ (12132506794073/100000000000000 : ℝ)^1671 := by
    have hnat : (1989758821 : ℕ)^2183*100000000000000^1671 ≤ 12132506794073^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989758821 10000000000 12132506794073 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352757213/2500000000 : ℝ)^2183 ≤ (44828674904467/100000000000000 : ℝ)^1671 := by
    have hnat : (1352757213 : ℕ)^2183*100000000000000^1671 ≤ 44828674904467^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352757213 2500000000 44828674904467 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81951069/156250000 : ℝ)^2183 ≤ (10759704568443/25000000000000 : ℝ)^1671 := by
    have hnat : (81951069 : ℕ)^2183*25000000000000^1671 ≤ 10759704568443^1671*156250000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81951069 156250000 10759704568443 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989758821/10000000000 : ℝ), (1352757213/2500000000 : ℝ), (81951069/156250000 : ℝ)] ![(12132506794073/100000000000000 : ℝ), (44828674904467/100000000000000 : ℝ), (10759704568443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989758821/10000000000 : ℝ)|^2183 ≤ (12132506794073/100000000000000 : ℝ)^1671
        have hw : |(-1989758821/10000000000 : ℝ)|=(1989758821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352757213/2500000000 : ℝ)|^2183 ≤ (44828674904467/100000000000000 : ℝ)^1671
        have hw : |(1352757213/2500000000 : ℝ)|=(1352757213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81951069/156250000 : ℝ)|^2183 ≤ (10759704568443/25000000000000 : ℝ)^1671
        have hw : |(81951069/156250000 : ℝ)|=(81951069/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_1 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348220079/10000000000 : ℝ)*x 0 + (-32412487/156250000 : ℝ)*x 1 + (1048973679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348220079/10000000000 : ℝ)^2183 ≤ (44150098789199/100000000000000 : ℝ)^1671 := by
    have hnat : (5348220079 : ℕ)^2183*100000000000000^1671 ≤ 44150098789199^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348220079 10000000000 44150098789199 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32412487/156250000 : ℝ)^2183 ≤ (3202770788157/25000000000000 : ℝ)^1671 := by
    have hnat : (32412487 : ℕ)^2183*25000000000000^1671 ≤ 3202770788157^1671*156250000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32412487 156250000 3202770788157 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048973679/2000000000 : ℝ)^2183 ≤ (5379852256081/12500000000000 : ℝ)^1671 := by
    have hnat : (1048973679 : ℕ)^2183*12500000000000^1671 ≤ 5379852256081^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048973679 2000000000 5379852256081 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348220079/10000000000 : ℝ), (-32412487/156250000 : ℝ), (1048973679/2000000000 : ℝ)] ![(44150098789199/100000000000000 : ℝ), (3202770788157/25000000000000 : ℝ), (5379852256081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348220079/10000000000 : ℝ)|^2183 ≤ (44150098789199/100000000000000 : ℝ)^1671
        have hw : |(5348220079/10000000000 : ℝ)|=(5348220079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32412487/156250000 : ℝ)|^2183 ≤ (3202770788157/25000000000000 : ℝ)^1671
        have hw : |(-32412487/156250000 : ℝ)|=(32412487/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048973679/2000000000 : ℝ)|^2183 ≤ (5379852256081/12500000000000 : ℝ)^1671
        have hw : |(1048973679/2000000000 : ℝ)|=(1048973679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_2 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33426373/62500000 : ℝ)*x 0 + (5244868499/10000000000 : ℝ)*x 1 + (-2074399563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33426373/62500000 : ℝ)^2183 ≤ (44150094486187/100000000000000 : ℝ)^1671 := by
    have hnat : (33426373 : ℕ)^2183*100000000000000^1671 ≤ 44150094486187^1671*62500000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33426373 62500000 44150094486187 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244868499/10000000000 : ℝ)^2183 ≤ (43038819163549/100000000000000 : ℝ)^1671 := by
    have hnat : (5244868499 : ℕ)^2183*100000000000000^1671 ≤ 43038819163549^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244868499 10000000000 43038819163549 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074399563/10000000000 : ℝ)^2183 ≤ (3202771584881/25000000000000 : ℝ)^1671 := by
    have hnat : (2074399563 : ℕ)^2183*25000000000000^1671 ≤ 3202771584881^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074399563 10000000000 3202771584881 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33426373/62500000 : ℝ), (5244868499/10000000000 : ℝ), (-2074399563/10000000000 : ℝ)] ![(44150094486187/100000000000000 : ℝ), (43038819163549/100000000000000 : ℝ), (3202771584881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33426373/62500000 : ℝ)|^2183 ≤ (44150094486187/100000000000000 : ℝ)^1671
        have hw : |(33426373/62500000 : ℝ)|=(33426373/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244868499/10000000000 : ℝ)|^2183 ≤ (43038819163549/100000000000000 : ℝ)^1671
        have hw : |(5244868499/10000000000 : ℝ)|=(5244868499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074399563/10000000000 : ℝ)|^2183 ≤ (3202771584881/25000000000000 : ℝ)^1671
        have hw : |(-2074399563/10000000000 : ℝ)|=(2074399563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_3 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310047647/10000000000 : ℝ)*x 0 + (1033794267/2500000000 : ℝ)*x 1 + (4491611507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310047647/10000000000 : ℝ)^2183 ≤ (6660642874499/20000000000000 : ℝ)^1671 := by
    have hnat : (4310047647 : ℕ)^2183*20000000000000^1671 ≤ 6660642874499^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310047647 10000000000 6660642874499 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033794267/2500000000 : ℝ)^2183 ≤ (1971817144499/6250000000000 : ℝ)^1671 := by
    have hnat : (1033794267 : ℕ)^2183*6250000000000^1671 ≤ 1971817144499^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033794267 2500000000 1971817144499 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491611507/10000000000 : ℝ)^2183 ≤ (17573855654413/50000000000000 : ℝ)^1671 := by
    have hnat : (4491611507 : ℕ)^2183*50000000000000^1671 ≤ 17573855654413^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491611507 10000000000 17573855654413 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310047647/10000000000 : ℝ), (1033794267/2500000000 : ℝ), (4491611507/10000000000 : ℝ)] ![(6660642874499/20000000000000 : ℝ), (1971817144499/6250000000000 : ℝ), (17573855654413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310047647/10000000000 : ℝ)|^2183 ≤ (6660642874499/20000000000000 : ℝ)^1671
        have hw : |(4310047647/10000000000 : ℝ)|=(4310047647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033794267/2500000000 : ℝ)|^2183 ≤ (1971817144499/6250000000000 : ℝ)^1671
        have hw : |(1033794267/2500000000 : ℝ)|=(1033794267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491611507/10000000000 : ℝ)|^2183 ≤ (17573855654413/50000000000000 : ℝ)^1671
        have hw : |(4491611507/10000000000 : ℝ)|=(4491611507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_4 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989770987/10000000000 : ℝ)*x 0 + (327842361/625000000 : ℝ)*x 1 + (2705208157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989770987/10000000000 : ℝ)^2183 ≤ (12132603705639/100000000000000 : ℝ)^1671 := by
    have hnat : (1989770987 : ℕ)^2183*100000000000000^1671 ≤ 12132603705639^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989770987 10000000000 12132603705639 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327842361/625000000 : ℝ)^2183 ≤ (4304535085321/10000000000000 : ℝ)^1671 := by
    have hnat : (327842361 : ℕ)^2183*10000000000000^1671 ≤ 4304535085321^1671*625000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327842361 625000000 4304535085321 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705208157/5000000000 : ℝ)^2183 ≤ (44822045433973/100000000000000 : ℝ)^1671 := by
    have hnat : (2705208157 : ℕ)^2183*100000000000000^1671 ≤ 44822045433973^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705208157 5000000000 44822045433973 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989770987/10000000000 : ℝ), (327842361/625000000 : ℝ), (2705208157/5000000000 : ℝ)] ![(12132603705639/100000000000000 : ℝ), (4304535085321/10000000000000 : ℝ), (44822045433973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989770987/10000000000 : ℝ)|^2183 ≤ (12132603705639/100000000000000 : ℝ)^1671
        have hw : |(-1989770987/10000000000 : ℝ)|=(1989770987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327842361/625000000 : ℝ)|^2183 ≤ (4304535085321/10000000000000 : ℝ)^1671
        have hw : |(327842361/625000000 : ℝ)|=(327842361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705208157/5000000000 : ℝ)|^2183 ≤ (44822045433973/100000000000000 : ℝ)^1671
        have hw : |(2705208157/5000000000 : ℝ)|=(2705208157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_5 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305121923/10000000000 : ℝ)*x 0 + (-1908851441/10000000000 : ℝ)*x 1 + (5410416461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305121923/10000000000 : ℝ)^2183 ≤ (21842940977329/50000000000000 : ℝ)^1671 := by
    have hnat : (5305121923 : ℕ)^2183*50000000000000^1671 ≤ 21842940977329^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305121923 10000000000 21842940977329 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1908851441/10000000000 : ℝ)^2183 ≤ (459682840003/4000000000000 : ℝ)^1671 := by
    have hnat : (1908851441 : ℕ)^2183*4000000000000^1671 ≤ 459682840003^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908851441 10000000000 459682840003 4000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410416461/10000000000 : ℝ)^2183 ≤ (1120551175623/2500000000000 : ℝ)^1671 := by
    have hnat : (5410416461 : ℕ)^2183*2500000000000^1671 ≤ 1120551175623^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410416461 10000000000 1120551175623 2500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305121923/10000000000 : ℝ), (-1908851441/10000000000 : ℝ), (5410416461/10000000000 : ℝ)] ![(21842940977329/50000000000000 : ℝ), (459682840003/4000000000000 : ℝ), (1120551175623/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305121923/10000000000 : ℝ)|^2183 ≤ (21842940977329/50000000000000 : ℝ)^1671
        have hw : |(5305121923/10000000000 : ℝ)|=(5305121923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1908851441/10000000000 : ℝ)|^2183 ≤ (459682840003/4000000000000 : ℝ)^1671
        have hw : |(-1908851441/10000000000 : ℝ)|=(1908851441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410416461/10000000000 : ℝ)|^2183 ≤ (1120551175623/2500000000000 : ℝ)^1671
        have hw : |(5410416461/10000000000 : ℝ)|=(5410416461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_6 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331570119/625000000 : ℝ)*x 0 + (5410416377/10000000000 : ℝ)*x 1 + (-1908851583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331570119/625000000 : ℝ)^2183 ≤ (2184294087513/5000000000000 : ℝ)^1671 := by
    have hnat : (331570119 : ℕ)^2183*5000000000000^1671 ≤ 2184294087513^1671*625000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331570119 625000000 2184294087513 5000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410416377/10000000000 : ℝ)^2183 ≤ (1400688941119/3125000000000 : ℝ)^1671 := by
    have hnat : (5410416377 : ℕ)^2183*3125000000000^1671 ≤ 1400688941119^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410416377 10000000000 1400688941119 3125000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1908851583/10000000000 : ℝ)^2183 ≤ (11492072116917/100000000000000 : ℝ)^1671 := by
    have hnat : (1908851583 : ℕ)^2183*100000000000000^1671 ≤ 11492072116917^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908851583 10000000000 11492072116917 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331570119/625000000 : ℝ), (5410416377/10000000000 : ℝ), (-1908851583/10000000000 : ℝ)] ![(2184294087513/5000000000000 : ℝ), (1400688941119/3125000000000 : ℝ), (11492072116917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331570119/625000000 : ℝ)|^2183 ≤ (2184294087513/5000000000000 : ℝ)^1671
        have hw : |(331570119/625000000 : ℝ)|=(331570119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410416377/10000000000 : ℝ)|^2183 ≤ (1400688941119/3125000000000 : ℝ)^1671
        have hw : |(5410416377/10000000000 : ℝ)|=(5410416377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1908851583/10000000000 : ℝ)|^2183 ≤ (11492072116917/100000000000000 : ℝ)^1671
        have hw : |(-1908851583/10000000000 : ℝ)|=(1908851583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s4_7 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310073297/10000000000 : ℝ)*x 0 + (898060837/2000000000 : ℝ)*x 1 + (413649183/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310073297/10000000000 : ℝ)^2183 ≤ (16651736647301/50000000000000 : ℝ)^1671 := by
    have hnat : (4310073297 : ℕ)^2183*50000000000000^1671 ≤ 16651736647301^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310073297 10000000000 16651736647301 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898060837/2000000000 : ℝ)^2183 ≤ (35134347343101/100000000000000 : ℝ)^1671 := by
    have hnat : (898060837 : ℕ)^2183*100000000000000^1671 ≤ 35134347343101^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898060837 2000000000 35134347343101 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413649183/1000000000 : ℝ)^2183 ≤ (31562179344167/100000000000000 : ℝ)^1671 := by
    have hnat : (413649183 : ℕ)^2183*100000000000000^1671 ≤ 31562179344167^1671*1000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413649183 1000000000 31562179344167 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310073297/10000000000 : ℝ), (898060837/2000000000 : ℝ), (413649183/1000000000 : ℝ)] ![(16651736647301/50000000000000 : ℝ), (35134347343101/100000000000000 : ℝ), (31562179344167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310073297/10000000000 : ℝ)|^2183 ≤ (16651736647301/50000000000000 : ℝ)^1671
        have hw : |(4310073297/10000000000 : ℝ)|=(4310073297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898060837/2000000000 : ℝ)|^2183 ≤ (35134347343101/100000000000000 : ℝ)^1671
        have hw : |(898060837/2000000000 : ℝ)|=(898060837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413649183/1000000000 : ℝ)|^2183 ≤ (31562179344167/100000000000000 : ℝ)^1671
        have hw : |(413649183/1000000000 : ℝ)|=(413649183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1406_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (187/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14779/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (187/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1109/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (187/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1109/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (187/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1109/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (187/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1109/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (187/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1109/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (187/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1109/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1109/10000 : ℝ) ^ (4365/1024 : ℝ) ≤ (8488563047397669/100000000000000000000 : ℝ) := by
    have hpowers : (1109/10000 : ℝ)^4365 ≤ (8488563047397669/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1109 : ℕ)^4365*100000000000000000000^1024 ≤ 8488563047397669^1024*10000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1109 10000 8488563047397669 100000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1109/10000 : ℝ)) (X := (8488563047397669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (187/1250 : ℝ) ^ (4365/1024 : ℝ) ≤ (30407783973569193/100000000000000000000 : ℝ) := by
    have hpowers : (187/1250 : ℝ)^4365 ≤ (30407783973569193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (187 : ℕ)^4365*100000000000000000000^1024 ≤ 30407783973569193^1024*1250^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        187 1250 30407783973569193 100000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (187/1250 : ℝ)) (X := (30407783973569193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008488563047397669/50000000000000000000 : ℝ) ≤ (5000199123112517/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50008488563047397669/50000000000000000000 : ℝ)^1024 ≤ (5000199123112517/5000000000000000 : ℝ)^4365 := by
      have hnat : (50008488563047397669 : ℕ)^1024*5000000000000000^4365 ≤ 5000199123112517^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008488563047397669 50000000000000000000 5000199123112517 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199123112517/5000000000000000 : ℝ)) (X := (50008488563047397669/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019448173510483431/50000000000000000000 : ℝ) ≤ (5000456173330223/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50019448173510483431/50000000000000000000 : ℝ)^1024 ≤ (5000456173330223/5000000000000000 : ℝ)^4365 := by
      have hnat : (50019448173510483431 : ℕ)^1024*5000000000000000^4365 ≤ 5000456173330223^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019448173510483431 50000000000000000000 5000456173330223 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000456173330223/5000000000000000 : ℝ)) (X := (50019448173510483431/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030407783973569193/50000000000000000000 : ℝ) ≤ (5000713223547929/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50030407783973569193/50000000000000000000 : ℝ)^1024 ≤ (5000713223547929/5000000000000000 : ℝ)^4365 := by
      have hnat : (50030407783973569193 : ℕ)^1024*5000000000000000^4365 ≤ 5000713223547929^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030407783973569193 50000000000000000000 5000713223547929 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000713223547929/5000000000000000 : ℝ)) (X := (50030407783973569193/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8488563047397669/100000000000000000000 : ℝ) ≤ ((644835641087224057/645000000000000000 : ℝ)+2*(42841702951/32250000000000 : ℝ)*(1109/10000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (644835641087224057/645000000000000000 : ℝ)+2*(42841702951/32250000000000 : ℝ)*(1109/10000 : ℝ)=(5000199123112517/5000000000000000 : ℝ) by norm_num, show 1+2*(8488563047397669/100000000000000000000 : ℝ)=(50008488563047397669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30407783973569193/100000000000000000000 : ℝ)+(8488563047397669/100000000000000000000 : ℝ) ≤ ((644835641087224057/645000000000000000 : ℝ)+(42841702951/32250000000000 : ℝ)*((187/1250 : ℝ)+(1109/10000 : ℝ)))^(4365/1024 : ℝ) := by
    rw [show (644835641087224057/645000000000000000 : ℝ)+(42841702951/32250000000000 : ℝ)*((187/1250 : ℝ)+(1109/10000 : ℝ))=(5000456173330223/5000000000000000 : ℝ) by norm_num, show 1+(30407783973569193/100000000000000000000 : ℝ)+(8488563047397669/100000000000000000000 : ℝ)=(50019448173510483431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30407783973569193/100000000000000000000 : ℝ) ≤ ((644835641087224057/645000000000000000 : ℝ)+2*(42841702951/32250000000000 : ℝ)*(187/1250 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (644835641087224057/645000000000000000 : ℝ)+2*(42841702951/32250000000000 : ℝ)*(187/1250 : ℝ)=(5000713223547929/5000000000000000 : ℝ) by norm_num, show 1+2*(30407783973569193/100000000000000000000 : ℝ)=(50030407783973569193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (644835641087224057/645000000000000000 : ℝ)*(X 1 0+X 2 0)+(42841702951/32250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (187/1250 : ℝ)) (c := (644835641087224057/645000000000000000 : ℝ)) (alpha := (42841702951/32250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (644835641087224057/645000000000000000 : ℝ)*(X 0 1+X 2 1)+(42841702951/32250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (187/1250 : ℝ)) (c := (644835641087224057/645000000000000000 : ℝ)) (alpha := (42841702951/32250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (644835641087224057/645000000000000000 : ℝ)*(X 0 2+X 1 2)+(42841702951/32250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (187/1250 : ℝ)) (c := (644835641087224057/645000000000000000 : ℝ)) (alpha := (42841702951/32250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989758821/10000000000 : ℝ)*X 0 0+(1352757213/2500000000 : ℝ)*X 0 1+(81951069/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348220079/10000000000 : ℝ)*X 1 0+(-32412487/156250000 : ℝ)*X 1 1+(1048973679/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33426373/62500000 : ℝ)*X 2 0+(5244868499/10000000000 : ℝ)*X 2 1+(-2074399563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310047647/10000000000 : ℝ)*X 0 0+(1033794267/2500000000 : ℝ)*X 0 1+(4491611507/10000000000 : ℝ)*X 0 2+(4310047647/10000000000 : ℝ)*X 1 0+(1033794267/2500000000 : ℝ)*X 1 1+(4491611507/10000000000 : ℝ)*X 1 2+(4310047647/10000000000 : ℝ)*X 2 0+(1033794267/2500000000 : ℝ)*X 2 1+(4491611507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1989770987/10000000000 : ℝ)*X 0 0+(327842361/625000000 : ℝ)*X 0 1+(2705208157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305121923/10000000000 : ℝ)*X 1 0+(-1908851441/10000000000 : ℝ)*X 1 1+(5410416461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331570119/625000000 : ℝ)*X 2 0+(5410416377/10000000000 : ℝ)*X 2 1+(-1908851583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310073297/10000000000 : ℝ)*X 0 0+(898060837/2000000000 : ℝ)*X 0 1+(413649183/1000000000 : ℝ)*X 0 2+(4310073297/10000000000 : ℝ)*X 1 0+(898060837/2000000000 : ℝ)*X 1 1+(413649183/1000000000 : ℝ)*X 1 2+(4310073297/10000000000 : ℝ)*X 2 0+(898060837/2000000000 : ℝ)*X 2 1+(413649183/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (560043789852209210283/107500000000000000000000000 : ℝ) := by norm_num
    linear_combination (388841197/25000000000000 : ℝ)*(base19) + (1966973/156250000000 : ℝ)*(base23) + (436730989/100000000000000 : ℝ)*(upper3) + (83573717/100000000000000 : ℝ)*(lower4) + (441196723244289/10000000000000 : ℝ)*(major0) + (441196723244289/10000000000000 : ℝ)*(major1) + (441196723244289/10000000000000 : ℝ)*(major2) + (6018319261097219/100000000000000 : ℝ)*(sp0) + (6018335237028933/100000000000000 : ℝ)*(sp1) + (3009167532651213/50000000000000 : ℝ)*(sp2) + (70139479071233/2500000000000 : ℝ)*(sp3) + (17531296503/100000000000000 : ℝ)*(sp4) + (18729143/4000000000000 : ℝ)*(sp6) + (9167992871/50000000000000 : ℝ)*(sp7) + (1402798749417531/50000000000000 : ℝ)*(f.failure) + (3009168396196861/50000000000000 : ℝ)*(f.sum) + (36854434671/107500000000000000000000000 : ℝ)*base65 + (12486928142086509/2150000000000000000000000000000 : ℝ)*base68 + (1287995672086509/2150000000000000000000000000000 : ℝ)*base70 + (3806367031663491/2150000000000000000000000000000 : ℝ)*base71 + (517683469519/107500000000000000000000000 : ℝ)*base74 + (17523478773436509/2150000000000000000000000000000 : ℝ)*base76 + (13649916769713491/2150000000000000000000000000000 : ℝ)*base77 + (12762518276963491/2150000000000000000000000000000 : ℝ)*base79 + (228599380503/215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (70754997/5000000000000000000000 : ℝ)*base89 + (70754997/5000000000000000000000 : ℝ)*base91 + (70754997/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11588787585141493844733183/1343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1387134881/100000000000000 : ℝ)*(base19) + (1351521169/100000000000000 : ℝ)*(base23) + (19922437/100000000000000 : ℝ)*(upper2) + (41716133/25000000000000 : ℝ)*(upper3) + (221602377/100000000000000 : ℝ)*(upper5) + (555576343998273/12500000000000 : ℝ)*(major0) + (555576343998273/12500000000000 : ℝ)*(major1) + (555576343998273/12500000000000 : ℝ)*(major2) + (33760390387/100000000000000 : ℝ)*(sp1) + (27427065949/100000000000000 : ℝ)*(sp2) + (3031432749926499/50000000000000 : ℝ)*(sp4) + (606283035232773/10000000000000 : ℝ)*(sp5) + (151570918031647/2500000000000 : ℝ)*(sp6) + (1413177858322781/50000000000000 : ℝ)*(sp7) + (1413177858322781/50000000000000 : ℝ)*(f.failure) + (3031432749926499/50000000000000 : ℝ)*(f.sum) + (445116087743/134375000000000000000000000 : ℝ)*base66 + (15466391962703813/2687500000000000000000000000000 : ℝ)*base68 + (51332472700328813/2687500000000000000000000000000 : ℝ)*base70 + (586547958766313/2687500000000000000000000000000 : ℝ)*base72 + (303099334143/134375000000000000000000000 : ℝ)*base74 + (21006381449641313/2687500000000000000000000000000 : ℝ)*base76 + (23590759115703813/2687500000000000000000000000000 : ℝ)*base78 + (28777538782016313/2687500000000000000000000000000 : ℝ)*base80 + (5103232540319/1075000000000000000000000000 : ℝ)*base82 + (58461747/5000000000000000000000 : ℝ)*base89 + (58461747/5000000000000000000000 : ℝ)*base91 + (58461747/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1406_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (187/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1406_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1406_s5_0 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989918651/10000000000 : ℝ)*x 0 + (676203513/1250000000 : ℝ)*x 1 + (2623081873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989918651/10000000000 : ℝ)^2183 ≤ (3033444994417/25000000000000 : ℝ)^1671 := by
    have hnat : (1989918651 : ℕ)^2183*25000000000000^1671 ≤ 3033444994417^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989918651 10000000000 3033444994417 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676203513/1250000000 : ℝ)^2183 ≤ (44813515011893/100000000000000 : ℝ)^1671 := by
    have hnat : (676203513 : ℕ)^2183*100000000000000^1671 ≤ 44813515011893^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676203513 1250000000 44813515011893 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623081873/5000000000 : ℝ)^2183 ≤ (21526352500133/50000000000000 : ℝ)^1671 := by
    have hnat : (2623081873 : ℕ)^2183*50000000000000^1671 ≤ 21526352500133^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623081873 5000000000 21526352500133 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989918651/10000000000 : ℝ), (676203513/1250000000 : ℝ), (2623081873/5000000000 : ℝ)] ![(3033444994417/25000000000000 : ℝ), (44813515011893/100000000000000 : ℝ), (21526352500133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989918651/10000000000 : ℝ)|^2183 ≤ (3033444994417/25000000000000 : ℝ)^1671
        have hw : |(-1989918651/10000000000 : ℝ)|=(1989918651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676203513/1250000000 : ℝ)|^2183 ≤ (44813515011893/100000000000000 : ℝ)^1671
        have hw : |(676203513/1250000000 : ℝ)|=(676203513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623081873/5000000000 : ℝ)|^2183 ≤ (21526352500133/50000000000000 : ℝ)^1671
        have hw : |(2623081873/5000000000 : ℝ)|=(2623081873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_1 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347858589/10000000000 : ℝ)*x 0 + (-1036580579/5000000000 : ℝ)*x 1 + (5246163649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347858589/10000000000 : ℝ)^2183 ≤ (44146200343531/100000000000000 : ℝ)^1671 := by
    have hnat : (5347858589 : ℕ)^2183*100000000000000^1671 ≤ 44146200343531^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347858589 10000000000 44146200343531 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036580579/5000000000 : ℝ)^2183 ≤ (2560219137649/20000000000000 : ℝ)^1671 := by
    have hnat : (1036580579 : ℕ)^2183*20000000000000^1671 ≤ 2560219137649^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036580579 5000000000 2560219137649 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246163649/10000000000 : ℝ)^2183 ≤ (43052703960327/100000000000000 : ℝ)^1671 := by
    have hnat : (5246163649 : ℕ)^2183*100000000000000^1671 ≤ 43052703960327^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246163649 10000000000 43052703960327 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347858589/10000000000 : ℝ), (-1036580579/5000000000 : ℝ), (5246163649/10000000000 : ℝ)] ![(44146200343531/100000000000000 : ℝ), (2560219137649/20000000000000 : ℝ), (43052703960327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347858589/10000000000 : ℝ)|^2183 ≤ (44146200343531/100000000000000 : ℝ)^1671
        have hw : |(5347858589/10000000000 : ℝ)|=(5347858589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036580579/5000000000 : ℝ)|^2183 ≤ (2560219137649/20000000000000 : ℝ)^1671
        have hw : |(-1036580579/5000000000 : ℝ)|=(1036580579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246163649/10000000000 : ℝ)|^2183 ≤ (43052703960327/100000000000000 : ℝ)^1671
        have hw : |(5246163649/10000000000 : ℝ)|=(5246163649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_2 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069571699/2000000000 : ℝ)*x 0 + (5246163613/10000000000 : ℝ)*x 1 + (-207316133/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069571699/2000000000 : ℝ)^2183 ≤ (4414619932981/10000000000000 : ℝ)^1671 := by
    have hnat : (1069571699 : ℕ)^2183*10000000000000^1671 ≤ 4414619932981^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069571699 2000000000 4414619932981 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246163613/10000000000 : ℝ)^2183 ≤ (43052703574371/100000000000000 : ℝ)^1671 := by
    have hnat : (5246163613 : ℕ)^2183*100000000000000^1671 ≤ 43052703574371^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246163613 10000000000 43052703574371 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207316133/1000000000 : ℝ)^2183 ≤ (12801097075703/100000000000000 : ℝ)^1671 := by
    have hnat : (207316133 : ℕ)^2183*100000000000000^1671 ≤ 12801097075703^1671*1000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207316133 1000000000 12801097075703 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069571699/2000000000 : ℝ), (5246163613/10000000000 : ℝ), (-207316133/1000000000 : ℝ)] ![(4414619932981/10000000000000 : ℝ), (43052703574371/100000000000000 : ℝ), (12801097075703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069571699/2000000000 : ℝ)|^2183 ≤ (4414619932981/10000000000000 : ℝ)^1671
        have hw : |(1069571699/2000000000 : ℝ)|=(1069571699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246163613/10000000000 : ℝ)|^2183 ≤ (43052703574371/100000000000000 : ℝ)^1671
        have hw : |(5246163613/10000000000 : ℝ)|=(5246163613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207316133/1000000000 : ℝ)|^2183 ≤ (12801097075703/100000000000000 : ℝ)^1671
        have hw : |(-207316133/1000000000 : ℝ)|=(207316133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_3 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155071347/5000000000 : ℝ)*x 0 + (2069029203/5000000000 : ℝ)*x 1 + (2244353903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155071347/5000000000 : ℝ)^2183 ≤ (33304173820067/100000000000000 : ℝ)^1671 := by
    have hnat : (2155071347 : ℕ)^2183*100000000000000^1671 ≤ 33304173820067^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155071347 5000000000 33304173820067 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069029203/5000000000 : ℝ)^2183 ≤ (31577796025997/100000000000000 : ℝ)^1671 := by
    have hnat : (2069029203 : ℕ)^2183*100000000000000^1671 ≤ 31577796025997^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069029203 5000000000 31577796025997 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244353903/5000000000 : ℝ)^2183 ≤ (35118030138343/100000000000000 : ℝ)^1671 := by
    have hnat : (2244353903 : ℕ)^2183*100000000000000^1671 ≤ 35118030138343^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244353903 5000000000 35118030138343 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155071347/5000000000 : ℝ), (2069029203/5000000000 : ℝ), (2244353903/5000000000 : ℝ)] ![(33304173820067/100000000000000 : ℝ), (31577796025997/100000000000000 : ℝ), (35118030138343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155071347/5000000000 : ℝ)|^2183 ≤ (33304173820067/100000000000000 : ℝ)^1671
        have hw : |(2155071347/5000000000 : ℝ)|=(2155071347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069029203/5000000000 : ℝ)|^2183 ≤ (31577796025997/100000000000000 : ℝ)^1671
        have hw : |(2069029203/5000000000 : ℝ)|=(2069029203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244353903/5000000000 : ℝ)|^2183 ≤ (35118030138343/100000000000000 : ℝ)^1671
        have hw : |(2244353903/5000000000 : ℝ)|=(2244353903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_4 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989930643/10000000000 : ℝ)*x 0 + (655844207/1250000000 : ℝ)*x 1 + (5409034867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989930643/10000000000 : ℝ)^2183 ≤ (606693775277/5000000000000 : ℝ)^1671 := by
    have hnat : (1989930643 : ℕ)^2183*5000000000000^1671 ≤ 606693775277^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989930643 10000000000 606693775277 5000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655844207/1250000000 : ℝ)^2183 ≤ (21529514771467/50000000000000 : ℝ)^1671 := by
    have hnat : (655844207 : ℕ)^2183*50000000000000^1671 ≤ 21529514771467^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655844207 1250000000 21529514771467 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409034867/10000000000 : ℝ)^2183 ≤ (22403547470533/50000000000000 : ℝ)^1671 := by
    have hnat : (5409034867 : ℕ)^2183*50000000000000^1671 ≤ 22403547470533^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409034867 10000000000 22403547470533 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989930643/10000000000 : ℝ), (655844207/1250000000 : ℝ), (5409034867/10000000000 : ℝ)] ![(606693775277/5000000000000 : ℝ), (21529514771467/50000000000000 : ℝ), (22403547470533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989930643/10000000000 : ℝ)|^2183 ≤ (606693775277/5000000000000 : ℝ)^1671
        have hw : |(-1989930643/10000000000 : ℝ)|=(1989930643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655844207/1250000000 : ℝ)|^2183 ≤ (21529514771467/50000000000000 : ℝ)^1671
        have hw : |(655844207/1250000000 : ℝ)|=(655844207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409034867/10000000000 : ℝ)|^2183 ≤ (22403547470533/50000000000000 : ℝ)^1671
        have hw : |(5409034867/10000000000 : ℝ)|=(5409034867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_5 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652729899/5000000000 : ℝ)*x 0 + (-1910290199/10000000000 : ℝ)*x 1 + (1352258717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652729899/5000000000 : ℝ)^2183 ≤ (21844758389051/50000000000000 : ℝ)^1671 := by
    have hnat : (2652729899 : ℕ)^2183*50000000000000^1671 ≤ 21844758389051^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652729899 5000000000 21844758389051 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1910290199/10000000000 : ℝ)^2183 ≤ (11503388261423/100000000000000 : ℝ)^1671 := by
    have hnat : (1910290199 : ℕ)^2183*100000000000000^1671 ≤ 11503388261423^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910290199 10000000000 11503388261423 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352258717/2500000000 : ℝ)^2183 ≤ (2800443434493/6250000000000 : ℝ)^1671 := by
    have hnat : (1352258717 : ℕ)^2183*6250000000000^1671 ≤ 2800443434493^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352258717 2500000000 2800443434493 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652729899/5000000000 : ℝ), (-1910290199/10000000000 : ℝ), (1352258717/2500000000 : ℝ)] ![(21844758389051/50000000000000 : ℝ), (11503388261423/100000000000000 : ℝ), (2800443434493/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652729899/5000000000 : ℝ)|^2183 ≤ (21844758389051/50000000000000 : ℝ)^1671
        have hw : |(2652729899/5000000000 : ℝ)|=(2652729899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1910290199/10000000000 : ℝ)|^2183 ≤ (11503388261423/100000000000000 : ℝ)^1671
        have hw : |(-1910290199/10000000000 : ℝ)|=(1910290199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352258717/2500000000 : ℝ)|^2183 ≤ (2800443434493/6250000000000 : ℝ)^1671
        have hw : |(1352258717/2500000000 : ℝ)|=(1352258717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_6 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061091959/2000000000 : ℝ)*x 0 + (5409034871/10000000000 : ℝ)*x 1 + (-1910290199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061091959/2000000000 : ℝ)^2183 ≤ (10922379186457/25000000000000 : ℝ)^1671 := by
    have hnat : (1061091959 : ℕ)^2183*25000000000000^1671 ≤ 10922379186457^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061091959 2000000000 10922379186457 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409034871/10000000000 : ℝ)^2183 ≤ (22403547492177/50000000000000 : ℝ)^1671 := by
    have hnat : (5409034871 : ℕ)^2183*50000000000000^1671 ≤ 22403547492177^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409034871 10000000000 22403547492177 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910290199/10000000000 : ℝ)^2183 ≤ (11503388261423/100000000000000 : ℝ)^1671 := by
    have hnat : (1910290199 : ℕ)^2183*100000000000000^1671 ≤ 11503388261423^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910290199 10000000000 11503388261423 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061091959/2000000000 : ℝ), (5409034871/10000000000 : ℝ), (-1910290199/10000000000 : ℝ)] ![(10922379186457/25000000000000 : ℝ), (22403547492177/50000000000000 : ℝ), (11503388261423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061091959/2000000000 : ℝ)|^2183 ≤ (10922379186457/25000000000000 : ℝ)^1671
        have hw : |(1061091959/2000000000 : ℝ)|=(1061091959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409034871/10000000000 : ℝ)|^2183 ≤ (22403547492177/50000000000000 : ℝ)^1671
        have hw : |(5409034871/10000000000 : ℝ)|=(5409034871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1910290199/10000000000 : ℝ)|^2183 ≤ (11503388261423/100000000000000 : ℝ)^1671
        have hw : |(-1910290199/10000000000 : ℝ)|=(1910290199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s5_7 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310168111/10000000000 : ℝ)*x 0 + (35058143/78125000 : ℝ)*x 1 + (4139329991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310168111/10000000000 : ℝ)^2183 ≤ (1040763449747/3125000000000 : ℝ)^1671 := by
    have hnat : (4310168111 : ℕ)^2183*3125000000000^1671 ≤ 1040763449747^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310168111 10000000000 1040763449747 3125000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35058143/78125000 : ℝ)^2183 ≤ (17552548109127/50000000000000 : ℝ)^1671 := by
    have hnat : (35058143 : ℕ)^2183*50000000000000^1671 ≤ 17552548109127^1671*78125000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35058143 78125000 17552548109127 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139329991/10000000000 : ℝ)^2183 ≤ (31590473371439/100000000000000 : ℝ)^1671 := by
    have hnat : (4139329991 : ℕ)^2183*100000000000000^1671 ≤ 31590473371439^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139329991 10000000000 31590473371439 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310168111/10000000000 : ℝ), (35058143/78125000 : ℝ), (4139329991/10000000000 : ℝ)] ![(1040763449747/3125000000000 : ℝ), (17552548109127/50000000000000 : ℝ), (31590473371439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310168111/10000000000 : ℝ)|^2183 ≤ (1040763449747/3125000000000 : ℝ)^1671
        have hw : |(4310168111/10000000000 : ℝ)|=(4310168111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35058143/78125000 : ℝ)|^2183 ≤ (17552548109127/50000000000000 : ℝ)^1671
        have hw : |(35058143/78125000 : ℝ)|=(35058143/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139329991/10000000000 : ℝ)|^2183 ≤ (31590473371439/100000000000000 : ℝ)^1671
        have hw : |(4139329991/10000000000 : ℝ)|=(4139329991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1406_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (563/5000 : ℝ) ^ (4365/1024 : ℝ) ≤ (4528633214549287/50000000000000000000 : ℝ) := by
    have hpowers : (563/5000 : ℝ)^4365 ≤ (4528633214549287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (563 : ℕ)^4365*50000000000000000000^1024 ≤ 4528633214549287^1024*5000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 5000 4528633214549287 50000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/5000 : ℝ)) (X := (4528633214549287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14779/100000 : ℝ) ^ (4365/1024 : ℝ) ≤ (28870203373317851/100000000000000000000 : ℝ) := by
    have hpowers : (14779/100000 : ℝ)^4365 ≤ (28870203373317851/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14779 : ℕ)^4365*100000000000000000000^1024 ≤ 28870203373317851^1024*100000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14779 100000 28870203373317851 100000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14779/100000 : ℝ)) (X := (28870203373317851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004528633214549287/25000000000000000000 : ℝ) ≤ (5000212462724587/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (25004528633214549287/25000000000000000000 : ℝ)^1024 ≤ (5000212462724587/5000000000000000 : ℝ)^4365 := by
      have hnat : (25004528633214549287 : ℕ)^1024*5000000000000000^4365 ≤ 5000212462724587^4365*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004528633214549287 25000000000000000000 5000212462724587 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000212462724587/5000000000000000 : ℝ)) (X := (25004528633214549287/25000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001517098792096657/4000000000000000000 : ℝ) ≤ (1250111203015611/1250000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (4001517098792096657/4000000000000000000 : ℝ)^1024 ≤ (1250111203015611/1250000000000000 : ℝ)^4365 := by
      have hnat : (4001517098792096657 : ℕ)^1024*1250000000000000^4365 ≤ 1250111203015611^4365*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001517098792096657 4000000000000000000 1250111203015611 1250000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250111203015611/1250000000000000 : ℝ)) (X := (4001517098792096657/4000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028870203373317851/50000000000000000000 : ℝ) ≤ (5000677161400301/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50028870203373317851/50000000000000000000 : ℝ)^1024 ≤ (5000677161400301/5000000000000000 : ℝ)^4365 := by
      have hnat : (50028870203373317851 : ℕ)^1024*5000000000000000^4365 ≤ 5000677161400301^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028870203373317851 50000000000000000000 5000677161400301 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000677161400301/5000000000000000 : ℝ)) (X := (50028870203373317851/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4528633214549287/50000000000000000000 : ℝ) ≤ ((17590515149239282013/17595000000000000000 : ℝ)+2*(232349337857/175950000000000 : ℝ)*(563/5000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (17590515149239282013/17595000000000000000 : ℝ)+2*(232349337857/175950000000000 : ℝ)*(563/5000 : ℝ)=(5000212462724587/5000000000000000 : ℝ) by norm_num, show 1+2*(4528633214549287/50000000000000000000 : ℝ)=(25004528633214549287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28870203373317851/100000000000000000000 : ℝ)+(4528633214549287/50000000000000000000 : ℝ) ≤ ((17590515149239282013/17595000000000000000 : ℝ)+(232349337857/175950000000000 : ℝ)*((14779/100000 : ℝ)+(563/5000 : ℝ)))^(4365/1024 : ℝ) := by
    rw [show (17590515149239282013/17595000000000000000 : ℝ)+(232349337857/175950000000000 : ℝ)*((14779/100000 : ℝ)+(563/5000 : ℝ))=(1250111203015611/1250000000000000 : ℝ) by norm_num, show 1+(28870203373317851/100000000000000000000 : ℝ)+(4528633214549287/50000000000000000000 : ℝ)=(4001517098792096657/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28870203373317851/100000000000000000000 : ℝ) ≤ ((17590515149239282013/17595000000000000000 : ℝ)+2*(232349337857/175950000000000 : ℝ)*(14779/100000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (17590515149239282013/17595000000000000000 : ℝ)+2*(232349337857/175950000000000 : ℝ)*(14779/100000 : ℝ)=(5000677161400301/5000000000000000 : ℝ) by norm_num, show 1+2*(28870203373317851/100000000000000000000 : ℝ)=(50028870203373317851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17590515149239282013/17595000000000000000 : ℝ)*(X 1 0+X 2 0)+(232349337857/175950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (17590515149239282013/17595000000000000000 : ℝ)) (alpha := (232349337857/175950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17590515149239282013/17595000000000000000 : ℝ)*(X 0 1+X 2 1)+(232349337857/175950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (17590515149239282013/17595000000000000000 : ℝ)) (alpha := (232349337857/175950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17590515149239282013/17595000000000000000 : ℝ)*(X 0 2+X 1 2)+(232349337857/175950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (17590515149239282013/17595000000000000000 : ℝ)) (alpha := (232349337857/175950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989918651/10000000000 : ℝ)*X 0 0+(676203513/1250000000 : ℝ)*X 0 1+(2623081873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347858589/10000000000 : ℝ)*X 1 0+(-1036580579/5000000000 : ℝ)*X 1 1+(5246163649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069571699/2000000000 : ℝ)*X 2 0+(5246163613/10000000000 : ℝ)*X 2 1+(-207316133/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155071347/5000000000 : ℝ)*X 0 0+(2069029203/5000000000 : ℝ)*X 0 1+(2244353903/5000000000 : ℝ)*X 0 2+(2155071347/5000000000 : ℝ)*X 1 0+(2069029203/5000000000 : ℝ)*X 1 1+(2244353903/5000000000 : ℝ)*X 1 2+(2155071347/5000000000 : ℝ)*X 2 0+(2069029203/5000000000 : ℝ)*X 2 1+(2244353903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1989930643/10000000000 : ℝ)*X 0 0+(655844207/1250000000 : ℝ)*X 0 1+(5409034867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652729899/5000000000 : ℝ)*X 1 0+(-1910290199/10000000000 : ℝ)*X 1 1+(1352258717/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061091959/2000000000 : ℝ)*X 2 0+(5409034871/10000000000 : ℝ)*X 2 1+(-1910290199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310168111/10000000000 : ℝ)*X 0 0+(35058143/78125000 : ℝ)*X 0 1+(4139329991/10000000000 : ℝ)*X 0 2+(4310168111/10000000000 : ℝ)*X 1 0+(35058143/78125000 : ℝ)*X 1 1+(4139329991/10000000000 : ℝ)*X 1 2+(4310168111/10000000000 : ℝ)*X 2 0+(35058143/78125000 : ℝ)*X 2 1+(4139329991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87941712290778151572896083/24437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (360582347/100000000000000 : ℝ)*(base19) + (281187829/100000000000000 : ℝ)*(base23) + (47005529/100000000000000 : ℝ)*(lower2) + (12410313/20000000000000 : ℝ)*(lower4) + (25797573/12500000000000 : ℝ)*(lower5) + (1121177393362673/25000000000000 : ℝ)*(major0) + (1121177393362673/25000000000000 : ℝ)*(major1) + (4484709573450693/100000000000000 : ℝ)*(major2) + (6117557338288029/100000000000000 : ℝ)*(sp0) + (3058781929443529/50000000000000 : ℝ)*(sp1) + (764695492285197/12500000000000 : ℝ)*(sp2) + (712962977689617/25000000000000 : ℝ)*(sp3) + (107518459/1562500000000 : ℝ)*(sp4) + (2896718909/100000000000000 : ℝ)*(sp7) + (1425927403738689/50000000000000 : ℝ)*(f.failure) + (1223512843893881/20000000000000 : ℝ)*(f.sum) + (22169092801553/3519000000000000000000000000 : ℝ)*base65 + (1998606623569025749/439875000000000000000000000000000 : ℝ)*base67 + (7483462432928185009/1759500000000000000000000000000000 : ℝ)*base69 + (625203252356349251/439875000000000000000000000000000 : ℝ)*base72 + (21672895727969/3519000000000000000000000000 : ℝ)*base73 + (18725206794723814991/1759500000000000000000000000000000 : ℝ)*base76 + (2745643728953024251/439875000000000000000000000000000 : ℝ)*base78 + (3596788930865399251/439875000000000000000000000000000 : ℝ)*base80 + (62981076051623/17595000000000000000000000000 : ℝ)*base81 + (54912143/5000000000000000000000 : ℝ)*base89 + (54912143/5000000000000000000000 : ℝ)*base91 + (4912143/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32905418858637597160018041/2875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195499323/10000000000000 : ℝ)*(base19) + (26422389/1250000000000 : ℝ)*(base23) + (117450163/50000000000000 : ℝ)*(upper3) + (18366179/25000000000000 : ℝ)*(lower4) + (3665737/1562500000000 : ℝ)*(upper5) + (2258694291632993/50000000000000 : ℝ)*(major0) + (2258694291632993/50000000000000 : ℝ)*(major1) + (2258694291632993/50000000000000 : ℝ)*(major2) + (40722140347/100000000000000 : ℝ)*(sp1) + (10925479963/25000000000000 : ℝ)*(sp2) + (3081070595623261/50000000000000 : ℝ)*(sp4) + (1232419702822589/20000000000000 : ℝ)*(sp5) + (123241907510711/2000000000000 : ℝ)*(sp6) + (1436317796886671/50000000000000 : ℝ)*(sp7) + (1436317796886671/50000000000000 : ℝ)*(f.failure) + (3081070595623261/50000000000000 : ℝ)*(f.sum) + (11477288339873/2199375000000000000000000000 : ℝ)*base65 + (7002483859322354909/879750000000000000000000000000000 : ℝ)*base67 + (1911616530633645091/879750000000000000000000000000000 : ℝ)*base70 + (2812297902936104909/879750000000000000000000000000000 : ℝ)*base71 + (48088243193239/17595000000000000000000000000 : ℝ)*base73 + (2652236249518604909/879750000000000000000000000000000 : ℝ)*base75 + (9015169265450354909/879750000000000000000000000000000 : ℝ)*base77 + (3162257516174145091/879750000000000000000000000000000 : ℝ)*base80 + (5966232428909/4398750000000000000000000000 : ℝ)*base82 + (13417823/5000000000000000000000 : ℝ)*base90 + (13417823/5000000000000000000000 : ℝ)*base92 + (13417823/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1406_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1406_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1406_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1406_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1406_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1406_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1406_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

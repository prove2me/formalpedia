-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1509_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:56.150241+00:00
-- url     : https://prove2.me/submissions/25b854fe-09e0-4562-ad62-e36e7aa5355b

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
theorem support_rectangle_w1509_s0_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1649434/9765625 : ℝ)*x 0 + (5915141993/10000000000 : ℝ)*x 1 + (1213507981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649434/9765625 : ℝ)^4515 ≤ (2004981478437/20000000000000 : ℝ)^3491 := by
    have hnat : (1649434 : ℕ)^4515*20000000000000^3491 ≤ 2004981478437^3491*9765625^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649434 9765625 2004981478437 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5915141993/10000000000 : ℝ)^4515 ≤ (25354012786937/50000000000000 : ℝ)^3491 := by
    have hnat : (5915141993 : ℕ)^4515*50000000000000^3491 ≤ 25354012786937^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5915141993 10000000000 25354012786937 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213507981/2500000000 : ℝ)^4515 ≤ (3926706701963/10000000000000 : ℝ)^3491 := by
    have hnat : (1213507981 : ℕ)^4515*10000000000000^3491 ≤ 3926706701963^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213507981 2500000000 3926706701963 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1649434/9765625 : ℝ), (5915141993/10000000000 : ℝ), (1213507981/2500000000 : ℝ)] ![(2004981478437/20000000000000 : ℝ), (25354012786937/50000000000000 : ℝ), (3926706701963/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1649434/9765625 : ℝ)|^4515 ≤ (2004981478437/20000000000000 : ℝ)^3491
        have hw : |(-1649434/9765625 : ℝ)|=(1649434/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5915141993/10000000000 : ℝ)|^4515 ≤ (25354012786937/50000000000000 : ℝ)^3491
        have hw : |(5915141993/10000000000 : ℝ)|=(5915141993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1213507981/2500000000 : ℝ)|^4515 ≤ (3926706701963/10000000000000 : ℝ)^3491
        have hw : |(1213507981/2500000000 : ℝ)|=(1213507981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21914533/40000000 : ℝ)*x 0 + (-1784393/7812500 : ℝ)*x 1 + (606753983/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21914533/40000000 : ℝ)^4515 ≤ (22960856443191/50000000000000 : ℝ)^3491 := by
    have hnat : (21914533 : ℕ)^4515*50000000000000^3491 ≤ 22960856443191^3491*40000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21914533 40000000 22960856443191 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784393/7812500 : ℝ)^4515 ≤ (7405610352571/50000000000000 : ℝ)^3491 := by
    have hnat : (1784393 : ℕ)^4515*50000000000000^3491 ≤ 7405610352571^3491*7812500^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784393 7812500 7405610352571 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606753983/1250000000 : ℝ)^4515 ≤ (39267066391883/100000000000000 : ℝ)^3491 := by
    have hnat : (606753983 : ℕ)^4515*100000000000000^3491 ≤ 39267066391883^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606753983 1250000000 39267066391883 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21914533/40000000 : ℝ), (-1784393/7812500 : ℝ), (606753983/1250000000 : ℝ)] ![(22960856443191/50000000000000 : ℝ), (7405610352571/50000000000000 : ℝ), (39267066391883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21914533/40000000 : ℝ)|^4515 ≤ (22960856443191/50000000000000 : ℝ)^3491
        have hw : |(21914533/40000000 : ℝ)|=(21914533/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784393/7812500 : ℝ)|^4515 ≤ (7405610352571/50000000000000 : ℝ)^3491
        have hw : |(-1784393/7812500 : ℝ)|=(1784393/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606753983/1250000000 : ℝ)|^4515 ≤ (39267066391883/100000000000000 : ℝ)^3491
        have hw : |(606753983/1250000000 : ℝ)|=(606753983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5478633297/10000000000 : ℝ)*x 0 + (2427015939/5000000000 : ℝ)*x 1 + (-1142011481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5478633297/10000000000 : ℝ)^4515 ≤ (45921713395891/100000000000000 : ℝ)^3491 := by
    have hnat : (5478633297 : ℕ)^4515*100000000000000^3491 ≤ 45921713395891^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478633297 10000000000 45921713395891 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2427015939/5000000000 : ℝ)^4515 ≤ (39267066538357/100000000000000 : ℝ)^3491 := by
    have hnat : (2427015939 : ℕ)^4515*100000000000000^3491 ≤ 39267066538357^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427015939 5000000000 39267066538357 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142011481/5000000000 : ℝ)^4515 ≤ (1851402506371/12500000000000 : ℝ)^3491 := by
    have hnat : (1142011481 : ℕ)^4515*12500000000000^3491 ≤ 1851402506371^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142011481 5000000000 1851402506371 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5478633297/10000000000 : ℝ), (2427015939/5000000000 : ℝ), (-1142011481/5000000000 : ℝ)] ![(45921713395891/100000000000000 : ℝ), (39267066538357/100000000000000 : ℝ), (1851402506371/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5478633297/10000000000 : ℝ)|^4515 ≤ (45921713395891/100000000000000 : ℝ)^3491
        have hw : |(5478633297/10000000000 : ℝ)|=(5478633297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2427015939/5000000000 : ℝ)|^4515 ≤ (39267066538357/100000000000000 : ℝ)^3491
        have hw : |(2427015939/5000000000 : ℝ)|=(2427015939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1142011481/5000000000 : ℝ)|^4515 ≤ (1851402506371/12500000000000 : ℝ)^3491
        have hw : |(-1142011481/5000000000 : ℝ)|=(1142011481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145953639/10000000000 : ℝ)*x 0 + (38640613/125000000 : ℝ)*x 1 + (1098464219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145953639/10000000000 : ℝ)^4515 ≤ (32023136390033/100000000000000 : ℝ)^3491 := by
    have hnat : (4145953639 : ℕ)^4515*100000000000000^3491 ≤ 32023136390033^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145953639 10000000000 32023136390033 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38640613/125000000 : ℝ)^4515 ≤ (876268470907/4000000000000 : ℝ)^3491 := by
    have hnat : (38640613 : ℕ)^4515*4000000000000^3491 ≤ 876268470907^3491*125000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38640613 125000000 876268470907 4000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098464219/2000000000 : ℝ)^4515 ≤ (4607015182741/10000000000000 : ℝ)^3491 := by
    have hnat : (1098464219 : ℕ)^4515*10000000000000^3491 ≤ 4607015182741^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098464219 2000000000 4607015182741 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145953639/10000000000 : ℝ), (38640613/125000000 : ℝ), (1098464219/2000000000 : ℝ)] ![(32023136390033/100000000000000 : ℝ), (876268470907/4000000000000 : ℝ), (4607015182741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145953639/10000000000 : ℝ)|^4515 ≤ (32023136390033/100000000000000 : ℝ)^3491
        have hw : |(4145953639/10000000000 : ℝ)|=(4145953639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38640613/125000000 : ℝ)|^4515 ≤ (876268470907/4000000000000 : ℝ)^3491
        have hw : |(38640613/125000000 : ℝ)|=(38640613/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098464219/2000000000 : ℝ)|^4515 ≤ (4607015182741/10000000000000 : ℝ)^3491
        have hw : |(1098464219/2000000000 : ℝ)|=(1098464219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-211570781/1250000000 : ℝ)*x 0 + (1220278341/2500000000 : ℝ)*x 1 + (5887090219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211570781/1250000000 : ℝ)^4515 ≤ (5026067364439/50000000000000 : ℝ)^3491 := by
    have hnat : (211570781 : ℕ)^4515*50000000000000^3491 ≤ 5026067364439^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211570781 1250000000 5026067364439 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220278341/2500000000 : ℝ)^4515 ≤ (9887659249133/25000000000000 : ℝ)^3491 := by
    have hnat : (1220278341 : ℕ)^4515*25000000000000^3491 ≤ 9887659249133^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220278341 2500000000 9887659249133 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5887090219/10000000000 : ℝ)^4515 ≤ (12599307065183/25000000000000 : ℝ)^3491 := by
    have hnat : (5887090219 : ℕ)^4515*25000000000000^3491 ≤ 12599307065183^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5887090219 10000000000 12599307065183 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211570781/1250000000 : ℝ), (1220278341/2500000000 : ℝ), (5887090219/10000000000 : ℝ)] ![(5026067364439/50000000000000 : ℝ), (9887659249133/25000000000000 : ℝ), (12599307065183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211570781/1250000000 : ℝ)|^4515 ≤ (5026067364439/50000000000000 : ℝ)^3491
        have hw : |(-211570781/1250000000 : ℝ)|=(211570781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1220278341/2500000000 : ℝ)|^4515 ≤ (9887659249133/25000000000000 : ℝ)^3491
        have hw : |(1220278341/2500000000 : ℝ)|=(1220278341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5887090219/10000000000 : ℝ)|^4515 ≤ (12599307065183/25000000000000 : ℝ)^3491
        have hw : |(5887090219/10000000000 : ℝ)|=(5887090219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64859249/125000000 : ℝ)*x 0 + (-312741241/2500000000 : ℝ)*x 1 + (1471772499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64859249/125000000 : ℝ)^4515 ≤ (10700947812431/25000000000000 : ℝ)^3491 := by
    have hnat : (64859249 : ℕ)^4515*25000000000000^3491 ≤ 10700947812431^3491*125000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64859249 125000000 10700947812431 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312741241/2500000000 : ℝ)^4515 ≤ (6798982948777/100000000000000 : ℝ)^3491 := by
    have hnat : (312741241 : ℕ)^4515*100000000000000^3491 ≤ 6798982948777^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312741241 2500000000 6798982948777 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1471772499/2500000000 : ℝ)^4515 ≤ (25198612895873/50000000000000 : ℝ)^3491 := by
    have hnat : (1471772499 : ℕ)^4515*50000000000000^3491 ≤ 25198612895873^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471772499 2500000000 25198612895873 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64859249/125000000 : ℝ), (-312741241/2500000000 : ℝ), (1471772499/2500000000 : ℝ)] ![(10700947812431/25000000000000 : ℝ), (6798982948777/100000000000000 : ℝ), (25198612895873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64859249/125000000 : ℝ)|^4515 ≤ (10700947812431/25000000000000 : ℝ)^3491
        have hw : |(64859249/125000000 : ℝ)|=(64859249/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-312741241/2500000000 : ℝ)|^4515 ≤ (6798982948777/100000000000000 : ℝ)^3491
        have hw : |(-312741241/2500000000 : ℝ)|=(312741241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1471772499/2500000000 : ℝ)|^4515 ≤ (25198612895873/50000000000000 : ℝ)^3491
        have hw : |(1471772499/2500000000 : ℝ)|=(1471772499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188740013/10000000000 : ℝ)*x 0 + (735886241/1250000000 : ℝ)*x 1 + (-1250964929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188740013/10000000000 : ℝ)^4515 ≤ (1337618507561/3125000000000 : ℝ)^3491 := by
    have hnat : (5188740013 : ℕ)^4515*3125000000000^3491 ≤ 1337618507561^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188740013 10000000000 1337618507561 3125000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735886241/1250000000 : ℝ)^4515 ≤ (50397225038871/100000000000000 : ℝ)^3491 := by
    have hnat : (735886241 : ℕ)^4515*100000000000000^3491 ≤ 50397225038871^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735886241 1250000000 50397225038871 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250964929/10000000000 : ℝ)^4515 ≤ (3399491351377/50000000000000 : ℝ)^3491 := by
    have hnat : (1250964929 : ℕ)^4515*50000000000000^3491 ≤ 3399491351377^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250964929 10000000000 3399491351377 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188740013/10000000000 : ℝ), (735886241/1250000000 : ℝ), (-1250964929/10000000000 : ℝ)] ![(1337618507561/3125000000000 : ℝ), (50397225038871/100000000000000 : ℝ), (3399491351377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188740013/10000000000 : ℝ)|^4515 ≤ (1337618507561/3125000000000 : ℝ)^3491
        have hw : |(5188740013/10000000000 : ℝ)|=(5188740013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(735886241/1250000000 : ℝ)|^4515 ≤ (50397225038871/100000000000000 : ℝ)^3491
        have hw : |(735886241/1250000000 : ℝ)|=(735886241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1250964929/10000000000 : ℝ)|^4515 ≤ (3399491351377/50000000000000 : ℝ)^3491
        have hw : |(-1250964929/10000000000 : ℝ)|=(1250964929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s0_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153977437/10000000000 : ℝ)*x 0 + (2715520743/5000000000 : ℝ)*x 1 + (3154725123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153977437/10000000000 : ℝ)^4515 ≤ (32103313521333/100000000000000 : ℝ)^3491 := by
    have hnat : (4153977437 : ℕ)^4515*100000000000000^3491 ≤ 32103313521333^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153977437 10000000000 32103313521333 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715520743/5000000000 : ℝ)^4515 ≤ (4540644774421/10000000000000 : ℝ)^3491 := by
    have hnat : (2715520743 : ℕ)^4515*10000000000000^3491 ≤ 4540644774421^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715520743 5000000000 4540644774421 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154725123/10000000000 : ℝ)^4515 ≤ (4498047746191/20000000000000 : ℝ)^3491 := by
    have hnat : (3154725123 : ℕ)^4515*20000000000000^3491 ≤ 4498047746191^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154725123 10000000000 4498047746191 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153977437/10000000000 : ℝ), (2715520743/5000000000 : ℝ), (3154725123/10000000000 : ℝ)] ![(32103313521333/100000000000000 : ℝ), (4540644774421/10000000000000 : ℝ), (4498047746191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153977437/10000000000 : ℝ)|^4515 ≤ (32103313521333/100000000000000 : ℝ)^3491
        have hw : |(4153977437/10000000000 : ℝ)|=(4153977437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715520743/5000000000 : ℝ)|^4515 ≤ (4540644774421/10000000000000 : ℝ)^3491
        have hw : |(2715520743/5000000000 : ℝ)|=(2715520743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154725123/10000000000 : ℝ)|^4515 ≤ (4498047746191/20000000000000 : ℝ)^3491
        have hw : |(3154725123/10000000000 : ℝ)|=(3154725123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2789/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25523/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4513/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4513 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4513*1^1024 ≤ 0^1024*1^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4513/1024 : ℝ) ≤ (881369926716748407/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4513 ≤ (881369926716748407/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4513*50000000000000000000^1024 ≤ 881369926716748407^1024*5^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 881369926716748407 50000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (881369926716748407/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4513 := by
      have hnat : (1 : ℕ)^1024*1^4513 ≤ 1^4513*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50881369926716748407/50000000000000000000 : ℝ) ≤ (5019863426291559/5000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (50881369926716748407/50000000000000000000 : ℝ)^1024 ≤ (5019863426291559/5000000000000000 : ℝ)^4513 := by
      have hnat : (50881369926716748407 : ℕ)^1024*5000000000000000^4513 ≤ 5019863426291559^4513*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50881369926716748407 50000000000000000000 5019863426291559 5000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019863426291559/5000000000000000 : ℝ)) (X := (50881369926716748407/50000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25881369926716748407/25000000000000000000 : ℝ) ≤ (2519863426291559/2500000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (25881369926716748407/25000000000000000000 : ℝ)^1024 ≤ (2519863426291559/2500000000000000 : ℝ)^4513 := by
      have hnat : (25881369926716748407 : ℕ)^1024*2500000000000000^4513 ≤ 2519863426291559^4513*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25881369926716748407 25000000000000000000 2519863426291559 2500000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2519863426291559/2500000000000000 : ℝ)) (X := (25881369926716748407/25000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(19863426291559/2000000000000000 : ℝ)*(0 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19863426291559/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(881369926716748407/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(19863426291559/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (1 : ℝ)+(19863426291559/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5019863426291559/5000000000000000 : ℝ) by norm_num, show 1+(881369926716748407/50000000000000000000 : ℝ)+(0 : ℝ)=(50881369926716748407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(881369926716748407/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(19863426291559/2000000000000000 : ℝ)*(2/5 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19863426291559/2000000000000000 : ℝ)*(2/5 : ℝ)=(2519863426291559/2500000000000000 : ℝ) by norm_num, show 1+2*(881369926716748407/50000000000000000000 : ℝ)=(25881369926716748407/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(19863426291559/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19863426291559/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(19863426291559/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19863426291559/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(19863426291559/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19863426291559/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1649434/9765625 : ℝ)*X 0 0+(5915141993/10000000000 : ℝ)*X 0 1+(1213507981/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((21914533/40000000 : ℝ)*X 1 0+(-1784393/7812500 : ℝ)*X 1 1+(606753983/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5478633297/10000000000 : ℝ)*X 2 0+(2427015939/5000000000 : ℝ)*X 2 1+(-1142011481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4145953639/10000000000 : ℝ)*X 0 0+(38640613/125000000 : ℝ)*X 0 1+(1098464219/2000000000 : ℝ)*X 0 2+(4145953639/10000000000 : ℝ)*X 1 0+(38640613/125000000 : ℝ)*X 1 1+(1098464219/2000000000 : ℝ)*X 1 2+(4145953639/10000000000 : ℝ)*X 2 0+(38640613/125000000 : ℝ)*X 2 1+(1098464219/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-211570781/1250000000 : ℝ)*X 0 0+(1220278341/2500000000 : ℝ)*X 0 1+(5887090219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((64859249/125000000 : ℝ)*X 1 0+(-312741241/2500000000 : ℝ)*X 1 1+(1471772499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5188740013/10000000000 : ℝ)*X 2 0+(735886241/1250000000 : ℝ)*X 2 1+(-1250964929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4153977437/10000000000 : ℝ)*X 0 0+(2715520743/5000000000 : ℝ)*X 0 1+(3154725123/10000000000 : ℝ)*X 0 2+(4153977437/10000000000 : ℝ)*X 1 0+(2715520743/5000000000 : ℝ)*X 1 1+(3154725123/10000000000 : ℝ)*X 1 2+(4153977437/10000000000 : ℝ)*X 2 0+(2715520743/5000000000 : ℝ)*X 2 1+(3154725123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2821454387838499401/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7911/40000000000 : ℝ)*(base1) + (665483453/100000000000000 : ℝ)*(base19) + (67356821/10000000000000 : ℝ)*(base23) + (36944279/50000000000000 : ℝ)*(upper3) + (49175253/50000000000000 : ℝ)*(upper5) + (135889671274801/20000000000000 : ℝ)*(major0) + (135889671274801/20000000000000 : ℝ)*(major1) + (135889671274801/20000000000000 : ℝ)*(major2) + (94241144826831/10000000000000 : ℝ)*(sp0) + (117801651883987/12500000000000 : ℝ)*(sp1) + (942413206987139/100000000000000 : ℝ)*(sp2) + (416481678509657/100000000000000 : ℝ)*(sp3) + (1226032269/50000000000000 : ℝ)*(sp4) + (51992851/5000000000000 : ℝ)*(sp7) + (416482738144177/100000000000000 : ℝ)*(f.failure) + (942413880555349/100000000000000 : ℝ)*(f.sum) + (26994947875241/20000000000000000000000000000 : ℝ)*base66 + (296205889224759/40000000000000000000000000000 : ℝ)*base67 + (76063030224759/40000000000000000000000000000 : ℝ)*base69 + (3524226815241/40000000000000000000000000000 : ℝ)*base72 + (87198892504759/20000000000000000000000000000 : ℝ)*base73 + (282369445055241/40000000000000000000000000000 : ℝ)*base76 + (91925238135241/40000000000000000000000000000 : ℝ)*base78 + (168097685975241/40000000000000000000000000000 : ℝ)*base80 + (25804592564759/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2049637/500000000000000000000 : ℝ)*base89 + (2049637/500000000000000000000 : ℝ)*base91 + (2049637/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (301381428170177440884717/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (595803769/50000000000000 : ℝ)*(base19) + (305645299/25000000000000 : ℝ)*(base23) + (104373369/100000000000000 : ℝ)*(base32) + (173394677/100000000000000 : ℝ)*(upper3) + (114525479/100000000000000 : ℝ)*(upper5) + (716682265635479/100000000000000 : ℝ)*(major0) + (716682265635479/100000000000000 : ℝ)*(major1) + (716682265635479/100000000000000 : ℝ)*(major2) + (2851100737/100000000000000 : ℝ)*(sp1) + (3086591133/100000000000000 : ℝ)*(sp2) + (497029126374407/50000000000000 : ℝ)*(sp4) + (994054210040539/100000000000000 : ℝ)*(sp5) + (198810788715297/20000000000000 : ℝ)*(sp6) + (54913246653477/12500000000000 : ℝ)*(sp7) + (87861215520237/20000000000000 : ℝ)*(f.failure) + (497029126374407/50000000000000 : ℝ)*(f.sum) + (52141696621761/100000000000000000000000000000 : ℝ)*base65 + (1489632494221761/200000000000000000000000000000 : ℝ)*base67 + (815396858178239/200000000000000000000000000000 : ℝ)*base70 + (171244475778239/200000000000000000000000000000 : ℝ)*base72 + (840025618621761/100000000000000000000000000000 : ℝ)*base73 + (1217393127378239/200000000000000000000000000000 : ℝ)*base76 + (405010010978239/200000000000000000000000000000 : ℝ)*base78 + (824686382621761/200000000000000000000000000000 : ℝ)*base79 + (155184382921761/100000000000000000000000000000 : ℝ)*base81 + (675503/100000000000000000000 : ℝ)*base90 + (675503/100000000000000000000 : ℝ)*base92 + (675503/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1509_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25523/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1509_s1_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1843537373/10000000000 : ℝ)*x 0 + (5572512267/10000000000 : ℝ)*x 1 + (5097363987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1843537373/10000000000 : ℝ)^4515 ≤ (1122661406527/10000000000000 : ℝ)^3491 := by
    have hnat : (1843537373 : ℕ)^4515*10000000000000^3491 ≤ 1122661406527^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843537373 10000000000 1122661406527 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5572512267/10000000000 : ℝ)^4515 ≤ (46941966166447/100000000000000 : ℝ)^3491 := by
    have hnat : (5572512267 : ℕ)^4515*100000000000000^3491 ≤ 46941966166447^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572512267 10000000000 46941966166447 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097363987/10000000000 : ℝ)^4515 ≤ (41831419753907/100000000000000 : ℝ)^3491 := by
    have hnat : (5097363987 : ℕ)^4515*100000000000000^3491 ≤ 41831419753907^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097363987 10000000000 41831419753907 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1843537373/10000000000 : ℝ), (5572512267/10000000000 : ℝ), (5097363987/10000000000 : ℝ)] ![(1122661406527/10000000000000 : ℝ), (46941966166447/100000000000000 : ℝ), (41831419753907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1843537373/10000000000 : ℝ)|^4515 ≤ (1122661406527/10000000000000 : ℝ)^3491
        have hw : |(-1843537373/10000000000 : ℝ)|=(1843537373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5572512267/10000000000 : ℝ)|^4515 ≤ (46941966166447/100000000000000 : ℝ)^3491
        have hw : |(5572512267/10000000000 : ℝ)|=(5572512267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097363987/10000000000 : ℝ)|^4515 ≤ (41831419753907/100000000000000 : ℝ)^3491
        have hw : |(5097363987/10000000000 : ℝ)|=(5097363987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693584861/5000000000 : ℝ)*x 0 + (-418765551/2000000000 : ℝ)*x 1 + (5097362981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693584861/5000000000 : ℝ)^4515 ≤ (44932629699419/100000000000000 : ℝ)^3491 := by
    have hnat : (2693584861 : ℕ)^4515*100000000000000^3491 ≤ 44932629699419^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693584861 5000000000 44932629699419 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (418765551/2000000000 : ℝ)^4515 ≤ (13235961203107/100000000000000 : ℝ)^3491 := by
    have hnat : (418765551 : ℕ)^4515*100000000000000^3491 ≤ 13235961203107^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418765551 2000000000 13235961203107 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097362981/10000000000 : ℝ)^4515 ≤ (41831409076573/100000000000000 : ℝ)^3491 := by
    have hnat : (5097362981 : ℕ)^4515*100000000000000^3491 ≤ 41831409076573^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097362981 10000000000 41831409076573 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693584861/5000000000 : ℝ), (-418765551/2000000000 : ℝ), (5097362981/10000000000 : ℝ)] ![(44932629699419/100000000000000 : ℝ), (13235961203107/100000000000000 : ℝ), (41831409076573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693584861/5000000000 : ℝ)|^4515 ≤ (44932629699419/100000000000000 : ℝ)^3491
        have hw : |(2693584861/5000000000 : ℝ)|=(2693584861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-418765551/2000000000 : ℝ)|^4515 ≤ (13235961203107/100000000000000 : ℝ)^3491
        have hw : |(-418765551/2000000000 : ℝ)|=(418765551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097362981/10000000000 : ℝ)|^4515 ≤ (41831409076573/100000000000000 : ℝ)^3491
        have hw : |(5097362981/10000000000 : ℝ)|=(5097362981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387169083/10000000000 : ℝ)*x 0 + (2548681827/5000000000 : ℝ)*x 1 + (-83753109/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387169083/10000000000 : ℝ)^4515 ≤ (5616577850799/12500000000000 : ℝ)^3491 := by
    have hnat : (5387169083 : ℕ)^4515*12500000000000^3491 ≤ 5616577850799^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387169083 10000000000 5616577850799 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548681827/5000000000 : ℝ)^4515 ≤ (41831416219561/100000000000000 : ℝ)^3491 := by
    have hnat : (2548681827 : ℕ)^4515*100000000000000^3491 ≤ 41831416219561^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548681827 5000000000 41831416219561 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83753109/400000000 : ℝ)^4515 ≤ (6617980478919/50000000000000 : ℝ)^3491 := by
    have hnat : (83753109 : ℕ)^4515*50000000000000^3491 ≤ 6617980478919^3491*400000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83753109 400000000 6617980478919 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387169083/10000000000 : ℝ), (2548681827/5000000000 : ℝ), (-83753109/400000000 : ℝ)] ![(5616577850799/12500000000000 : ℝ), (41831416219561/100000000000000 : ℝ), (6617980478919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387169083/10000000000 : ℝ)|^4515 ≤ (5616577850799/12500000000000 : ℝ)^3491
        have hw : |(5387169083/10000000000 : ℝ)|=(5387169083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548681827/5000000000 : ℝ)|^4515 ≤ (41831416219561/100000000000000 : ℝ)^3491
        have hw : |(2548681827/5000000000 : ℝ)|=(2548681827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83753109/400000000 : ℝ)|^4515 ≤ (6617980478919/50000000000000 : ℝ)^3491
        have hw : |(-83753109/400000000 : ℝ)|=(83753109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125353289/5000000000 : ℝ)*x 0 + (1870949193/5000000000 : ℝ)*x 1 + (1204265453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125353289/5000000000 : ℝ)^4515 ≤ (33073429373529/100000000000000 : ℝ)^3491 := by
    have hnat : (2125353289 : ℕ)^4515*100000000000000^3491 ≤ 33073429373529^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125353289 5000000000 33073429373529 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870949193/5000000000 : ℝ)^4515 ≤ (5609173799101/20000000000000 : ℝ)^3491 := by
    have hnat : (1870949193 : ℕ)^4515*20000000000000^3491 ≤ 5609173799101^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870949193 5000000000 5609173799101 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204265453/2500000000 : ℝ)^4515 ≤ (38880701609787/100000000000000 : ℝ)^3491 := by
    have hnat : (1204265453 : ℕ)^4515*100000000000000^3491 ≤ 38880701609787^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204265453 2500000000 38880701609787 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125353289/5000000000 : ℝ), (1870949193/5000000000 : ℝ), (1204265453/2500000000 : ℝ)] ![(33073429373529/100000000000000 : ℝ), (5609173799101/20000000000000 : ℝ), (38880701609787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125353289/5000000000 : ℝ)|^4515 ≤ (33073429373529/100000000000000 : ℝ)^3491
        have hw : |(2125353289/5000000000 : ℝ)|=(2125353289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870949193/5000000000 : ℝ)|^4515 ≤ (5609173799101/20000000000000 : ℝ)^3491
        have hw : |(1870949193/5000000000 : ℝ)|=(1870949193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204265453/2500000000 : ℝ)|^4515 ≤ (38880701609787/100000000000000 : ℝ)^3491
        have hw : |(1204265453/2500000000 : ℝ)|=(1204265453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-460961267/2500000000 : ℝ)*x 0 + (5102699923/10000000000 : ℝ)*x 1 + (556709/1000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460961267/2500000000 : ℝ)^4515 ≤ (11229037525083/100000000000000 : ℝ)^3491 := by
    have hnat : (460961267 : ℕ)^4515*100000000000000^3491 ≤ 11229037525083^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460961267 2500000000 11229037525083 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5102699923/10000000000 : ℝ)^4515 ≤ (10472015554259/25000000000000 : ℝ)^3491 := by
    have hnat : (5102699923 : ℕ)^4515*25000000000000^3491 ≤ 10472015554259^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102699923 10000000000 10472015554259 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556709/1000000 : ℝ)^4515 ≤ (9376580047147/20000000000000 : ℝ)^3491 := by
    have hnat : (556709 : ℕ)^4515*20000000000000^3491 ≤ 9376580047147^3491*1000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556709 1000000 9376580047147 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460961267/2500000000 : ℝ), (5102699923/10000000000 : ℝ), (556709/1000000 : ℝ)] ![(11229037525083/100000000000000 : ℝ), (10472015554259/25000000000000 : ℝ), (9376580047147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460961267/2500000000 : ℝ)|^4515 ≤ (11229037525083/100000000000000 : ℝ)^3491
        have hw : |(-460961267/2500000000 : ℝ)|=(460961267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5102699923/10000000000 : ℝ)|^4515 ≤ (10472015554259/25000000000000 : ℝ)^3491
        have hw : |(5102699923/10000000000 : ℝ)|=(5102699923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(556709/1000000 : ℝ)|^4515 ≤ (9376580047147/20000000000000 : ℝ)^3491
        have hw : |(556709/1000000 : ℝ)|=(556709/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65775787/125000000 : ℝ)*x 0 + (-324820177/2000000000 : ℝ)*x 1 + (695886271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65775787/125000000 : ℝ)^4515 ≤ (4358769886529/10000000000000 : ℝ)^3491 := by
    have hnat : (65775787 : ℕ)^4515*10000000000000^3491 ≤ 4358769886529^3491*125000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65775787 125000000 4358769886529 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324820177/2000000000 : ℝ)^4515 ≤ (4764699525763/50000000000000 : ℝ)^3491 := by
    have hnat : (324820177 : ℕ)^4515*50000000000000^3491 ≤ 4764699525763^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324820177 2000000000 4764699525763 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695886271/1250000000 : ℝ)^4515 ≤ (23441451032767/50000000000000 : ℝ)^3491 := by
    have hnat : (695886271 : ℕ)^4515*50000000000000^3491 ≤ 23441451032767^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695886271 1250000000 23441451032767 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65775787/125000000 : ℝ), (-324820177/2000000000 : ℝ), (695886271/1250000000 : ℝ)] ![(4358769886529/10000000000000 : ℝ), (4764699525763/50000000000000 : ℝ), (23441451032767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65775787/125000000 : ℝ)|^4515 ≤ (4358769886529/10000000000000 : ℝ)^3491
        have hw : |(65775787/125000000 : ℝ)|=(65775787/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-324820177/2000000000 : ℝ)|^4515 ≤ (4764699525763/50000000000000 : ℝ)^3491
        have hw : |(-324820177/2000000000 : ℝ)|=(324820177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(695886271/1250000000 : ℝ)|^4515 ≤ (23441451032767/50000000000000 : ℝ)^3491
        have hw : |(695886271/1250000000 : ℝ)|=(695886271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052412553/2000000000 : ℝ)*x 0 + (1391772561/2500000000 : ℝ)*x 1 + (-1624101051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052412553/2000000000 : ℝ)^4515 ≤ (5448462097029/12500000000000 : ℝ)^3491 := by
    have hnat : (1052412553 : ℕ)^4515*12500000000000^3491 ≤ 5448462097029^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052412553 2000000000 5448462097029 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391772561/2500000000 : ℝ)^4515 ≤ (46882902893301/100000000000000 : ℝ)^3491 := by
    have hnat : (1391772561 : ℕ)^4515*100000000000000^3491 ≤ 46882902893301^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391772561 2500000000 46882902893301 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1624101051/10000000000 : ℝ)^4515 ≤ (952940031123/10000000000000 : ℝ)^3491 := by
    have hnat : (1624101051 : ℕ)^4515*10000000000000^3491 ≤ 952940031123^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624101051 10000000000 952940031123 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052412553/2000000000 : ℝ), (1391772561/2500000000 : ℝ), (-1624101051/10000000000 : ℝ)] ![(5448462097029/12500000000000 : ℝ), (46882902893301/100000000000000 : ℝ), (952940031123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052412553/2000000000 : ℝ)|^4515 ≤ (5448462097029/12500000000000 : ℝ)^3491
        have hw : |(1052412553/2000000000 : ℝ)|=(1052412553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1391772561/2500000000 : ℝ)|^4515 ≤ (46882902893301/100000000000000 : ℝ)^3491
        have hw : |(1391772561/2500000000 : ℝ)|=(1391772561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1624101051/10000000000 : ℝ)|^4515 ≤ (952940031123/10000000000000 : ℝ)^3491
        have hw : |(-1624101051/10000000000 : ℝ)|=(1624101051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s1_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850280563/2000000000 : ℝ)*x 0 + (600623431/1250000000 : ℝ)*x 1 + (1877083897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850280563/2000000000 : ℝ)^4515 ≤ (4135054468891/12500000000000 : ℝ)^3491 := by
    have hnat : (850280563 : ℕ)^4515*12500000000000^3491 ≤ 4135054468891^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850280563 2000000000 4135054468891 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600623431/1250000000 : ℝ)^4515 ≤ (38754703432119/100000000000000 : ℝ)^3491 := by
    have hnat : (600623431 : ℕ)^4515*100000000000000^3491 ≤ 38754703432119^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600623431 1250000000 38754703432119 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877083897/5000000000 : ℝ)^4515 ≤ (7041215201001/25000000000000 : ℝ)^3491 := by
    have hnat : (1877083897 : ℕ)^4515*25000000000000^3491 ≤ 7041215201001^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877083897 5000000000 7041215201001 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850280563/2000000000 : ℝ), (600623431/1250000000 : ℝ), (1877083897/5000000000 : ℝ)] ![(4135054468891/12500000000000 : ℝ), (38754703432119/100000000000000 : ℝ), (7041215201001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850280563/2000000000 : ℝ)|^4515 ≤ (4135054468891/12500000000000 : ℝ)^3491
        have hw : |(850280563/2000000000 : ℝ)|=(850280563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600623431/1250000000 : ℝ)|^4515 ≤ (38754703432119/100000000000000 : ℝ)^3491
        have hw : |(600623431/1250000000 : ℝ)|=(600623431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1877083897/5000000000 : ℝ)|^4515 ≤ (7041215201001/25000000000000 : ℝ)^3491
        have hw : |(1877083897/5000000000 : ℝ)|=(1877083897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2079/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3673/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2789/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2789/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2789/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2789/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2789/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2789/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2789/100000 : ℝ) ^ (4513/1024 : ℝ) ≤ (7042217004469/50000000000000000000 : ℝ) := by
    have hpowers : (2789/100000 : ℝ)^4513 ≤ (7042217004469/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2789 : ℕ)^4513*50000000000000000000^1024 ≤ 7042217004469^1024*100000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789 100000 7042217004469 50000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2789/100000 : ℝ)) (X := (7042217004469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25523/100000 : ℝ) ^ (4513/1024 : ℝ) ≤ (243340124044519369/100000000000000000000 : ℝ) := by
    have hpowers : (25523/100000 : ℝ)^4513 ≤ (243340124044519369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25523 : ℕ)^4513*100000000000000000000^1024 ≤ 243340124044519369^1024*100000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25523 100000 243340124044519369 100000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25523/100000 : ℝ)) (X := (243340124044519369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000007042217004469/25000000000000000000 : ℝ) ≤ (10000000639151733/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (25000007042217004469/25000000000000000000 : ℝ)^1024 ≤ (10000000639151733/10000000000000000 : ℝ)^4513 := by
      have hnat : (25000007042217004469 : ℕ)^1024*10000000000000000^4513 ≤ 10000000639151733^4513*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000007042217004469 25000000000000000000 10000000639151733 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000639151733/10000000000000000 : ℝ)) (X := (25000007042217004469/25000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100243354208478528307/100000000000000000000 : ℝ) ≤ (10005516521874473/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (100243354208478528307/100000000000000000000 : ℝ)^1024 ≤ (10005516521874473/10000000000000000 : ℝ)^4513 := by
      have hnat : (100243354208478528307 : ℕ)^1024*10000000000000000^4513 ≤ 10005516521874473^4513*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100243354208478528307 100000000000000000000 10005516521874473 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005516521874473/10000000000000000 : ℝ)) (X := (100243354208478528307/100000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50243340124044519369/50000000000000000000 : ℝ) ≤ (10011032404597213/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (50243340124044519369/50000000000000000000 : ℝ)^1024 ≤ (10011032404597213/10000000000000000 : ℝ)^4513 := by
      have hnat : (50243340124044519369 : ℕ)^1024*10000000000000000^4513 ≤ 10011032404597213^4513*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50243340124044519369 50000000000000000000 10011032404597213 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011032404597213/10000000000000000 : ℝ)) (X := (50243340124044519369/50000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7042217004469/50000000000000000000 : ℝ) ≤ ((113654623468324027151/113670000000000000000 : ℝ)+2*(275794136137/113670000000000 : ℝ)*(2789/100000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (113654623468324027151/113670000000000000000 : ℝ)+2*(275794136137/113670000000000 : ℝ)*(2789/100000 : ℝ)=(10000000639151733/10000000000000000 : ℝ) by norm_num, show 1+2*(7042217004469/50000000000000000000 : ℝ)=(25000007042217004469/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(243340124044519369/100000000000000000000 : ℝ)+(7042217004469/50000000000000000000 : ℝ) ≤ ((113654623468324027151/113670000000000000000 : ℝ)+(275794136137/113670000000000 : ℝ)*((25523/100000 : ℝ)+(2789/100000 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (113654623468324027151/113670000000000000000 : ℝ)+(275794136137/113670000000000 : ℝ)*((25523/100000 : ℝ)+(2789/100000 : ℝ))=(10005516521874473/10000000000000000 : ℝ) by norm_num, show 1+(243340124044519369/100000000000000000000 : ℝ)+(7042217004469/50000000000000000000 : ℝ)=(100243354208478528307/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(243340124044519369/100000000000000000000 : ℝ) ≤ ((113654623468324027151/113670000000000000000 : ℝ)+2*(275794136137/113670000000000 : ℝ)*(25523/100000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (113654623468324027151/113670000000000000000 : ℝ)+2*(275794136137/113670000000000 : ℝ)*(25523/100000 : ℝ)=(10011032404597213/10000000000000000 : ℝ) by norm_num, show 1+2*(243340124044519369/100000000000000000000 : ℝ)=(50243340124044519369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (113654623468324027151/113670000000000000000 : ℝ)*(X 1 0+X 2 0)+(275794136137/113670000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (2789/100000 : ℝ)) (hi := (25523/100000 : ℝ)) (c := (113654623468324027151/113670000000000000000 : ℝ)) (alpha := (275794136137/113670000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (113654623468324027151/113670000000000000000 : ℝ)*(X 0 1+X 2 1)+(275794136137/113670000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (2789/100000 : ℝ)) (hi := (25523/100000 : ℝ)) (c := (113654623468324027151/113670000000000000000 : ℝ)) (alpha := (275794136137/113670000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (113654623468324027151/113670000000000000000 : ℝ)*(X 0 2+X 1 2)+(275794136137/113670000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (2789/100000 : ℝ)) (hi := (25523/100000 : ℝ)) (c := (113654623468324027151/113670000000000000000 : ℝ)) (alpha := (275794136137/113670000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1843537373/10000000000 : ℝ)*X 0 0+(5572512267/10000000000 : ℝ)*X 0 1+(5097363987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2693584861/5000000000 : ℝ)*X 1 0+(-418765551/2000000000 : ℝ)*X 1 1+(5097362981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5387169083/10000000000 : ℝ)*X 2 0+(2548681827/5000000000 : ℝ)*X 2 1+(-83753109/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125353289/5000000000 : ℝ)*X 0 0+(1870949193/5000000000 : ℝ)*X 0 1+(1204265453/2500000000 : ℝ)*X 0 2+(2125353289/5000000000 : ℝ)*X 1 0+(1870949193/5000000000 : ℝ)*X 1 1+(1204265453/2500000000 : ℝ)*X 1 2+(2125353289/5000000000 : ℝ)*X 2 0+(1870949193/5000000000 : ℝ)*X 2 1+(1204265453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-460961267/2500000000 : ℝ)*X 0 0+(5102699923/10000000000 : ℝ)*X 0 1+(556709/1000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((65775787/125000000 : ℝ)*X 1 0+(-324820177/2000000000 : ℝ)*X 1 1+(695886271/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052412553/2000000000 : ℝ)*X 2 0+(1391772561/2500000000 : ℝ)*X 2 1+(-1624101051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((850280563/2000000000 : ℝ)*X 0 0+(600623431/1250000000 : ℝ)*X 0 1+(1877083897/5000000000 : ℝ)*X 0 2+(850280563/2000000000 : ℝ)*X 1 0+(600623431/1250000000 : ℝ)*X 1 1+(1877083897/5000000000 : ℝ)*X 1 2+(850280563/2000000000 : ℝ)*X 2 0+(600623431/1250000000 : ℝ)*X 2 1+(1877083897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298439698760361020626970647/78937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23754389/50000000000000 : ℝ)*(base1) + (422807089/50000000000000 : ℝ)*(base19) + (297987669/50000000000000 : ℝ)*(base23) + (62398051/100000000000000 : ℝ)*(upper3) + (6635423/25000000000000 : ℝ)*(upper5) + (189669217162097/12500000000000 : ℝ)*(major0) + (189669217162097/12500000000000 : ℝ)*(major1) + (189669217162097/12500000000000 : ℝ)*(major2) + (263076218076633/12500000000000 : ℝ)*(sp0) + (2104611326016641/100000000000000 : ℝ)*(sp1) + (2104611575655481/100000000000000 : ℝ)*(sp2) + (232523292599987/25000000000000 : ℝ)*(sp3) + (2474526533/100000000000000 : ℝ)*(sp4) + (15672243/800000000000 : ℝ)*(sp7) + (930095176939101/100000000000000 : ℝ)*(f.failure) + (1052306085815409/50000000000000 : ℝ)*(f.sum) + (28951765228373/11367000000000000000000000000 : ℝ)*base65 + (3678099524447676451/473625000000000000000000000000000 : ℝ)*base68 + (1166889910734051451/473625000000000000000000000000000 : ℝ)*base70 + (552258543628176451/473625000000000000000000000000000 : ℝ)*base72 + (10548449913533/11367000000000000000000000000 : ℝ)*base73 + (1991504498761176451/473625000000000000000000000000000 : ℝ)*base76 + (2181220744686801451/473625000000000000000000000000000 : ℝ)*base78 + (1009826297298051451/473625000000000000000000000000000 : ℝ)*base80 + (74197149944657/11367000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5014081/500000000000000000000 : ℝ)*base89 + (5014081/500000000000000000000 : ℝ)*base91 + (5014081/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7415457006904478505684535439/1894500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194392711/25000000000000 : ℝ)*(base19) + (152938243/20000000000000 : ℝ)*(base23) + (6223909/5000000000000 : ℝ)*(upper3) + (28619871/100000000000000 : ℝ)*(lower4) + (20430387/100000000000000 : ℝ)*(upper5) + (1552499394230911/100000000000000 : ℝ)*(major0) + (1552499394230911/100000000000000 : ℝ)*(major1) + (1552499394230911/100000000000000 : ℝ)*(major2) + (1091648183/20000000000000 : ℝ)*(sp1) + (5985275741/100000000000000 : ℝ)*(sp2) + (2153360181552741/100000000000000 : ℝ)*(sp4) + (1076676972870491/50000000000000 : ℝ)*(sp5) + (1076676715792893/50000000000000 : ℝ)*(sp6) + (951638476435651/100000000000000 : ℝ)*(sp7) + (951638476435651/100000000000000 : ℝ)*(f.failure) + (2153360181552741/100000000000000 : ℝ)*(f.sum) + (12606969301531/2273400000000000000000000000 : ℝ)*base65 + (28361275726612488187/3789000000000000000000000000000000 : ℝ)*base67 + (174692295454511813/3789000000000000000000000000000000 : ℝ)*base70 + (43169777730976488187/3789000000000000000000000000000000 : ℝ)*base71 + (29716833021263/11367000000000000000000000000 : ℝ)*base73 + (3713797027246488187/3789000000000000000000000000000000 : ℝ)*base75 + (2426011133449488187/3789000000000000000000000000000000 : ℝ)*base77 + (26616547647382511813/3789000000000000000000000000000000 : ℝ)*base80 + (19144214546347/11367000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2070369/500000000000000000000 : ℝ)*base90 + (2070369/500000000000000000000 : ℝ)*base92 + (2070369/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1509_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2079/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1509_s2_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467100881/2500000000 : ℝ)*x 0 + (2729441173/5000000000 : ℝ)*x 1 + (1298723003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467100881/2500000000 : ℝ)^4515 ≤ (2284569128657/20000000000000 : ℝ)^3491 := by
    have hnat : (467100881 : ℕ)^4515*20000000000000^3491 ≤ 2284569128657^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467100881 2500000000 2284569128657 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729441173/5000000000 : ℝ)^4515 ≤ (11426928581369/25000000000000 : ℝ)^3491 := by
    have hnat : (2729441173 : ℕ)^4515*25000000000000^3491 ≤ 11426928581369^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729441173 5000000000 11426928581369 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298723003/2500000000 : ℝ)^4515 ≤ (21434720006939/50000000000000 : ℝ)^3491 := by
    have hnat : (1298723003 : ℕ)^4515*50000000000000^3491 ≤ 21434720006939^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298723003 2500000000 21434720006939 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467100881/2500000000 : ℝ), (2729441173/5000000000 : ℝ), (1298723003/2500000000 : ℝ)] ![(2284569128657/20000000000000 : ℝ), (11426928581369/25000000000000 : ℝ), (21434720006939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467100881/2500000000 : ℝ)|^4515 ≤ (2284569128657/20000000000000 : ℝ)^3491
        have hw : |(-467100881/2500000000 : ℝ)|=(467100881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729441173/5000000000 : ℝ)|^4515 ≤ (11426928581369/25000000000000 : ℝ)^3491
        have hw : |(2729441173/5000000000 : ℝ)|=(2729441173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298723003/2500000000 : ℝ)|^4515 ≤ (21434720006939/50000000000000 : ℝ)^3491
        have hw : |(1298723003/2500000000 : ℝ)|=(1298723003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679161669/5000000000 : ℝ)*x 0 + (-10021623/50000000 : ℝ)*x 1 + (649361601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679161669/5000000000 : ℝ)^4515 ≤ (11155425603389/25000000000000 : ℝ)^3491 := by
    have hnat : (2679161669 : ℕ)^4515*25000000000000^3491 ≤ 11155425603389^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679161669 5000000000 11155425603389 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10021623/50000000 : ℝ)^4515 ≤ (12508849063231/100000000000000 : ℝ)^3491 := by
    have hnat : (10021623 : ℕ)^4515*100000000000000^3491 ≤ 12508849063231^3491*50000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10021623 50000000 12508849063231 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649361601/1250000000 : ℝ)^4515 ≤ (42869448509443/100000000000000 : ℝ)^3491 := by
    have hnat : (649361601 : ℕ)^4515*100000000000000^3491 ≤ 42869448509443^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649361601 1250000000 42869448509443 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679161669/5000000000 : ℝ), (-10021623/50000000 : ℝ), (649361601/1250000000 : ℝ)] ![(11155425603389/25000000000000 : ℝ), (12508849063231/100000000000000 : ℝ), (42869448509443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679161669/5000000000 : ℝ)|^4515 ≤ (11155425603389/25000000000000 : ℝ)^3491
        have hw : |(2679161669/5000000000 : ℝ)|=(2679161669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10021623/50000000 : ℝ)|^4515 ≤ (12508849063231/100000000000000 : ℝ)^3491
        have hw : |(-10021623/50000000 : ℝ)|=(10021623/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649361601/1250000000 : ℝ)|^4515 ≤ (42869448509443/100000000000000 : ℝ)^3491
        have hw : |(649361601/1250000000 : ℝ)|=(649361601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679162117/5000000000 : ℝ)*x 0 + (5194892217/10000000000 : ℝ)*x 1 + (-1002162093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679162117/5000000000 : ℝ)^4515 ≤ (8924342412737/20000000000000 : ℝ)^3491 := by
    have hnat : (2679162117 : ℕ)^4515*20000000000000^3491 ≤ 8924342412737^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679162117 5000000000 8924342412737 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194892217/10000000000 : ℝ)^4515 ≤ (21434721100903/50000000000000 : ℝ)^3491 := by
    have hnat : (5194892217 : ℕ)^4515*50000000000000^3491 ≤ 21434721100903^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194892217 10000000000 21434721100903 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002162093/5000000000 : ℝ)^4515 ≤ (1563605715201/12500000000000 : ℝ)^3491 := by
    have hnat : (1002162093 : ℕ)^4515*12500000000000^3491 ≤ 1563605715201^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002162093 5000000000 1563605715201 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679162117/5000000000 : ℝ), (5194892217/10000000000 : ℝ), (-1002162093/5000000000 : ℝ)] ![(8924342412737/20000000000000 : ℝ), (21434721100903/50000000000000 : ℝ), (1563605715201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679162117/5000000000 : ℝ)|^4515 ≤ (8924342412737/20000000000000 : ℝ)^3491
        have hw : |(2679162117/5000000000 : ℝ)|=(2679162117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194892217/10000000000 : ℝ)|^4515 ≤ (21434721100903/50000000000000 : ℝ)^3491
        have hw : |(5194892217/10000000000 : ℝ)|=(5194892217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002162093/5000000000 : ℝ)|^4515 ≤ (1563605715201/12500000000000 : ℝ)^3491
        have hw : |(-1002162093/5000000000 : ℝ)|=(1002162093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268546777/10000000000 : ℝ)*x 0 + (994688509/2500000000 : ℝ)*x 1 + (4576110277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268546777/10000000000 : ℝ)^4515 ≤ (33253065087111/100000000000000 : ℝ)^3491 := by
    have hnat : (4268546777 : ℕ)^4515*100000000000000^3491 ≤ 33253065087111^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268546777 10000000000 33253065087111 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994688509/2500000000 : ℝ)^4515 ≤ (30362856703963/100000000000000 : ℝ)^3491 := by
    have hnat : (994688509 : ℕ)^4515*100000000000000^3491 ≤ 30362856703963^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994688509 2500000000 30362856703963 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4576110277/10000000000 : ℝ)^4515 ≤ (36384078195941/100000000000000 : ℝ)^3491 := by
    have hnat : (4576110277 : ℕ)^4515*100000000000000^3491 ≤ 36384078195941^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576110277 10000000000 36384078195941 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268546777/10000000000 : ℝ), (994688509/2500000000 : ℝ), (4576110277/10000000000 : ℝ)] ![(33253065087111/100000000000000 : ℝ), (30362856703963/100000000000000 : ℝ), (36384078195941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268546777/10000000000 : ℝ)|^4515 ≤ (33253065087111/100000000000000 : ℝ)^3491
        have hw : |(4268546777/10000000000 : ℝ)|=(4268546777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994688509/2500000000 : ℝ)|^4515 ≤ (30362856703963/100000000000000 : ℝ)^3491
        have hw : |(994688509/2500000000 : ℝ)|=(994688509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4576110277/10000000000 : ℝ)|^4515 ≤ (36384078195941/100000000000000 : ℝ)^3491
        have hw : |(4576110277/10000000000 : ℝ)|=(4576110277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-373691051/2000000000 : ℝ)*x 0 + (2598274599/5000000000 : ℝ)*x 1 + (5457211157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373691051/2000000000 : ℝ)^4515 ≤ (2855813670443/25000000000000 : ℝ)^3491 := by
    have hnat : (373691051 : ℕ)^4515*25000000000000^3491 ≤ 2855813670443^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373691051 2000000000 2855813670443 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598274599/5000000000 : ℝ)^4515 ≤ (42887127689489/100000000000000 : ℝ)^3491 := by
    have hnat : (2598274599 : ℕ)^4515*100000000000000^3491 ≤ 42887127689489^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598274599 5000000000 42887127689489 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457211157/10000000000 : ℝ)^4515 ≤ (22844808805319/50000000000000 : ℝ)^3491 := by
    have hnat : (5457211157 : ℕ)^4515*50000000000000^3491 ≤ 22844808805319^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457211157 10000000000 22844808805319 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373691051/2000000000 : ℝ), (2598274599/5000000000 : ℝ), (5457211157/10000000000 : ℝ)] ![(2855813670443/25000000000000 : ℝ), (42887127689489/100000000000000 : ℝ), (22844808805319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373691051/2000000000 : ℝ)|^4515 ≤ (2855813670443/25000000000000 : ℝ)^3491
        have hw : |(-373691051/2000000000 : ℝ)|=(373691051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598274599/5000000000 : ℝ)|^4515 ≤ (42887127689489/100000000000000 : ℝ)^3491
        have hw : |(2598274599/5000000000 : ℝ)|=(2598274599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457211157/10000000000 : ℝ)|^4515 ≤ (22844808805319/50000000000000 : ℝ)^3491
        have hw : |(5457211157/10000000000 : ℝ)|=(5457211157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644517703/5000000000 : ℝ)*x 0 + (-348401109/2000000000 : ℝ)*x 1 + (2728606107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644517703/5000000000 : ℝ)^4515 ≤ (21938437388431/50000000000000 : ℝ)^3491 := by
    have hnat : (2644517703 : ℕ)^4515*50000000000000^3491 ≤ 21938437388431^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644517703 5000000000 21938437388431 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348401109/2000000000 : ℝ)^4515 ≤ (1304187018891/12500000000000 : ℝ)^3491 := by
    have hnat : (348401109 : ℕ)^4515*12500000000000^3491 ≤ 1304187018891^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348401109 2000000000 1304187018891 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728606107/5000000000 : ℝ)^4515 ≤ (11422407264001/25000000000000 : ℝ)^3491 := by
    have hnat : (2728606107 : ℕ)^4515*25000000000000^3491 ≤ 11422407264001^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728606107 5000000000 11422407264001 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644517703/5000000000 : ℝ), (-348401109/2000000000 : ℝ), (2728606107/5000000000 : ℝ)] ![(21938437388431/50000000000000 : ℝ), (1304187018891/12500000000000 : ℝ), (11422407264001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644517703/5000000000 : ℝ)|^4515 ≤ (21938437388431/50000000000000 : ℝ)^3491
        have hw : |(2644517703/5000000000 : ℝ)|=(2644517703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-348401109/2000000000 : ℝ)|^4515 ≤ (1304187018891/12500000000000 : ℝ)^3491
        have hw : |(-348401109/2000000000 : ℝ)|=(348401109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728606107/5000000000 : ℝ)|^4515 ≤ (11422407264001/25000000000000 : ℝ)^3491
        have hw : |(2728606107/5000000000 : ℝ)|=(2728606107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644517947/5000000000 : ℝ)*x 0 + (2728605741/5000000000 : ℝ)*x 1 + (-1742005893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644517947/5000000000 : ℝ)^4515 ≤ (43876880012709/100000000000000 : ℝ)^3491 := by
    have hnat : (2644517947 : ℕ)^4515*100000000000000^3491 ≤ 43876880012709^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644517947 5000000000 43876880012709 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728605741/5000000000 : ℝ)^4515 ≤ (4568962112979/10000000000000 : ℝ)^3491 := by
    have hnat : (2728605741 : ℕ)^4515*10000000000000^3491 ≤ 4568962112979^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728605741 5000000000 4568962112979 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1742005893/10000000000 : ℝ)^4515 ≤ (10433498846803/100000000000000 : ℝ)^3491 := by
    have hnat : (1742005893 : ℕ)^4515*100000000000000^3491 ≤ 10433498846803^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742005893 10000000000 10433498846803 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644517947/5000000000 : ℝ), (2728605741/5000000000 : ℝ), (-1742005893/10000000000 : ℝ)] ![(43876880012709/100000000000000 : ℝ), (4568962112979/10000000000000 : ℝ), (10433498846803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644517947/5000000000 : ℝ)|^4515 ≤ (43876880012709/100000000000000 : ℝ)^3491
        have hw : |(2644517947/5000000000 : ℝ)|=(2644517947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728605741/5000000000 : ℝ)|^4515 ≤ (4568962112979/10000000000000 : ℝ)^3491
        have hw : |(2728605741/5000000000 : ℝ)|=(2728605741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1742005893/10000000000 : ℝ)|^4515 ≤ (10433498846803/100000000000000 : ℝ)^3491
        have hw : |(-1742005893/10000000000 : ℝ)|=(1742005893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s2_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268667489/10000000000 : ℝ)*x 0 + (4572362703/10000000000 : ℝ)*x 1 + (3982534349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268667489/10000000000 : ℝ)^4515 ≤ (33254281306129/100000000000000 : ℝ)^3491 := by
    have hnat : (4268667489 : ℕ)^4515*100000000000000^3491 ≤ 33254281306129^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268667489 10000000000 33254281306129 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4572362703/10000000000 : ℝ)^4515 ≤ (7269109251779/20000000000000 : ℝ)^3491 := by
    have hnat : (4572362703 : ℕ)^4515*20000000000000^3491 ≤ 7269109251779^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572362703 10000000000 7269109251779 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3982534349/10000000000 : ℝ)^4515 ≤ (7600043103371/25000000000000 : ℝ)^3491 := by
    have hnat : (3982534349 : ℕ)^4515*25000000000000^3491 ≤ 7600043103371^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982534349 10000000000 7600043103371 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268667489/10000000000 : ℝ), (4572362703/10000000000 : ℝ), (3982534349/10000000000 : ℝ)] ![(33254281306129/100000000000000 : ℝ), (7269109251779/20000000000000 : ℝ), (7600043103371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268667489/10000000000 : ℝ)|^4515 ≤ (33254281306129/100000000000000 : ℝ)^3491
        have hw : |(4268667489/10000000000 : ℝ)|=(4268667489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4572362703/10000000000 : ℝ)|^4515 ≤ (7269109251779/20000000000000 : ℝ)^3491
        have hw : |(4572362703/10000000000 : ℝ)|=(4572362703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3982534349/10000000000 : ℝ)|^4515 ≤ (7600043103371/25000000000000 : ℝ)^3491
        have hw : |(3982534349/10000000000 : ℝ)|=(3982534349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2079/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (521/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2001/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3673/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2079/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3673/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2079/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3673/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2079/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3673/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2079/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3673/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2079/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3673/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2079/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2079/25000 : ℝ) ^ (4513/1024 : ℝ) ≤ (54283573679659/3125000000000000000 : ℝ) := by
    have hpowers : (2079/25000 : ℝ)^4513 ≤ (54283573679659/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2079 : ℕ)^4513*3125000000000000000^1024 ≤ 54283573679659^1024*25000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2079 25000 54283573679659 3125000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2079/25000 : ℝ)) (X := (54283573679659/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3673/20000 : ℝ) ^ (4513/1024 : ℝ) ≤ (14262028400666157/25000000000000000000 : ℝ) := by
    have hpowers : (3673/20000 : ℝ)^4513 ≤ (14262028400666157/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3673 : ℕ)^4513*25000000000000000000^1024 ≤ 14262028400666157^1024*20000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 20000 14262028400666157 25000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/20000 : ℝ)) (X := (14262028400666157/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562554283573679659/1562500000000000000 : ℝ) ≤ (10000078827398859/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (1562554283573679659/1562500000000000000 : ℝ)^1024 ≤ (10000078827398859/10000000000000000 : ℝ)^4513 := by
      have hnat : (1562554283573679659 : ℕ)^1024*10000000000000000^4513 ≤ 10000078827398859^4513*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562554283573679659 1562500000000000000 10000078827398859 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078827398859/10000000000000000 : ℝ)) (X := (1562554283573679659/1562500000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25014696296990103429/25000000000000000000 : ℝ) ≤ (10001333533317733/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (25014696296990103429/25000000000000000000 : ℝ)^1024 ≤ (10001333533317733/10000000000000000 : ℝ)^4513 := by
      have hnat : (25014696296990103429 : ℕ)^1024*10000000000000000^4513 ≤ 10001333533317733^4513*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014696296990103429 25000000000000000000 10001333533317733 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001333533317733/10000000000000000 : ℝ)) (X := (25014696296990103429/25000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514262028400666157/12500000000000000000 : ℝ) ≤ (10002588239236607/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (12514262028400666157/12500000000000000000 : ℝ)^1024 ≤ (10002588239236607/10000000000000000 : ℝ)^4513 := by
      have hnat : (12514262028400666157 : ℕ)^1024*10000000000000000^4513 ≤ 10002588239236607^4513*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514262028400666157 12500000000000000000 10002588239236607 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002588239236607/10000000000000000 : ℝ)) (X := (12514262028400666157/12500000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(54283573679659/3125000000000000000 : ℝ) ≤ ((100469923867688421723/100490000000000000000 : ℝ)+2*(627352959437/502450000000000 : ℝ)*(2079/25000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (100469923867688421723/100490000000000000000 : ℝ)+2*(627352959437/502450000000000 : ℝ)*(2079/25000 : ℝ)=(10000078827398859/10000000000000000 : ℝ) by norm_num, show 1+2*(54283573679659/3125000000000000000 : ℝ)=(1562554283573679659/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14262028400666157/25000000000000000000 : ℝ)+(54283573679659/3125000000000000000 : ℝ) ≤ ((100469923867688421723/100490000000000000000 : ℝ)+(627352959437/502450000000000 : ℝ)*((3673/20000 : ℝ)+(2079/25000 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (100469923867688421723/100490000000000000000 : ℝ)+(627352959437/502450000000000 : ℝ)*((3673/20000 : ℝ)+(2079/25000 : ℝ))=(10001333533317733/10000000000000000 : ℝ) by norm_num, show 1+(14262028400666157/25000000000000000000 : ℝ)+(54283573679659/3125000000000000000 : ℝ)=(25014696296990103429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14262028400666157/25000000000000000000 : ℝ) ≤ ((100469923867688421723/100490000000000000000 : ℝ)+2*(627352959437/502450000000000 : ℝ)*(3673/20000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (100469923867688421723/100490000000000000000 : ℝ)+2*(627352959437/502450000000000 : ℝ)*(3673/20000 : ℝ)=(10002588239236607/10000000000000000 : ℝ) by norm_num, show 1+2*(14262028400666157/25000000000000000000 : ℝ)=(12514262028400666157/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (100469923867688421723/100490000000000000000 : ℝ)*(X 1 0+X 2 0)+(627352959437/502450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (2079/25000 : ℝ)) (hi := (3673/20000 : ℝ)) (c := (100469923867688421723/100490000000000000000 : ℝ)) (alpha := (627352959437/502450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (100469923867688421723/100490000000000000000 : ℝ)*(X 0 1+X 2 1)+(627352959437/502450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (2079/25000 : ℝ)) (hi := (3673/20000 : ℝ)) (c := (100469923867688421723/100490000000000000000 : ℝ)) (alpha := (627352959437/502450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (100469923867688421723/100490000000000000000 : ℝ)*(X 0 2+X 1 2)+(627352959437/502450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (2079/25000 : ℝ)) (hi := (3673/20000 : ℝ)) (c := (100469923867688421723/100490000000000000000 : ℝ)) (alpha := (627352959437/502450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-467100881/2500000000 : ℝ)*X 0 0+(2729441173/5000000000 : ℝ)*X 0 1+(1298723003/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679161669/5000000000 : ℝ)*X 1 0+(-10021623/50000000 : ℝ)*X 1 1+(649361601/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679162117/5000000000 : ℝ)*X 2 0+(5194892217/10000000000 : ℝ)*X 2 1+(-1002162093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268546777/10000000000 : ℝ)*X 0 0+(994688509/2500000000 : ℝ)*X 0 1+(4576110277/10000000000 : ℝ)*X 0 2+(4268546777/10000000000 : ℝ)*X 1 0+(994688509/2500000000 : ℝ)*X 1 1+(4576110277/10000000000 : ℝ)*X 1 2+(4268546777/10000000000 : ℝ)*X 2 0+(994688509/2500000000 : ℝ)*X 2 1+(4576110277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-373691051/2000000000 : ℝ)*X 0 0+(2598274599/5000000000 : ℝ)*X 0 1+(5457211157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644517703/5000000000 : ℝ)*X 1 0+(-348401109/2000000000 : ℝ)*X 1 1+(2728606107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644517947/5000000000 : ℝ)*X 2 0+(2728605741/5000000000 : ℝ)*X 2 1+(-1742005893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268667489/10000000000 : ℝ)*X 0 0+(4572362703/10000000000 : ℝ)*X 0 1+(3982534349/10000000000 : ℝ)*X 0 2+(4268667489/10000000000 : ℝ)*X 1 0+(4572362703/10000000000 : ℝ)*X 1 1+(3982534349/10000000000 : ℝ)*X 1 2+(4268667489/10000000000 : ℝ)*X 2 0+(4572362703/10000000000 : ℝ)*X 2 1+(3982534349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18331332138735112801708869849/2512250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1483542301/100000000000000 : ℝ)*(base19) + (445284929/25000000000000 : ℝ)*(base23) + (114919321/100000000000000 : ℝ)*(upper3) + (179949021/100000000000000 : ℝ)*(upper4) + (64300867/20000000000000 : ℝ)*(upper5) + (1365536478157721/50000000000000 : ℝ)*(major0) + (1365536478157721/50000000000000 : ℝ)*(major1) + (1365536478157721/50000000000000 : ℝ)*(major2) + (1894020224348107/50000000000000 : ℝ)*(sp0) + (378807325427933/10000000000000 : ℝ)*(sp1) + (757614591336383/20000000000000 : ℝ)*(sp2) + (837028382751691/50000000000000 : ℝ)*(sp3) + (34289125417/100000000000000 : ℝ)*(sp4) + (1416607991/10000000000000 : ℝ)*(sp7) + (418517732895823/25000000000000 : ℝ)*(f.failure) + (378807473782163/10000000000000 : ℝ)*(f.sum) + (79026699174277/50245000000000000000000000000 : ℝ)*base66 + (10984320182517973283/5024500000000000000000000000000000 : ℝ)*base67 + (27767414168532526717/5024500000000000000000000000000000 : ℝ)*base70 + (77839289509156026717/5024500000000000000000000000000000 : ℝ)*base72 + (53584175187109/25122500000000000000000000000 : ℝ)*base73 + (24210764579306026717/5024500000000000000000000000000000 : ℝ)*base76 + (2793480961121026717/5024500000000000000000000000000000 : ℝ)*base78 + (4835578534865473283/5024500000000000000000000000000000 : ℝ)*base79 + (113323703802561/25122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (690363/125000000000000000000 : ℝ)*base89 + (690363/125000000000000000000 : ℝ)*base91 + (690363/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143602828908172253056379763/12561250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1376425127/100000000000000 : ℝ)*(base23) + (2491647/50000000000000 : ℝ)*(lower2) + (9718923/3125000000000 : ℝ)*(upper3) + (457678237/100000000000000 : ℝ)*(lower4) + (13829476135827/500000000000 : ℝ)*(major0) + (13829476135827/500000000000 : ℝ)*(major1) + (13829476135827/500000000000 : ℝ)*(major2) + (360244801/10000000000000 : ℝ)*(sp1) + (8157708281/50000000000000 : ℝ)*(sp2) + (3026812241/100000000000000 : ℝ)*(sp3) + (1918187034377079/50000000000000 : ℝ)*(sp4) + (959092616576537/25000000000000 : ℝ)*(sp5) + (383635637691247/10000000000000 : ℝ)*(sp6) + (847706488845387/50000000000000 : ℝ)*(sp7) + (847708002251507/50000000000000 : ℝ)*(f.failure) + (1918187034377079/50000000000000 : ℝ)*(f.sum) + (65411180207277/10049000000000000000000000000 : ℝ)*base66 + (99045156224920079/50245000000000000000000000000000 : ℝ)*base68 + (125870777601364921/50245000000000000000000000000000 : ℝ)*base69 + (333069038181525079/50245000000000000000000000000000 : ℝ)*base72 + (16097490657421/5024500000000000000000000000 : ℝ)*base74 + (303425665120405079/50245000000000000000000000000000 : ℝ)*base76 + (2140563988095425079/50245000000000000000000000000000 : ℝ)*base78 + (1075085091961370079/50245000000000000000000000000000 : ℝ)*base80 + (18773320552511/10049000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (179633/250000000000000000000 : ℝ)*base90 + (179633/250000000000000000000 : ℝ)*base92 + (179633/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1509_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2079/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1509_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1509_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1509_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1509_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1509_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1441_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:46.562982+00:00
-- url     : https://prove2.me/submissions/1db47a51-e28c-4a85-9d3b-a4d60045e95d

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
theorem support_rectangle_w1441_s3_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-980225339/5000000000 : ℝ)*x 0 + (1354020787/2500000000 : ℝ)*x 1 + (654916827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980225339/5000000000 : ℝ)^4401 ≤ (5980653290969/50000000000000 : ℝ)^3377 := by
    have hnat : (980225339 : ℕ)^4401*50000000000000^3377 ≤ 5980653290969^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980225339 5000000000 5980653290969 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354020787/2500000000 : ℝ)^4401 ≤ (5621359295173/12500000000000 : ℝ)^3377 := by
    have hnat : (1354020787 : ℕ)^4401*12500000000000^3377 ≤ 5621359295173^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354020787 2500000000 5621359295173 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654916827/1250000000 : ℝ)^4401 ≤ (43067819049813/100000000000000 : ℝ)^3377 := by
    have hnat : (654916827 : ℕ)^4401*100000000000000^3377 ≤ 43067819049813^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654916827 1250000000 43067819049813 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-980225339/5000000000 : ℝ), (1354020787/2500000000 : ℝ), (654916827/1250000000 : ℝ)] ![(5980653290969/50000000000000 : ℝ), (5621359295173/12500000000000 : ℝ), (43067819049813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-980225339/5000000000 : ℝ)|^4401 ≤ (5980653290969/50000000000000 : ℝ)^3377
        have hw : |(-980225339/5000000000 : ℝ)|=(980225339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354020787/2500000000 : ℝ)|^4401 ≤ (5621359295173/12500000000000 : ℝ)^3377
        have hw : |(1354020787/2500000000 : ℝ)|=(1354020787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654916827/1250000000 : ℝ)|^4401 ≤ (43067819049813/100000000000000 : ℝ)^3377
        have hw : |(654916827/1250000000 : ℝ)|=(654916827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668658221/1250000000 : ℝ)*x 0 + (-64080949/312500000 : ℝ)*x 1 + (5239333959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668658221/1250000000 : ℝ)^4401 ≤ (8849840313389/20000000000000 : ℝ)^3377 := by
    have hnat : (668658221 : ℕ)^4401*20000000000000^3377 ≤ 8849840313389^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668658221 1250000000 8849840313389 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64080949/312500000 : ℝ)^4401 ≤ (79268665033/625000000000 : ℝ)^3377 := by
    have hnat : (64080949 : ℕ)^4401*625000000000^3377 ≤ 79268665033^3377*312500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64080949 312500000 79268665033 625000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239333959/10000000000 : ℝ)^4401 ≤ (107669530029/250000000000 : ℝ)^3377 := by
    have hnat : (5239333959 : ℕ)^4401*250000000000^3377 ≤ 107669530029^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239333959 10000000000 107669530029 250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668658221/1250000000 : ℝ), (-64080949/312500000 : ℝ), (5239333959/10000000000 : ℝ)] ![(8849840313389/20000000000000 : ℝ), (79268665033/625000000000 : ℝ), (107669530029/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668658221/1250000000 : ℝ)|^4401 ≤ (8849840313389/20000000000000 : ℝ)^3377
        have hw : |(668658221/1250000000 : ℝ)|=(668658221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64080949/312500000 : ℝ)|^4401 ≤ (79268665033/625000000000 : ℝ)^3377
        have hw : |(-64080949/312500000 : ℝ)|=(64080949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239333959/10000000000 : ℝ)|^4401 ≤ (107669530029/250000000000 : ℝ)^3377
        have hw : |(5239333959/10000000000 : ℝ)|=(5239333959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349265701/10000000000 : ℝ)*x 0 + (2619667043/5000000000 : ℝ)*x 1 + (-205059029/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349265701/10000000000 : ℝ)^4401 ≤ (44249200844663/100000000000000 : ℝ)^3377 := by
    have hnat : (5349265701 : ℕ)^4401*100000000000000^3377 ≤ 44249200844663^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349265701 10000000000 44249200844663 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619667043/5000000000 : ℝ)^4401 ≤ (43067813372107/100000000000000 : ℝ)^3377 := by
    have hnat : (2619667043 : ℕ)^4401*100000000000000^3377 ≤ 43067813372107^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619667043 5000000000 43067813372107 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205059029/1000000000 : ℝ)^4401 ≤ (12682985776559/100000000000000 : ℝ)^3377 := by
    have hnat : (205059029 : ℕ)^4401*100000000000000^3377 ≤ 12682985776559^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205059029 1000000000 12682985776559 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349265701/10000000000 : ℝ), (2619667043/5000000000 : ℝ), (-205059029/1000000000 : ℝ)] ![(44249200844663/100000000000000 : ℝ), (43067813372107/100000000000000 : ℝ), (12682985776559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349265701/10000000000 : ℝ)|^4401 ≤ (44249200844663/100000000000000 : ℝ)^3377
        have hw : |(5349265701/10000000000 : ℝ)|=(5349265701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619667043/5000000000 : ℝ)|^4401 ≤ (43067813372107/100000000000000 : ℝ)^3377
        have hw : |(2619667043/5000000000 : ℝ)|=(2619667043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205059029/1000000000 : ℝ)|^4401 ≤ (12682985776559/100000000000000 : ℝ)^3377
        have hw : |(-205059029/1000000000 : ℝ)|=(205059029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430077903/1000000000 : ℝ)*x 0 + (205629511/500000000 : ℝ)*x 1 + (899327649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430077903/1000000000 : ℝ)^4401 ≤ (16649395370059/50000000000000 : ℝ)^3377 := by
    have hnat : (430077903 : ℕ)^4401*50000000000000^3377 ≤ 16649395370059^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430077903 1000000000 16649395370059 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205629511/500000000 : ℝ)^4401 ≤ (6282529542507/20000000000000 : ℝ)^3377 := by
    have hnat : (205629511 : ℕ)^4401*20000000000000^3377 ≤ 6282529542507^3377*500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205629511 500000000 6282529542507 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899327649/2000000000 : ℝ)^4401 ≤ (1764428076261/5000000000000 : ℝ)^3377 := by
    have hnat : (899327649 : ℕ)^4401*5000000000000^3377 ≤ 1764428076261^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899327649 2000000000 1764428076261 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430077903/1000000000 : ℝ), (205629511/500000000 : ℝ), (899327649/2000000000 : ℝ)] ![(16649395370059/50000000000000 : ℝ), (6282529542507/20000000000000 : ℝ), (1764428076261/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430077903/1000000000 : ℝ)|^4401 ≤ (16649395370059/50000000000000 : ℝ)^3377
        have hw : |(430077903/1000000000 : ℝ)|=(430077903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205629511/500000000 : ℝ)|^4401 ≤ (6282529542507/20000000000000 : ℝ)^3377
        have hw : |(205629511/500000000 : ℝ)|=(205629511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899327649/2000000000 : ℝ)|^4401 ≤ (1764428076261/5000000000000 : ℝ)^3377
        have hw : |(899327649/2000000000 : ℝ)|=(899327649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1960465301/10000000000 : ℝ)*x 0 + (1048007431/2000000000 : ℝ)*x 1 + (5415376867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960465301/10000000000 : ℝ)^4401 ≤ (5980711427617/50000000000000 : ℝ)^3377 := by
    have hnat : (1960465301 : ℕ)^4401*50000000000000^3377 ≤ 5980711427617^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960465301 10000000000 5980711427617 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048007431/2000000000 : ℝ)^4401 ≤ (43075345259579/100000000000000 : ℝ)^3377 := by
    have hnat : (1048007431 : ℕ)^4401*100000000000000^3377 ≤ 43075345259579^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048007431 2000000000 43075345259579 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415376867/10000000000 : ℝ)^4401 ≤ (44963231864807/100000000000000 : ℝ)^3377 := by
    have hnat : (5415376867 : ℕ)^4401*100000000000000^3377 ≤ 44963231864807^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415376867 10000000000 44963231864807 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1960465301/10000000000 : ℝ), (1048007431/2000000000 : ℝ), (5415376867/10000000000 : ℝ)] ![(5980711427617/50000000000000 : ℝ), (43075345259579/100000000000000 : ℝ), (44963231864807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1960465301/10000000000 : ℝ)|^4401 ≤ (5980711427617/50000000000000 : ℝ)^3377
        have hw : |(-1960465301/10000000000 : ℝ)|=(1960465301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048007431/2000000000 : ℝ)|^4401 ≤ (43075345259579/100000000000000 : ℝ)^3377
        have hw : |(1048007431/2000000000 : ℝ)|=(1048007431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415376867/10000000000 : ℝ)|^4401 ≤ (44963231864807/100000000000000 : ℝ)^3377
        have hw : |(5415376867/10000000000 : ℝ)|=(5415376867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303262783/10000000000 : ℝ)*x 0 + (-1874548039/10000000000 : ℝ)*x 1 + (541537681/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303262783/10000000000 : ℝ)^4401 ≤ (43753922675733/100000000000000 : ℝ)^3377 := by
    have hnat : (5303262783 : ℕ)^4401*100000000000000^3377 ≤ 43753922675733^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303262783 10000000000 43753922675733 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1874548039/10000000000 : ℝ)^4401 ≤ (5641423031443/50000000000000 : ℝ)^3377 := by
    have hnat : (1874548039 : ℕ)^4401*50000000000000^3377 ≤ 5641423031443^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874548039 10000000000 5641423031443 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541537681/1000000000 : ℝ)^4401 ≤ (11240807812009/25000000000000 : ℝ)^3377 := by
    have hnat : (541537681 : ℕ)^4401*25000000000000^3377 ≤ 11240807812009^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541537681 1000000000 11240807812009 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303262783/10000000000 : ℝ), (-1874548039/10000000000 : ℝ), (541537681/1000000000 : ℝ)] ![(43753922675733/100000000000000 : ℝ), (5641423031443/50000000000000 : ℝ), (11240807812009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303262783/10000000000 : ℝ)|^4401 ≤ (43753922675733/100000000000000 : ℝ)^3377
        have hw : |(5303262783/10000000000 : ℝ)|=(5303262783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1874548039/10000000000 : ℝ)|^4401 ≤ (5641423031443/50000000000000 : ℝ)^3377
        have hw : |(-1874548039/10000000000 : ℝ)|=(1874548039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541537681/1000000000 : ℝ)|^4401 ≤ (11240807812009/25000000000000 : ℝ)^3377
        have hw : |(541537681/1000000000 : ℝ)|=(541537681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651630747/5000000000 : ℝ)*x 0 + (5415377861/10000000000 : ℝ)*x 1 + (-468637089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651630747/5000000000 : ℝ)^4401 ≤ (43753908816249/100000000000000 : ℝ)^3377 := by
    have hnat : (2651630747 : ℕ)^4401*100000000000000^3377 ≤ 43753908816249^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651630747 5000000000 43753908816249 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415377861/10000000000 : ℝ)^4401 ≤ (44963242620429/100000000000000 : ℝ)^3377 := by
    have hnat : (5415377861 : ℕ)^4401*100000000000000^3377 ≤ 44963242620429^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415377861 10000000000 44963242620429 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468637089/2500000000 : ℝ)^4401 ≤ (5641424274731/50000000000000 : ℝ)^3377 := by
    have hnat : (468637089 : ℕ)^4401*50000000000000^3377 ≤ 5641424274731^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468637089 2500000000 5641424274731 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651630747/5000000000 : ℝ), (5415377861/10000000000 : ℝ), (-468637089/2500000000 : ℝ)] ![(43753908816249/100000000000000 : ℝ), (44963242620429/100000000000000 : ℝ), (5641424274731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651630747/5000000000 : ℝ)|^4401 ≤ (43753908816249/100000000000000 : ℝ)^3377
        have hw : |(2651630747/5000000000 : ℝ)|=(2651630747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415377861/10000000000 : ℝ)|^4401 ≤ (44963242620429/100000000000000 : ℝ)^3377
        have hw : |(5415377861/10000000000 : ℝ)|=(5415377861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468637089/2500000000 : ℝ)|^4401 ≤ (5641424274731/50000000000000 : ℝ)^3377
        have hw : |(-468637089/2500000000 : ℝ)|=(468637089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s3_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430081081/1000000000 : ℝ)*x 0 + (4495112329/10000000000 : ℝ)*x 1 + (1028531407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430081081/1000000000 : ℝ)^4401 ≤ (33299111408411/100000000000000 : ℝ)^3377 := by
    have hnat : (430081081 : ℕ)^4401*100000000000000^3377 ≤ 33299111408411^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430081081 1000000000 33299111408411 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495112329/10000000000 : ℝ)^4401 ≤ (35272956136407/100000000000000 : ℝ)^3377 := by
    have hnat : (4495112329 : ℕ)^4401*100000000000000^3377 ≤ 35272956136407^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495112329 10000000000 35272956136407 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028531407/2500000000 : ℝ)^4401 ≤ (3928491555409/12500000000000 : ℝ)^3377 := by
    have hnat : (1028531407 : ℕ)^4401*12500000000000^3377 ≤ 3928491555409^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028531407 2500000000 3928491555409 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430081081/1000000000 : ℝ), (4495112329/10000000000 : ℝ), (1028531407/2500000000 : ℝ)] ![(33299111408411/100000000000000 : ℝ), (35272956136407/100000000000000 : ℝ), (3928491555409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430081081/1000000000 : ℝ)|^4401 ≤ (33299111408411/100000000000000 : ℝ)^3377
        have hw : |(430081081/1000000000 : ℝ)|=(430081081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495112329/10000000000 : ℝ)|^4401 ≤ (35272956136407/100000000000000 : ℝ)^3377
        have hw : |(4495112329/10000000000 : ℝ)|=(4495112329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028531407/2500000000 : ℝ)|^4401 ≤ (3928491555409/12500000000000 : ℝ)^3377
        have hw : |(1028531407/2500000000 : ℝ)|=(1028531407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11197/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14941/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10431/100000 : ℝ) ^ (275/64 : ℝ) ≤ (3025793607262323/50000000000000000000 : ℝ) := by
    have hpowers : (10431/100000 : ℝ)^275 ≤ (3025793607262323/50000000000000000000 : ℝ)^64 := by
      have hnat : (10431 : ℕ)^275*50000000000000000000^64 ≤ 3025793607262323^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10431 100000 3025793607262323 50000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10431/100000 : ℝ)) (X := (3025793607262323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (15763/100000 : ℝ) ^ (275/64 : ℝ) ≤ (35674224694996279/100000000000000000000 : ℝ) := by
    have hpowers : (15763/100000 : ℝ)^275 ≤ (35674224694996279/100000000000000000000 : ℝ)^64 := by
      have hnat : (15763 : ℕ)^275*100000000000000000000^64 ≤ 35674224694996279^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15763 100000 35674224694996279 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15763/100000 : ℝ)) (X := (35674224694996279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003025793607262323/25000000000000000000 : ℝ) ≤ (10000281660799823/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (25003025793607262323/25000000000000000000 : ℝ)^64 ≤ (10000281660799823/10000000000000000 : ℝ)^275 := by
      have hnat : (25003025793607262323 : ℕ)^64*10000000000000000^275 ≤ 10000281660799823^275*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003025793607262323 25000000000000000000 10000281660799823 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281660799823/10000000000000000 : ℝ)) (X := (25003025793607262323/25000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001669032476380837/4000000000000000000 : ℝ) ≤ (2500242729508511/2500000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (4001669032476380837/4000000000000000000 : ℝ)^64 ≤ (2500242729508511/2500000000000000 : ℝ)^275 := by
      have hnat : (4001669032476380837 : ℕ)^64*2500000000000000^275 ≤ 2500242729508511^275*4000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001669032476380837 4000000000000000000 2500242729508511 2500000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500242729508511/2500000000000000 : ℝ)) (X := (4001669032476380837/4000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035674224694996279/50000000000000000000 : ℝ) ≤ (2000332035053653/2000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50035674224694996279/50000000000000000000 : ℝ)^64 ≤ (2000332035053653/2000000000000000 : ℝ)^275 := by
      have hnat : (50035674224694996279 : ℕ)^64*2000000000000000^275 ≤ 2000332035053653^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035674224694996279 50000000000000000000 2000332035053653 2000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000332035053653/2000000000000000 : ℝ)) (X := (50035674224694996279/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3025793607262323/50000000000000000000 : ℝ) ≤ ((26653561265482168867/26660000000000000000 : ℝ)+2*(689257234221/533200000000000 : ℝ)*(10431/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (26653561265482168867/26660000000000000000 : ℝ)+2*(689257234221/533200000000000 : ℝ)*(10431/100000 : ℝ)=(10000281660799823/10000000000000000 : ℝ) by norm_num, show 1+2*(3025793607262323/50000000000000000000 : ℝ)=(25003025793607262323/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35674224694996279/100000000000000000000 : ℝ)+(3025793607262323/50000000000000000000 : ℝ) ≤ ((26653561265482168867/26660000000000000000 : ℝ)+(689257234221/533200000000000 : ℝ)*((15763/100000 : ℝ)+(10431/100000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (26653561265482168867/26660000000000000000 : ℝ)+(689257234221/533200000000000 : ℝ)*((15763/100000 : ℝ)+(10431/100000 : ℝ))=(2500242729508511/2500000000000000 : ℝ) by norm_num, show 1+(35674224694996279/100000000000000000000 : ℝ)+(3025793607262323/50000000000000000000 : ℝ)=(4001669032476380837/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35674224694996279/100000000000000000000 : ℝ) ≤ ((26653561265482168867/26660000000000000000 : ℝ)+2*(689257234221/533200000000000 : ℝ)*(15763/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (26653561265482168867/26660000000000000000 : ℝ)+2*(689257234221/533200000000000 : ℝ)*(15763/100000 : ℝ)=(2000332035053653/2000000000000000 : ℝ) by norm_num, show 1+2*(35674224694996279/100000000000000000000 : ℝ)=(50035674224694996279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26653561265482168867/26660000000000000000 : ℝ)*(X 1 0+X 2 0)+(689257234221/533200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (15763/100000 : ℝ)) (c := (26653561265482168867/26660000000000000000 : ℝ)) (alpha := (689257234221/533200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26653561265482168867/26660000000000000000 : ℝ)*(X 0 1+X 2 1)+(689257234221/533200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (15763/100000 : ℝ)) (c := (26653561265482168867/26660000000000000000 : ℝ)) (alpha := (689257234221/533200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26653561265482168867/26660000000000000000 : ℝ)*(X 0 2+X 1 2)+(689257234221/533200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (15763/100000 : ℝ)) (c := (26653561265482168867/26660000000000000000 : ℝ)) (alpha := (689257234221/533200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-980225339/5000000000 : ℝ)*X 0 0+(1354020787/2500000000 : ℝ)*X 0 1+(654916827/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668658221/1250000000 : ℝ)*X 1 0+(-64080949/312500000 : ℝ)*X 1 1+(5239333959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349265701/10000000000 : ℝ)*X 2 0+(2619667043/5000000000 : ℝ)*X 2 1+(-205059029/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430077903/1000000000 : ℝ)*X 0 0+(205629511/500000000 : ℝ)*X 0 1+(899327649/2000000000 : ℝ)*X 0 2+(430077903/1000000000 : ℝ)*X 1 0+(205629511/500000000 : ℝ)*X 1 1+(899327649/2000000000 : ℝ)*X 1 2+(430077903/1000000000 : ℝ)*X 2 0+(205629511/500000000 : ℝ)*X 2 1+(899327649/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1960465301/10000000000 : ℝ)*X 0 0+(1048007431/2000000000 : ℝ)*X 0 1+(5415376867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303262783/10000000000 : ℝ)*X 1 0+(-1874548039/10000000000 : ℝ)*X 1 1+(541537681/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651630747/5000000000 : ℝ)*X 2 0+(5415377861/10000000000 : ℝ)*X 2 1+(-468637089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430081081/1000000000 : ℝ)*X 0 0+(4495112329/10000000000 : ℝ)*X 0 1+(1028531407/2500000000 : ℝ)*X 0 2+(430081081/1000000000 : ℝ)*X 1 0+(4495112329/10000000000 : ℝ)*X 1 1+(1028531407/2500000000 : ℝ)*X 1 2+(430081081/1000000000 : ℝ)*X 2 0+(4495112329/10000000000 : ℝ)*X 2 1+(1028531407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (683494100619611194778634693/83312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1336440393/100000000000000 : ℝ)*(base19) + (1171331689/100000000000000 : ℝ)*(base23) + (25206967/50000000000000 : ℝ)*(lower2) + (12888761/20000000000000 : ℝ)*(upper3) + (18717679/25000000000000 : ℝ)*(upper5) + (258175910746607/6250000000000 : ℝ)*(major0) + (258175910746607/6250000000000 : ℝ)*(major1) + (258175910746607/6250000000000 : ℝ)*(major2) + (5657765921389741/100000000000000 : ℝ)*(sp0) + (5657775950111133/100000000000000 : ℝ)*(sp1) + (1414444028804959/25000000000000 : ℝ)*(sp2) + (650961570327011/25000000000000 : ℝ)*(sp3) + (2273032357/20000000000000 : ℝ)*(sp4) + (5302565837/100000000000000 : ℝ)*(sp7) + (1301925791936941/50000000000000 : ℝ)*(f.failure) + (2828888643275763/50000000000000 : ℝ)*(f.sum) + (42080133436933/6665000000000000000000000000 : ℝ)*base65 + (1392813289454865731/166625000000000000000000000000000 : ℝ)*base68 + (378431276839759269/166625000000000000000000000000000 : ℝ)*base69 + (410140852963384269/166625000000000000000000000000000 : ℝ)*base71 + (8669364871103/6665000000000000000000000000 : ℝ)*base73 + (271550103181240731/166625000000000000000000000000000 : ℝ)*base76 + (1537017414708884269/166625000000000000000000000000000 : ℝ)*base77 + (1076265361026509269/166625000000000000000000000000000 : ℝ)*base79 + (11192994461887/1666250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (13883983/2500000000000000000000 : ℝ)*base90 + (13883983/2500000000000000000000 : ℝ)*base92 + (13883983/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11938456967071820921596288887/666500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137472723/50000000000000 : ℝ)*(base21) + (14764513/6250000000000 : ℝ)*(upper2) + (351745617/100000000000000 : ℝ)*(lower4) + (4056283/3125000000000 : ℝ)*(upper5) + (2081990682818229/50000000000000 : ℝ)*(major0) + (2081990682818229/50000000000000 : ℝ)*(major1) + (2081990682818229/50000000000000 : ℝ)*(major2) + (923308551/50000000000000 : ℝ)*(sp0) + (3919309557/100000000000000 : ℝ)*(sp2) + (409454503/25000000000000 : ℝ)*(sp3) + (5703202074574187/100000000000000 : ℝ)*(sp4) + (5703203921191289/100000000000000 : ℝ)*(sp5) + (1140639945387257/20000000000000 : ℝ)*(sp6) + (2624756575191487/100000000000000 : ℝ)*(sp7) + (1312379106504749/50000000000000 : ℝ)*(f.failure) + (5703203921191289/100000000000000 : ℝ)*(f.sum) + (110277245804101/13330000000000000000000000000 : ℝ)*base66 + (2909883180777673457/1333000000000000000000000000000000 : ℝ)*base68 + (11253839060846673457/1333000000000000000000000000000000 : ℝ)*base70 + (28034346058386673457/1333000000000000000000000000000000 : ℝ)*base72 + (60181846033249/13330000000000000000000000000 : ℝ)*base73 + (21735582141803673457/1333000000000000000000000000000000 : ℝ)*base76 + (3661796666066673457/1333000000000000000000000000000000 : ℝ)*base78 + (17689562278375673457/1333000000000000000000000000000000 : ℝ)*base80 + (46851991402771/13330000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12945487/2500000000000000000000 : ℝ)*base90 + (12945487/2500000000000000000000 : ℝ)*base92 + (12945487/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1441_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1441_s4_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961291759/10000000000 : ℝ)*x 0 + (169026991/312500000 : ℝ)*x 1 + (1311499991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961291759/10000000000 : ℝ)^4401 ≤ (11967994779253/100000000000000 : ℝ)^3377 := by
    have hnat : (1961291759 : ℕ)^4401*100000000000000^3377 ≤ 11967994779253^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961291759 10000000000 11967994779253 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169026991/312500000 : ℝ)^4401 ≤ (4489276883167/10000000000000 : ℝ)^3377 := by
    have hnat : (169026991 : ℕ)^4401*10000000000000^3377 ≤ 4489276883167^3377*312500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169026991 312500000 4489276883167 10000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311499991/2500000000 : ℝ)^4401 ≤ (43139236380553/100000000000000 : ℝ)^3377 := by
    have hnat : (1311499991 : ℕ)^4401*100000000000000^3377 ≤ 43139236380553^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311499991 2500000000 43139236380553 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961291759/10000000000 : ℝ), (169026991/312500000 : ℝ), (1311499991/2500000000 : ℝ)] ![(11967994779253/100000000000000 : ℝ), (4489276883167/10000000000000 : ℝ), (43139236380553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961291759/10000000000 : ℝ)|^4401 ≤ (11967994779253/100000000000000 : ℝ)^3377
        have hw : |(-1961291759/10000000000 : ℝ)|=(1961291759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169026991/312500000 : ℝ)|^4401 ≤ (4489276883167/10000000000000 : ℝ)^3377
        have hw : |(169026991/312500000 : ℝ)|=(169026991/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311499991/2500000000 : ℝ)|^4401 ≤ (43139236380553/100000000000000 : ℝ)^3377
        have hw : |(1311499991/2500000000 : ℝ)|=(1311499991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069479839/2000000000 : ℝ)*x 0 + (-2044222341/10000000000 : ℝ)*x 1 + (1311500043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069479839/2000000000 : ℝ)^4401 ≤ (4422908038111/10000000000000 : ℝ)^3377 := by
    have hnat : (1069479839 : ℕ)^4401*10000000000000^3377 ≤ 4422908038111^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069479839 2000000000 4422908038111 10000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044222341/10000000000 : ℝ)^4401 ≤ (6315840498809/50000000000000 : ℝ)^3377 := by
    have hnat : (2044222341 : ℕ)^4401*50000000000000^3377 ≤ 6315840498809^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044222341 10000000000 6315840498809 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311500043/2500000000 : ℝ)^4401 ≤ (10784809652411/25000000000000 : ℝ)^3377 := by
    have hnat : (1311500043 : ℕ)^4401*25000000000000^3377 ≤ 10784809652411^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311500043 2500000000 10784809652411 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069479839/2000000000 : ℝ), (-2044222341/10000000000 : ℝ), (1311500043/2500000000 : ℝ)] ![(4422908038111/10000000000000 : ℝ), (6315840498809/50000000000000 : ℝ), (10784809652411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069479839/2000000000 : ℝ)|^4401 ≤ (4422908038111/10000000000000 : ℝ)^3377
        have hw : |(1069479839/2000000000 : ℝ)|=(1069479839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044222341/10000000000 : ℝ)|^4401 ≤ (6315840498809/50000000000000 : ℝ)^3377
        have hw : |(-2044222341/10000000000 : ℝ)|=(2044222341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311500043/2500000000 : ℝ)|^4401 ≤ (10784809652411/25000000000000 : ℝ)^3377
        have hw : |(1311500043/2500000000 : ℝ)|=(1311500043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336849841/2500000000 : ℝ)*x 0 + (131150003/250000000 : ℝ)*x 1 + (-2044222183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336849841/2500000000 : ℝ)^4401 ≤ (44229082202791/100000000000000 : ℝ)^3377 := by
    have hnat : (1336849841 : ℕ)^4401*100000000000000^3377 ≤ 44229082202791^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336849841 2500000000 44229082202791 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131150003/250000000 : ℝ)^4401 ≤ (43139238052371/100000000000000 : ℝ)^3377 := by
    have hnat : (131150003 : ℕ)^4401*100000000000000^3377 ≤ 43139238052371^3377*250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131150003 250000000 43139238052371 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044222183/10000000000 : ℝ)^4401 ≤ (12631679725257/100000000000000 : ℝ)^3377 := by
    have hnat : (2044222183 : ℕ)^4401*100000000000000^3377 ≤ 12631679725257^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044222183 10000000000 12631679725257 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336849841/2500000000 : ℝ), (131150003/250000000 : ℝ), (-2044222183/10000000000 : ℝ)] ![(44229082202791/100000000000000 : ℝ), (43139238052371/100000000000000 : ℝ), (12631679725257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336849841/2500000000 : ℝ)|^4401 ≤ (44229082202791/100000000000000 : ℝ)^3377
        have hw : |(1336849841/2500000000 : ℝ)|=(1336849841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131150003/250000000 : ℝ)|^4401 ≤ (43139238052371/100000000000000 : ℝ)^3377
        have hw : |(131150003/250000000 : ℝ)|=(131150003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044222183/10000000000 : ℝ)|^4401 ≤ (12631679725257/100000000000000 : ℝ)^3377
        have hw : |(-2044222183/10000000000 : ℝ)|=(2044222183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150647827/5000000000 : ℝ)*x 0 + (515951643/1250000000 : ℝ)*x 1 + (4481491019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150647827/5000000000 : ℝ)^4401 ≤ (33304003696937/100000000000000 : ℝ)^3377 := by
    have hnat : (2150647827 : ℕ)^4401*100000000000000^3377 ≤ 33304003696937^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150647827 5000000000 33304003696937 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515951643/1250000000 : ℝ)^4401 ≤ (3945284088033/12500000000000 : ℝ)^3377 := by
    have hnat : (515951643 : ℕ)^4401*12500000000000^3377 ≤ 3945284088033^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515951643 1250000000 3945284088033 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481491019/10000000000 : ℝ)^4401 ≤ (35133723585233/100000000000000 : ℝ)^3377 := by
    have hnat : (4481491019 : ℕ)^4401*100000000000000^3377 ≤ 35133723585233^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481491019 10000000000 35133723585233 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150647827/5000000000 : ℝ), (515951643/1250000000 : ℝ), (4481491019/10000000000 : ℝ)] ![(33304003696937/100000000000000 : ℝ), (3945284088033/12500000000000 : ℝ), (35133723585233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150647827/5000000000 : ℝ)|^4401 ≤ (33304003696937/100000000000000 : ℝ)^3377
        have hw : |(2150647827/5000000000 : ℝ)|=(2150647827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515951643/1250000000 : ℝ)|^4401 ≤ (3945284088033/12500000000000 : ℝ)^3377
        have hw : |(515951643/1250000000 : ℝ)|=(515951643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481491019/10000000000 : ℝ)|^4401 ≤ (35133723585233/100000000000000 : ℝ)^3377
        have hw : |(4481491019/10000000000 : ℝ)|=(4481491019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961303609/10000000000 : ℝ)*x 0 + (131164923/250000000 : ℝ)*x 1 + (5408263531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961303609/10000000000 : ℝ)^4401 ≤ (11968089015557/100000000000000 : ℝ)^3377 := by
    have hnat : (1961303609 : ℕ)^4401*100000000000000^3377 ≤ 11968089015557^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961303609 10000000000 11968089015557 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131164923/250000000 : ℝ)^4401 ≤ (21572816969719/50000000000000 : ℝ)^3377 := by
    have hnat : (131164923 : ℕ)^4401*50000000000000^3377 ≤ 21572816969719^3377*250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131164923 250000000 21572816969719 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408263531/10000000000 : ℝ)^4401 ≤ (8977255404941/20000000000000 : ℝ)^3377 := by
    have hnat : (5408263531 : ℕ)^4401*20000000000000^3377 ≤ 8977255404941^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408263531 10000000000 8977255404941 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961303609/10000000000 : ℝ), (131164923/250000000 : ℝ), (5408263531/10000000000 : ℝ)] ![(11968089015557/100000000000000 : ℝ), (21572816969719/50000000000000 : ℝ), (8977255404941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961303609/10000000000 : ℝ)|^4401 ≤ (11968089015557/100000000000000 : ℝ)^3377
        have hw : |(-1961303609/10000000000 : ℝ)|=(1961303609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131164923/250000000 : ℝ)|^4401 ≤ (21572816969719/50000000000000 : ℝ)^3377
        have hw : |(131164923/250000000 : ℝ)|=(131164923/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408263531/10000000000 : ℝ)|^4401 ≤ (8977255404941/20000000000000 : ℝ)^3377
        have hw : |(5408263531/10000000000 : ℝ)|=(5408263531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652505059/5000000000 : ℝ)*x 0 + (-376391773/2000000000 : ℝ)*x 1 + (1352065877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652505059/5000000000 : ℝ)^4401 ≤ (21886355586029/50000000000000 : ℝ)^3377 := by
    have hnat : (2652505059 : ℕ)^4401*50000000000000^3377 ≤ 21886355586029^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652505059 5000000000 21886355586029 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376391773/2000000000 : ℝ)^4401 ≤ (70881325233/625000000000 : ℝ)^3377 := by
    have hnat : (376391773 : ℕ)^4401*625000000000^3377 ≤ 70881325233^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376391773 2000000000 70881325233 625000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352065877/2500000000 : ℝ)^4401 ≤ (44886276775931/100000000000000 : ℝ)^3377 := by
    have hnat : (1352065877 : ℕ)^4401*100000000000000^3377 ≤ 44886276775931^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352065877 2500000000 44886276775931 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652505059/5000000000 : ℝ), (-376391773/2000000000 : ℝ), (1352065877/2500000000 : ℝ)] ![(21886355586029/50000000000000 : ℝ), (70881325233/625000000000 : ℝ), (44886276775931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652505059/5000000000 : ℝ)|^4401 ≤ (21886355586029/50000000000000 : ℝ)^3377
        have hw : |(2652505059/5000000000 : ℝ)|=(2652505059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376391773/2000000000 : ℝ)|^4401 ≤ (70881325233/625000000000 : ℝ)^3377
        have hw : |(-376391773/2000000000 : ℝ)|=(376391773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352065877/2500000000 : ℝ)|^4401 ≤ (44886276775931/100000000000000 : ℝ)^3377
        have hw : |(1352065877/2500000000 : ℝ)|=(1352065877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53050101/100000000 : ℝ)*x 0 + (5408263537/10000000000 : ℝ)*x 1 + (-37639177/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53050101/100000000 : ℝ)^4401 ≤ (43772710978501/100000000000000 : ℝ)^3377 := by
    have hnat : (53050101 : ℕ)^4401*100000000000000^3377 ≤ 43772710978501^3377*100000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53050101 100000000 43772710978501 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408263537/10000000000 : ℝ)^4401 ≤ (22443138544801/50000000000000 : ℝ)^3377 := by
    have hnat : (5408263537 : ℕ)^4401*50000000000000^3377 ≤ 22443138544801^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408263537 10000000000 22443138544801 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37639177/200000000 : ℝ)^4401 ≤ (5670505959739/50000000000000 : ℝ)^3377 := by
    have hnat : (37639177 : ℕ)^4401*50000000000000^3377 ≤ 5670505959739^3377*200000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37639177 200000000 5670505959739 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53050101/100000000 : ℝ), (5408263537/10000000000 : ℝ), (-37639177/200000000 : ℝ)] ![(43772710978501/100000000000000 : ℝ), (22443138544801/50000000000000 : ℝ), (5670505959739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53050101/100000000 : ℝ)|^4401 ≤ (43772710978501/100000000000000 : ℝ)^3377
        have hw : |(53050101/100000000 : ℝ)|=(53050101/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408263537/10000000000 : ℝ)|^4401 ≤ (22443138544801/50000000000000 : ℝ)^3377
        have hw : |(5408263537/10000000000 : ℝ)|=(5408263537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37639177/200000000 : ℝ)|^4401 ≤ (5670505959739/50000000000000 : ℝ)^3377
        have hw : |(-37639177/200000000 : ℝ)|=(37639177/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s4_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150660593/5000000000 : ℝ)*x 0 + (4480194041/10000000000 : ℝ)*x 1 + (516114613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150660593/5000000000 : ℝ)^4401 ≤ (16652130665323/50000000000000 : ℝ)^3377 := by
    have hnat : (2150660593 : ℕ)^4401*50000000000000^3377 ≤ 16652130665323^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150660593 5000000000 16652130665323 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480194041/10000000000 : ℝ)^4401 ≤ (35120472986291/100000000000000 : ℝ)^3377 := by
    have hnat : (4480194041 : ℕ)^4401*100000000000000^3377 ≤ 35120472986291^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480194041 10000000000 35120472986291 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516114613/1250000000 : ℝ)^4401 ≤ (15787632831177/50000000000000 : ℝ)^3377 := by
    have hnat : (516114613 : ℕ)^4401*50000000000000^3377 ≤ 15787632831177^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516114613 1250000000 15787632831177 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150660593/5000000000 : ℝ), (4480194041/10000000000 : ℝ), (516114613/1250000000 : ℝ)] ![(16652130665323/50000000000000 : ℝ), (35120472986291/100000000000000 : ℝ), (15787632831177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150660593/5000000000 : ℝ)|^4401 ≤ (16652130665323/50000000000000 : ℝ)^3377
        have hw : |(2150660593/5000000000 : ℝ)|=(2150660593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480194041/10000000000 : ℝ)|^4401 ≤ (35120472986291/100000000000000 : ℝ)^3377
        have hw : |(4480194041/10000000000 : ℝ)|=(4480194041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516114613/1250000000 : ℝ)|^4401 ≤ (15787632831177/50000000000000 : ℝ)^3377
        have hw : |(516114613/1250000000 : ℝ)|=(516114613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1479/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14941/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14941/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14941/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14941/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14941/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14941/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11197/100000 : ℝ) ^ (275/64 : ℝ) ≤ (1025696294507227/12500000000000000000 : ℝ) := by
    have hpowers : (11197/100000 : ℝ)^275 ≤ (1025696294507227/12500000000000000000 : ℝ)^64 := by
      have hnat : (11197 : ℕ)^275*12500000000000000000^64 ≤ 1025696294507227^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11197 100000 1025696294507227 12500000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11197/100000 : ℝ)) (X := (1025696294507227/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14941/100000 : ℝ) ^ (275/64 : ℝ) ≤ (28340833997596967/100000000000000000000 : ℝ) := by
    have hpowers : (14941/100000 : ℝ)^275 ≤ (28340833997596967/100000000000000000000 : ℝ)^64 := by
      have hnat : (14941 : ℕ)^275*100000000000000000000^64 ≤ 28340833997596967^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14941 100000 28340833997596967 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14941/100000 : ℝ)) (X := (28340833997596967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251025696294507227/6250000000000000000 : ℝ) ≤ (625023869247391/625000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (6251025696294507227/6250000000000000000 : ℝ)^64 ≤ (625023869247391/625000000000000 : ℝ)^275 := by
      have hnat : (6251025696294507227 : ℕ)^64*625000000000000^275 ≤ 625023869247391^275*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251025696294507227 6250000000000000000 625023869247391 625000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625023869247391/625000000000000 : ℝ)) (X := (6251025696294507227/6250000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036546404353654783/100000000000000000000 : ℝ) ≤ (10000850415277547/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (100036546404353654783/100000000000000000000 : ℝ)^64 ≤ (10000850415277547/10000000000000000 : ℝ)^275 := by
      have hnat : (100036546404353654783 : ℕ)^64*10000000000000000^275 ≤ 10000850415277547^275*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036546404353654783 100000000000000000000 10000850415277547 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000850415277547/10000000000000000 : ℝ)) (X := (100036546404353654783/100000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028340833997596967/50000000000000000000 : ℝ) ≤ (5000659461298419/5000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50028340833997596967/50000000000000000000 : ℝ)^64 ≤ (5000659461298419/5000000000000000 : ℝ)^275 := by
      have hnat : (50028340833997596967 : ℕ)^64*5000000000000000^275 ≤ 5000659461298419^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028340833997596967 50000000000000000000 5000659461298419 5000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000659461298419/5000000000000000 : ℝ)) (X := (50028340833997596967/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1025696294507227/12500000000000000000 : ℝ) ≤ ((3743093811048750781/3744000000000000000 : ℝ)+2*(468507319291/374400000000000 : ℝ)*(11197/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (3743093811048750781/3744000000000000000 : ℝ)+2*(468507319291/374400000000000 : ℝ)*(11197/100000 : ℝ)=(625023869247391/625000000000000 : ℝ) by norm_num, show 1+2*(1025696294507227/12500000000000000000 : ℝ)=(6251025696294507227/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28340833997596967/100000000000000000000 : ℝ)+(1025696294507227/12500000000000000000 : ℝ) ≤ ((3743093811048750781/3744000000000000000 : ℝ)+(468507319291/374400000000000 : ℝ)*((14941/100000 : ℝ)+(11197/100000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (3743093811048750781/3744000000000000000 : ℝ)+(468507319291/374400000000000 : ℝ)*((14941/100000 : ℝ)+(11197/100000 : ℝ))=(10000850415277547/10000000000000000 : ℝ) by norm_num, show 1+(28340833997596967/100000000000000000000 : ℝ)+(1025696294507227/12500000000000000000 : ℝ)=(100036546404353654783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28340833997596967/100000000000000000000 : ℝ) ≤ ((3743093811048750781/3744000000000000000 : ℝ)+2*(468507319291/374400000000000 : ℝ)*(14941/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (3743093811048750781/3744000000000000000 : ℝ)+2*(468507319291/374400000000000 : ℝ)*(14941/100000 : ℝ)=(5000659461298419/5000000000000000 : ℝ) by norm_num, show 1+2*(28340833997596967/100000000000000000000 : ℝ)=(50028340833997596967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3743093811048750781/3744000000000000000 : ℝ)*(X 1 0+X 2 0)+(468507319291/374400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (3743093811048750781/3744000000000000000 : ℝ)) (alpha := (468507319291/374400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3743093811048750781/3744000000000000000 : ℝ)*(X 0 1+X 2 1)+(468507319291/374400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (3743093811048750781/3744000000000000000 : ℝ)) (alpha := (468507319291/374400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3743093811048750781/3744000000000000000 : ℝ)*(X 0 2+X 1 2)+(468507319291/374400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (3743093811048750781/3744000000000000000 : ℝ)) (alpha := (468507319291/374400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1961291759/10000000000 : ℝ)*X 0 0+(169026991/312500000 : ℝ)*X 0 1+(1311499991/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069479839/2000000000 : ℝ)*X 1 0+(-2044222341/10000000000 : ℝ)*X 1 1+(1311500043/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336849841/2500000000 : ℝ)*X 2 0+(131150003/250000000 : ℝ)*X 2 1+(-2044222183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150647827/5000000000 : ℝ)*X 0 0+(515951643/1250000000 : ℝ)*X 0 1+(4481491019/10000000000 : ℝ)*X 0 2+(2150647827/5000000000 : ℝ)*X 1 0+(515951643/1250000000 : ℝ)*X 1 1+(4481491019/10000000000 : ℝ)*X 1 2+(2150647827/5000000000 : ℝ)*X 2 0+(515951643/1250000000 : ℝ)*X 2 1+(4481491019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1961303609/10000000000 : ℝ)*X 0 0+(131164923/250000000 : ℝ)*X 0 1+(5408263531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652505059/5000000000 : ℝ)*X 1 0+(-376391773/2000000000 : ℝ)*X 1 1+(1352065877/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53050101/100000000 : ℝ)*X 2 0+(5408263537/10000000000 : ℝ)*X 2 1+(-37639177/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150660593/5000000000 : ℝ)*X 0 0+(4480194041/10000000000 : ℝ)*X 0 1+(516114613/1250000000 : ℝ)*X 0 2+(2150660593/5000000000 : ℝ)*X 1 0+(4480194041/10000000000 : ℝ)*X 1 1+(516114613/1250000000 : ℝ)*X 1 2+(2150660593/5000000000 : ℝ)*X 2 0+(4480194041/10000000000 : ℝ)*X 2 1+(516114613/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729842067086759232834060191/62400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1762361349/100000000000000 : ℝ)*(base19) + (836934727/50000000000000 : ℝ)*(base23) + (30217873/20000000000000 : ℝ)*(lower2) + (181556321/100000000000000 : ℝ)*(upper3) + (103619093/50000000000000 : ℝ)*(upper5) + (4483031710386389/100000000000000 : ℝ)*(major0) + (4483031710386389/100000000000000 : ℝ)*(major1) + (4483031710386389/100000000000000 : ℝ)*(major2) + (6140143687599497/100000000000000 : ℝ)*(sp0) + (767523780105297/12500000000000 : ℝ)*(sp1) + (6140190329334271/100000000000000 : ℝ)*(sp2) + (176615719043669/6250000000000 : ℝ)*(sp3) + (48315604227/100000000000000 : ℝ)*(sp4) + (19522997441/100000000000000 : ℝ)*(sp7) + (176616939231009/6250000000000 : ℝ)*(f.failure) + (245607680128149/4000000000000 : ℝ)*(f.sum) + (22939170260521/18720000000000000000000000000 : ℝ)*base66 + (299682625099109809/374400000000000000000000000000000 : ℝ)*base67 + (2074713952113509809/374400000000000000000000000000000 : ℝ)*base69 + (825410566315290191/374400000000000000000000000000000 : ℝ)*base72 + (68533139221321/18720000000000000000000000000 : ℝ)*base74 + (2711596422004709809/374400000000000000000000000000000 : ℝ)*base75 + (2227357478020890191/374400000000000000000000000000000 : ℝ)*base78 + (1738809276388709809/374400000000000000000000000000000 : ℝ)*base79 + (1746847397641/18720000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2986867/312500000000000000000 : ℝ)*base90 + (2986867/312500000000000000000 : ℝ)*base92 + (2986867/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (753983337840783307927438003/62400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3113819/160000000000 : ℝ)*(base19) + (2128341203/100000000000000 : ℝ)*(base23) + (232830251/100000000000000 : ℝ)*(upper3) + (92612341/100000000000000 : ℝ)*(lower4) + (254674407/100000000000000 : ℝ)*(upper5) + (4516161160745137/100000000000000 : ℝ)*(major0) + (4516161160745137/100000000000000 : ℝ)*(major1) + (4516161160745137/100000000000000 : ℝ)*(major2) + (1593847949/4000000000000 : ℝ)*(sp1) + (43427414879/100000000000000 : ℝ)*(sp2) + (6185567801192223/100000000000000 : ℝ)*(sp4) + (6185526008856623/100000000000000 : ℝ)*(sp5) + (309276112271807/5000000000000 : ℝ)*(sp6) + (1423377058764583/50000000000000 : ℝ)*(sp7) + (1423377058764583/50000000000000 : ℝ)*(f.failure) + (6185567801192223/100000000000000 : ℝ)*(f.sum) + (18249046913813/18720000000000000000000000000 : ℝ)*base66 + (3020273186121028003/374400000000000000000000000000000 : ℝ)*base68 + (2130127275360571997/374400000000000000000000000000000 : ℝ)*base69 + (898760386733371997/374400000000000000000000000000000 : ℝ)*base71 + (40737263424053/18720000000000000000000000000 : ℝ)*base74 + (78636078901828003/374400000000000000000000000000000 : ℝ)*base76 + (5678944934448571997/374400000000000000000000000000000 : ℝ)*base77 + (5355781337078971997/374400000000000000000000000000000 : ℝ)*base79 + (22282161177173/18720000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9650829/2500000000000000000000 : ℝ)*base90 + (9650829/2500000000000000000000 : ℝ)*base92 + (9650829/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1441_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1441_s5_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196141613/1000000000 : ℝ)*x 0 + (1351941751/2500000000 : ℝ)*x 1 + (5247014531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196141613/1000000000 : ℝ)^4401 ≤ (2393796767923/20000000000000 : ℝ)^3377 := by
    have hnat : (196141613 : ℕ)^4401*20000000000000^3377 ≤ 2393796767923^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196141613 1000000000 2393796767923 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351941751/2500000000 : ℝ)^4401 ≤ (44880906547569/100000000000000 : ℝ)^3377 := by
    have hnat : (1351941751 : ℕ)^4401*100000000000000^3377 ≤ 44880906547569^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351941751 2500000000 44880906547569 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247014531/10000000000 : ℝ)^4401 ≤ (10787527398689/25000000000000 : ℝ)^3377 := by
    have hnat : (5247014531 : ℕ)^4401*25000000000000^3377 ≤ 10787527398689^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247014531 10000000000 10787527398689 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196141613/1000000000 : ℝ), (1351941751/2500000000 : ℝ), (5247014531/10000000000 : ℝ)] ![(2393796767923/20000000000000 : ℝ), (44880906547569/100000000000000 : ℝ), (10787527398689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196141613/1000000000 : ℝ)|^4401 ≤ (2393796767923/20000000000000 : ℝ)^3377
        have hw : |(-196141613/1000000000 : ℝ)|=(196141613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351941751/2500000000 : ℝ)|^4401 ≤ (44880906547569/100000000000000 : ℝ)^3377
        have hw : |(1351941751/2500000000 : ℝ)|=(1351941751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247014531/10000000000 : ℝ)|^4401 ≤ (10787527398689/25000000000000 : ℝ)^3377
        have hw : |(5247014531/10000000000 : ℝ)|=(5247014531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347115189/10000000000 : ℝ)*x 0 + (-1021626239/5000000000 : ℝ)*x 1 + (1311753633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347115189/10000000000 : ℝ)^4401 ≤ (11056504763691/25000000000000 : ℝ)^3377 := by
    have hnat : (5347115189 : ℕ)^4401*25000000000000^3377 ≤ 11056504763691^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347115189 10000000000 11056504763691 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021626239/5000000000 : ℝ)^4401 ≤ (3155967832843/25000000000000 : ℝ)^3377 := by
    have hnat : (1021626239 : ℕ)^4401*25000000000000^3377 ≤ 3155967832843^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021626239 5000000000 3155967832843 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311753633/2500000000 : ℝ)^4401 ≤ (43150109605473/100000000000000 : ℝ)^3377 := by
    have hnat : (1311753633 : ℕ)^4401*100000000000000^3377 ≤ 43150109605473^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311753633 2500000000 43150109605473 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347115189/10000000000 : ℝ), (-1021626239/5000000000 : ℝ), (1311753633/2500000000 : ℝ)] ![(11056504763691/25000000000000 : ℝ), (3155967832843/25000000000000 : ℝ), (43150109605473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347115189/10000000000 : ℝ)|^4401 ≤ (11056504763691/25000000000000 : ℝ)^3377
        have hw : |(5347115189/10000000000 : ℝ)|=(5347115189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021626239/5000000000 : ℝ)|^4401 ≤ (3155967832843/25000000000000 : ℝ)^3377
        have hw : |(-1021626239/5000000000 : ℝ)|=(1021626239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311753633/2500000000 : ℝ)|^4401 ≤ (43150109605473/100000000000000 : ℝ)^3377
        have hw : |(1311753633/2500000000 : ℝ)|=(1311753633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347115189/10000000000 : ℝ)*x 0 + (5247014531/10000000000 : ℝ)*x 1 + (-1021626239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347115189/10000000000 : ℝ)^4401 ≤ (11056504763691/25000000000000 : ℝ)^3377 := by
    have hnat : (5347115189 : ℕ)^4401*25000000000000^3377 ≤ 11056504763691^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347115189 10000000000 11056504763691 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247014531/10000000000 : ℝ)^4401 ≤ (10787527398689/25000000000000 : ℝ)^3377 := by
    have hnat : (5247014531 : ℕ)^4401*25000000000000^3377 ≤ 10787527398689^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247014531 10000000000 10787527398689 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021626239/5000000000 : ℝ)^4401 ≤ (3155967832843/25000000000000 : ℝ)^3377 := by
    have hnat : (1021626239 : ℕ)^4401*25000000000000^3377 ≤ 3155967832843^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021626239 5000000000 3155967832843 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347115189/10000000000 : ℝ), (5247014531/10000000000 : ℝ), (-1021626239/5000000000 : ℝ)] ![(11056504763691/25000000000000 : ℝ), (10787527398689/25000000000000 : ℝ), (3155967832843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347115189/10000000000 : ℝ)|^4401 ≤ (11056504763691/25000000000000 : ℝ)^3377
        have hw : |(5347115189/10000000000 : ℝ)|=(5347115189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247014531/10000000000 : ℝ)|^4401 ≤ (10787527398689/25000000000000 : ℝ)^3377
        have hw : |(5247014531/10000000000 : ℝ)|=(5247014531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021626239/5000000000 : ℝ)|^4401 ≤ (3155967832843/25000000000000 : ℝ)^3377
        have hw : |(-1021626239/5000000000 : ℝ)|=(1021626239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150685241/5000000000 : ℝ)*x 0 + (2064948811/5000000000 : ℝ)*x 1 + (1119797137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150685241/5000000000 : ℝ)^4401 ≤ (33304758759159/100000000000000 : ℝ)^3377 := by
    have hnat : (2150685241 : ℕ)^4401*100000000000000^3377 ≤ 33304758759159^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150685241 5000000000 33304758759159 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064948811/5000000000 : ℝ)^4401 ≤ (6317008016323/20000000000000 : ℝ)^3377 := by
    have hnat : (2064948811 : ℕ)^4401*20000000000000^3377 ≤ 6317008016323^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064948811 5000000000 6317008016323 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119797137/2500000000 : ℝ)^4401 ≤ (3428730581/9765625000 : ℝ)^3377 := by
    have hnat : (1119797137 : ℕ)^4401*9765625000^3377 ≤ 3428730581^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119797137 2500000000 3428730581 9765625000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150685241/5000000000 : ℝ), (2064948811/5000000000 : ℝ), (1119797137/2500000000 : ℝ)] ![(33304758759159/100000000000000 : ℝ), (6317008016323/20000000000000 : ℝ), (3428730581/9765625000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150685241/5000000000 : ℝ)|^4401 ≤ (33304758759159/100000000000000 : ℝ)^3377
        have hw : |(2150685241/5000000000 : ℝ)|=(2150685241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064948811/5000000000 : ℝ)|^4401 ≤ (6317008016323/20000000000000 : ℝ)^3377
        have hw : |(2064948811/5000000000 : ℝ)|=(2064948811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119797137/2500000000 : ℝ)|^4401 ≤ (3428730581/9765625000 : ℝ)^3377
        have hw : |(1119797137/2500000000 : ℝ)|=(1119797137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98071371/500000000 : ℝ)*x 0 + (327974757/625000000 : ℝ)*x 1 + (5407182401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98071371/500000000 : ℝ)^4401 ≤ (299226840607/2500000000000 : ℝ)^3377 := by
    have hnat : (98071371 : ℕ)^4401*2500000000000^3377 ≤ 299226840607^3377*500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98071371 500000000 299226840607 2500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327974757/625000000 : ℝ)^4401 ≤ (1348635710717/3125000000000 : ℝ)^3377 := by
    have hnat : (327974757 : ℕ)^4401*3125000000000^3377 ≤ 1348635710717^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327974757 625000000 1348635710717 3125000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407182401/10000000000 : ℝ)^4401 ≤ (2804661476549/6250000000000 : ℝ)^3377 := by
    have hnat : (5407182401 : ℕ)^4401*6250000000000^3377 ≤ 2804661476549^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407182401 10000000000 2804661476549 6250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98071371/500000000 : ℝ), (327974757/625000000 : ℝ), (5407182401/10000000000 : ℝ)] ![(299226840607/2500000000000 : ℝ), (1348635710717/3125000000000 : ℝ), (2804661476549/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98071371/500000000 : ℝ)|^4401 ≤ (299226840607/2500000000000 : ℝ)^3377
        have hw : |(-98071371/500000000 : ℝ)|=(98071371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327974757/625000000 : ℝ)|^4401 ≤ (1348635710717/3125000000000 : ℝ)^3377
        have hw : |(327974757/625000000 : ℝ)|=(327974757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407182401/10000000000 : ℝ)|^4401 ≤ (2804661476549/6250000000000 : ℝ)^3377
        have hw : |(5407182401/10000000000 : ℝ)|=(5407182401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652637617/5000000000 : ℝ)*x 0 + (-1883084647/10000000000 : ℝ)*x 1 + (2703591209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652637617/5000000000 : ℝ)^4401 ≤ (43775562037813/100000000000000 : ℝ)^3377 := by
    have hnat : (2652637617 : ℕ)^4401*100000000000000^3377 ≤ 43775562037813^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652637617 5000000000 43775562037813 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1883084647/10000000000 : ℝ)^4401 ≤ (11349854142411/100000000000000 : ℝ)^3377 := by
    have hnat : (1883084647 : ℕ)^4401*100000000000000^3377 ≤ 11349854142411^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883084647 10000000000 11349854142411 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703591209/5000000000 : ℝ)^4401 ≤ (5609322976081/12500000000000 : ℝ)^3377 := by
    have hnat : (2703591209 : ℕ)^4401*12500000000000^3377 ≤ 5609322976081^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703591209 5000000000 5609322976081 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652637617/5000000000 : ℝ), (-1883084647/10000000000 : ℝ), (2703591209/5000000000 : ℝ)] ![(43775562037813/100000000000000 : ℝ), (11349854142411/100000000000000 : ℝ), (5609322976081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652637617/5000000000 : ℝ)|^4401 ≤ (43775562037813/100000000000000 : ℝ)^3377
        have hw : |(2652637617/5000000000 : ℝ)|=(2652637617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1883084647/10000000000 : ℝ)|^4401 ≤ (11349854142411/100000000000000 : ℝ)^3377
        have hw : |(-1883084647/10000000000 : ℝ)|=(1883084647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703591209/5000000000 : ℝ)|^4401 ≤ (5609322976081/12500000000000 : ℝ)^3377
        have hw : |(2703591209/5000000000 : ℝ)|=(2703591209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530527501/1000000000 : ℝ)*x 0 + (2703591303/5000000000 : ℝ)*x 1 + (-941542347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530527501/1000000000 : ℝ)^4401 ≤ (2188777981453/5000000000000 : ℝ)^3377 := by
    have hnat : (530527501 : ℕ)^4401*5000000000000^3377 ≤ 2188777981453^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530527501 1000000000 2188777981453 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703591303/5000000000 : ℝ)^4401 ≤ (44874585841977/100000000000000 : ℝ)^3377 := by
    have hnat : (2703591303 : ℕ)^4401*100000000000000^3377 ≤ 44874585841977^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703591303 5000000000 44874585841977 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941542347/5000000000 : ℝ)^4401 ≤ (11349854511591/100000000000000 : ℝ)^3377 := by
    have hnat : (941542347 : ℕ)^4401*100000000000000^3377 ≤ 11349854511591^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941542347 5000000000 11349854511591 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530527501/1000000000 : ℝ), (2703591303/5000000000 : ℝ), (-941542347/5000000000 : ℝ)] ![(2188777981453/5000000000000 : ℝ), (44874585841977/100000000000000 : ℝ), (11349854511591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530527501/1000000000 : ℝ)|^4401 ≤ (2188777981453/5000000000000 : ℝ)^3377
        have hw : |(530527501/1000000000 : ℝ)|=(530527501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703591303/5000000000 : ℝ)|^4401 ≤ (44874585841977/100000000000000 : ℝ)^3377
        have hw : |(2703591303/5000000000 : ℝ)|=(2703591303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941542347/5000000000 : ℝ)|^4401 ≤ (11349854511591/100000000000000 : ℝ)^3377
        have hw : |(-941542347/5000000000 : ℝ)|=(941542347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s5_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150697473/5000000000 : ℝ)*x 0 + (1119481251/2500000000 : ℝ)*x 1 + (129098993/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150697473/5000000000 : ℝ)^4401 ≤ (33305005617379/100000000000000 : ℝ)^3377 := by
    have hnat : (2150697473 : ℕ)^4401*100000000000000^3377 ≤ 33305005617379^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150697473 5000000000 33305005617379 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119481251/2500000000 : ℝ)^4401 ≤ (350972941267/1000000000000 : ℝ)^3377 := by
    have hnat : (1119481251 : ℕ)^4401*1000000000000^3377 ≤ 350972941267^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119481251 2500000000 350972941267 1000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129098993/312500000 : ℝ)^4401 ≤ (15798850119191/50000000000000 : ℝ)^3377 := by
    have hnat : (129098993 : ℕ)^4401*50000000000000^3377 ≤ 15798850119191^3377*312500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129098993 312500000 15798850119191 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150697473/5000000000 : ℝ), (1119481251/2500000000 : ℝ), (129098993/312500000 : ℝ)] ![(33305005617379/100000000000000 : ℝ), (350972941267/1000000000000 : ℝ), (15798850119191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150697473/5000000000 : ℝ)|^4401 ≤ (33305005617379/100000000000000 : ℝ)^3377
        have hw : |(2150697473/5000000000 : ℝ)|=(2150697473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119481251/2500000000 : ℝ)|^4401 ≤ (350972941267/1000000000000 : ℝ)^3377
        have hw : |(1119481251/2500000000 : ℝ)|=(1119481251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129098993/312500000 : ℝ)|^4401 ≤ (15798850119191/50000000000000 : ℝ)^3377
        have hw : |(129098993/312500000 : ℝ)|=(129098993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11339/100000 : ℝ) ^ (275/64 : ℝ) ≤ (8662154021856019/100000000000000000000 : ℝ) := by
    have hpowers : (11339/100000 : ℝ)^275 ≤ (8662154021856019/100000000000000000000 : ℝ)^64 := by
      have hnat : (11339 : ℕ)^275*100000000000000000000^64 ≤ 8662154021856019^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11339 100000 8662154021856019 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11339/100000 : ℝ)) (X := (8662154021856019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1479/10000 : ℝ) ^ (275/64 : ℝ) ≤ (27130450023955633/100000000000000000000 : ℝ) := by
    have hpowers : (1479/10000 : ℝ)^275 ≤ (27130450023955633/100000000000000000000 : ℝ)^64 := by
      have hnat : (1479 : ℕ)^275*100000000000000000000^64 ≤ 27130450023955633^64*10000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1479 10000 27130450023955633 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1479/10000 : ℝ)) (X := (27130450023955633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008662154021856019/50000000000000000000 : ℝ) ≤ (5000201578551239/5000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50008662154021856019/50000000000000000000 : ℝ)^64 ≤ (5000201578551239/5000000000000000 : ℝ)^275 := by
      have hnat : (50008662154021856019 : ℕ)^64*5000000000000000^275 ≤ 5000201578551239^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008662154021856019 50000000000000000000 5000201578551239 5000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000201578551239/5000000000000000 : ℝ)) (X := (50008662154021856019/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008948151011452913/25000000000000000000 : ℝ) ≤ (10000832877155517/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (25008948151011452913/25000000000000000000 : ℝ)^64 ≤ (10000832877155517/10000000000000000 : ℝ)^275 := by
      have hnat : (25008948151011452913 : ℕ)^64*10000000000000000^275 ≤ 10000832877155517^275*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008948151011452913 25000000000000000000 10000832877155517 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000832877155517/10000000000000000 : ℝ)) (X := (25008948151011452913/25000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027130450023955633/50000000000000000000 : ℝ) ≤ (2500315649302139/2500000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50027130450023955633/50000000000000000000 : ℝ)^64 ≤ (2500315649302139/2500000000000000 : ℝ)^275 := by
      have hnat : (50027130450023955633 : ℕ)^64*2500000000000000^275 ≤ 2500315649302139^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027130450023955633 50000000000000000000 2500315649302139 2500000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500315649302139/2500000000000000 : ℝ)) (X := (50027130450023955633/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8662154021856019/100000000000000000000 : ℝ) ≤ ((4373940936079847/4375000000000000 : ℝ)+2*(429720053039/345100000000000 : ℝ)*(11339/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (4373940936079847/4375000000000000 : ℝ)+2*(429720053039/345100000000000 : ℝ)*(11339/100000 : ℝ)=(5000201578551239/5000000000000000 : ℝ) by norm_num, show 1+2*(8662154021856019/100000000000000000000 : ℝ)=(50008662154021856019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27130450023955633/100000000000000000000 : ℝ)+(8662154021856019/100000000000000000000 : ℝ) ≤ ((4373940936079847/4375000000000000 : ℝ)+(429720053039/345100000000000 : ℝ)*((1479/10000 : ℝ)+(11339/100000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (4373940936079847/4375000000000000 : ℝ)+(429720053039/345100000000000 : ℝ)*((1479/10000 : ℝ)+(11339/100000 : ℝ))=(10000832877155517/10000000000000000 : ℝ) by norm_num, show 1+(27130450023955633/100000000000000000000 : ℝ)+(8662154021856019/100000000000000000000 : ℝ)=(25008948151011452913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27130450023955633/100000000000000000000 : ℝ) ≤ ((4373940936079847/4375000000000000 : ℝ)+2*(429720053039/345100000000000 : ℝ)*(1479/10000 : ℝ))^(275/64 : ℝ) := by
    rw [show (4373940936079847/4375000000000000 : ℝ)+2*(429720053039/345100000000000 : ℝ)*(1479/10000 : ℝ)=(2500315649302139/2500000000000000 : ℝ) by norm_num, show 1+2*(27130450023955633/100000000000000000000 : ℝ)=(50027130450023955633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4373940936079847/4375000000000000 : ℝ)*(X 1 0+X 2 0)+(429720053039/345100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (4373940936079847/4375000000000000 : ℝ)) (alpha := (429720053039/345100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4373940936079847/4375000000000000 : ℝ)*(X 0 1+X 2 1)+(429720053039/345100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (4373940936079847/4375000000000000 : ℝ)) (alpha := (429720053039/345100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4373940936079847/4375000000000000 : ℝ)*(X 0 2+X 1 2)+(429720053039/345100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (4373940936079847/4375000000000000 : ℝ)) (alpha := (429720053039/345100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196141613/1000000000 : ℝ)*X 0 0+(1351941751/2500000000 : ℝ)*X 0 1+(5247014531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347115189/10000000000 : ℝ)*X 1 0+(-1021626239/5000000000 : ℝ)*X 1 1+(1311753633/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347115189/10000000000 : ℝ)*X 2 0+(5247014531/10000000000 : ℝ)*X 2 1+(-1021626239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150685241/5000000000 : ℝ)*X 0 0+(2064948811/5000000000 : ℝ)*X 0 1+(1119797137/2500000000 : ℝ)*X 0 2+(2150685241/5000000000 : ℝ)*X 1 0+(2064948811/5000000000 : ℝ)*X 1 1+(1119797137/2500000000 : ℝ)*X 1 2+(2150685241/5000000000 : ℝ)*X 2 0+(2064948811/5000000000 : ℝ)*X 2 1+(1119797137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98071371/500000000 : ℝ)*X 0 0+(327974757/625000000 : ℝ)*X 0 1+(5407182401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652637617/5000000000 : ℝ)*X 1 0+(-1883084647/10000000000 : ℝ)*X 1 1+(2703591209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530527501/1000000000 : ℝ)*X 2 0+(2703591303/5000000000 : ℝ)*X 2 1+(-941542347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150697473/5000000000 : ℝ)*X 0 0+(1119481251/2500000000 : ℝ)*X 0 1+(129098993/312500000 : ℝ)*X 0 2+(2150697473/5000000000 : ℝ)*X 1 0+(1119481251/2500000000 : ℝ)*X 1 1+(129098993/312500000 : ℝ)*X 1 2+(2150697473/5000000000 : ℝ)*X 2 0+(1119481251/2500000000 : ℝ)*X 2 1+(129098993/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (815243892814218701881152801/107843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1371102441/100000000000000 : ℝ)*(base19) + (639013413/50000000000000 : ℝ)*(base23) + (49768603/100000000000000 : ℝ)*(lower2) + (94408349/50000000000000 : ℝ)*(upper3) + (60236761/50000000000000 : ℝ)*(upper5) + (4541886886896377/100000000000000 : ℝ)*(major0) + (4541886886896377/100000000000000 : ℝ)*(major1) + (4541886886896377/100000000000000 : ℝ)*(major2) + (6220774301108937/100000000000000 : ℝ)*(sp0) + (3110400933834603/50000000000000 : ℝ)*(sp1) + (311040098037241/5000000000000 : ℝ)*(sp2) + (1431477933305367/50000000000000 : ℝ)*(sp3) + (28937662709/100000000000000 : ℝ)*(sp4) + (3604106831/25000000000000 : ℝ)*(sp7) + (1431485141519029/50000000000000 : ℝ)*(f.failure) + (3110401619385823/50000000000000 : ℝ)*(f.sum) + (58003066038307/17255000000000000000000000000 : ℝ)*base66 + (344505333506600431/30812500000000000000000000000000 : ℝ)*base67 + (67976905456899569/30812500000000000000000000000000 : ℝ)*base70 + (86984973832024569/30812500000000000000000000000000 : ℝ)*base72 + (82368293753177/17255000000000000000000000000 : ℝ)*base74 + (278092079947399569/30812500000000000000000000000000 : ℝ)*base76 + (66799737311899569/30812500000000000000000000000000 : ℝ)*base78 + (39798140309600431/30812500000000000000000000000000 : ℝ)*base79 + (87196765924777/17255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14318873/2500000000000000000000 : ℝ)*base89 + (14318873/2500000000000000000000 : ℝ)*base91 + (14318873/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (212884324872380227097757/17255000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1806658277/100000000000000 : ℝ)*(base19) + (166890369/10000000000000 : ℝ)*(base23) + (138194259/50000000000000 : ℝ)*(upper3) + (30775267/50000000000000 : ℝ)*(lower4) + (6741239/3125000000000 : ℝ)*(upper5) + (1143757323361109/25000000000000 : ℝ)*(major0) + (1143757323361109/25000000000000 : ℝ)*(major1) + (1143757323361109/25000000000000 : ℝ)*(major2) + (35214874903/100000000000000 : ℝ)*(sp1) + (36584095767/100000000000000 : ℝ)*(sp2) + (1253239327171107/20000000000000 : ℝ)*(sp4) + (1253231922864471/20000000000000 : ℝ)*(sp5) + (3133079191428039/50000000000000 : ℝ)*(sp6) + (144193076989093/5000000000000 : ℝ)*(sp7) + (144193076989093/5000000000000 : ℝ)*(f.failure) + (1253239327171107/20000000000000 : ℝ)*(f.sum) + (573123800419/1078437500000000000000000000 : ℝ)*base65 + (45280709355705427/7703125000000000000000000000000 : ℝ)*base67 + (2914525078105181/962890625000000000000000000000 : ℝ)*base70 + (659402813873849/3851562500000000000000000000000 : ℝ)*base72 + (103622059066851/17255000000000000000000000000 : ℝ)*base74 + (29735180801049177/7703125000000000000000000000000 : ℝ)*base75 + (63461952425257/120361328125000000000000000000 : ℝ)*base78 + (17834029794063651/3851562500000000000000000000000 : ℝ)*base79 + (75339330503253/8627500000000000000000000000 : ℝ)*base82 + (2268041/250000000000000000000 : ℝ)*base89 + (2268041/250000000000000000000 : ℝ)*base91 + (2268041/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1441_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1441_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1441_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1441_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1441_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1441_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

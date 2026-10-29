-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1445_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:10.592983+00:00
-- url     : https://prove2.me/submissions/810093b8-5cb6-4177-8c18-bc8c5aad06a6

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
theorem support_rectangle_w1445_s6_0 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61194463/312500000 : ℝ)*x 0 + (5407395761/10000000000 : ℝ)*x 1 + (5247250789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61194463/312500000 : ℝ)^4405 ≤ (1493822932819/12500000000000 : ℝ)^3381 := by
    have hnat : (61194463 : ℕ)^4405*12500000000000^3381 ≤ 1493822932819^3381*312500000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61194463 312500000 1493822932819 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407395761/10000000000 : ℝ)^4405 ≤ (44886790461451/100000000000000 : ℝ)^3381 := by
    have hnat : (5407395761 : ℕ)^4405*100000000000000^3381 ≤ 44886790461451^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407395761 10000000000 44886790461451 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247250789/10000000000 : ℝ)^4405 ≤ (21581313029727/50000000000000 : ℝ)^3381 := by
    have hnat : (5247250789 : ℕ)^4405*50000000000000^3381 ≤ 21581313029727^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247250789 10000000000 21581313029727 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61194463/312500000 : ℝ), (5407395761/10000000000 : ℝ), (5247250789/10000000000 : ℝ)] ![(1493822932819/12500000000000 : ℝ), (44886790461451/100000000000000 : ℝ), (21581313029727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61194463/312500000 : ℝ)|^4405 ≤ (1493822932819/12500000000000 : ℝ)^3381
        have hw : |(-61194463/312500000 : ℝ)|=(61194463/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407395761/10000000000 : ℝ)|^4405 ≤ (44886790461451/100000000000000 : ℝ)^3381
        have hw : |(5407395761/10000000000 : ℝ)|=(5407395761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247250789/10000000000 : ℝ)|^4405 ≤ (21581313029727/50000000000000 : ℝ)^3381
        have hw : |(5247250789/10000000000 : ℝ)|=(5247250789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_1 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346985639/10000000000 : ℝ)*x 0 + (-40794887/200000000 : ℝ)*x 1 + (2623625397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346985639/10000000000 : ℝ)^4405 ≤ (1382329882819/3125000000000 : ℝ)^3381 := by
    have hnat : (5346985639 : ℕ)^4405*3125000000000^3381 ≤ 1382329882819^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346985639 10000000000 1382329882819 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40794887/200000000 : ℝ)^4405 ≤ (12602817619303/100000000000000 : ℝ)^3381 := by
    have hnat : (40794887 : ℕ)^4405*100000000000000^3381 ≤ 12602817619303^3381*200000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40794887 200000000 12602817619303 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623625397/5000000000 : ℝ)^4405 ≤ (539532826413/1250000000000 : ℝ)^3381 := by
    have hnat : (2623625397 : ℕ)^4405*1250000000000^3381 ≤ 539532826413^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623625397 5000000000 539532826413 1250000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346985639/10000000000 : ℝ), (-40794887/200000000 : ℝ), (2623625397/5000000000 : ℝ)] ![(1382329882819/3125000000000 : ℝ), (12602817619303/100000000000000 : ℝ), (539532826413/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346985639/10000000000 : ℝ)|^4405 ≤ (1382329882819/3125000000000 : ℝ)^3381
        have hw : |(5346985639/10000000000 : ℝ)|=(5346985639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40794887/200000000 : ℝ)|^4405 ≤ (12602817619303/100000000000000 : ℝ)^3381
        have hw : |(-40794887/200000000 : ℝ)|=(40794887/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623625397/5000000000 : ℝ)|^4405 ≤ (539532826413/1250000000000 : ℝ)^3381
        have hw : |(2623625397/5000000000 : ℝ)|=(2623625397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_2 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346985637/10000000000 : ℝ)*x 0 + (655906349/1250000000 : ℝ)*x 1 + (-407948871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346985637/10000000000 : ℝ)^4405 ≤ (44234556228651/100000000000000 : ℝ)^3381 := by
    have hnat : (5346985637 : ℕ)^4405*100000000000000^3381 ≤ 44234556228651^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346985637 10000000000 44234556228651 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655906349/1250000000 : ℝ)^4405 ≤ (21581313045803/50000000000000 : ℝ)^3381 := by
    have hnat : (655906349 : ℕ)^4405*50000000000000^3381 ≤ 21581313045803^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655906349 1250000000 21581313045803 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407948871/2000000000 : ℝ)^4405 ≤ (393838051861/3125000000000 : ℝ)^3381 := by
    have hnat : (407948871 : ℕ)^4405*3125000000000^3381 ≤ 393838051861^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407948871 2000000000 393838051861 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346985637/10000000000 : ℝ), (655906349/1250000000 : ℝ), (-407948871/2000000000 : ℝ)] ![(44234556228651/100000000000000 : ℝ), (21581313045803/50000000000000 : ℝ), (393838051861/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346985637/10000000000 : ℝ)|^4405 ≤ (44234556228651/100000000000000 : ℝ)^3381
        have hw : |(5346985637/10000000000 : ℝ)|=(5346985637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655906349/1250000000 : ℝ)|^4405 ≤ (21581313045803/50000000000000 : ℝ)^3381
        have hw : |(655906349/1250000000 : ℝ)|=(655906349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407948871/2000000000 : ℝ)|^4405 ≤ (393838051861/3125000000000 : ℝ)^3381
        have hw : |(-407948871/2000000000 : ℝ)|=(407948871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_3 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075097121/2500000000 : ℝ)*x 0 + (4129302101/10000000000 : ℝ)*x 1 + (2238890597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075097121/2500000000 : ℝ)^4405 ≤ (33304931170519/100000000000000 : ℝ)^3381 := by
    have hnat : (1075097121 : ℕ)^4405*100000000000000^3381 ≤ 33304931170519^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075097121 2500000000 33304931170519 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129302101/10000000000 : ℝ)^4405 ≤ (6317825264297/20000000000000 : ℝ)^3381 := by
    have hnat : (4129302101 : ℕ)^4405*20000000000000^3381 ≤ 6317825264297^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129302101 10000000000 6317825264297 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238890597/5000000000 : ℝ)^4405 ≤ (35105942486873/100000000000000 : ℝ)^3381 := by
    have hnat : (2238890597 : ℕ)^4405*100000000000000^3381 ≤ 35105942486873^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238890597 5000000000 35105942486873 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075097121/2500000000 : ℝ), (4129302101/10000000000 : ℝ), (2238890597/5000000000 : ℝ)] ![(33304931170519/100000000000000 : ℝ), (6317825264297/20000000000000 : ℝ), (35105942486873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075097121/2500000000 : ℝ)|^4405 ≤ (33304931170519/100000000000000 : ℝ)^3381
        have hw : |(1075097121/2500000000 : ℝ)|=(1075097121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129302101/10000000000 : ℝ)|^4405 ≤ (6317825264297/20000000000000 : ℝ)^3381
        have hw : |(4129302101/10000000000 : ℝ)|=(4129302101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238890597/5000000000 : ℝ)|^4405 ≤ (35105942486873/100000000000000 : ℝ)^3381
        have hw : |(2238890597/5000000000 : ℝ)|=(2238890597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_4 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1958233941/10000000000 : ℝ)*x 0 + (5247829249/10000000000 : ℝ)*x 1 + (5406814347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958233941/10000000000 : ℝ)^4405 ≤ (2987667979681/25000000000000 : ℝ)^3381 := by
    have hnat : (1958233941 : ℕ)^4405*25000000000000^3381 ≤ 2987667979681^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958233941 10000000000 2987667979681 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247829249/10000000000 : ℝ)^4405 ≤ (21584412784717/50000000000000 : ℝ)^3381 := by
    have hnat : (5247829249 : ℕ)^4405*50000000000000^3381 ≤ 21584412784717^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247829249 10000000000 21584412784717 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406814347/10000000000 : ℝ)^4405 ≤ (1402515703269/3125000000000 : ℝ)^3381 := by
    have hnat : (5406814347 : ℕ)^4405*3125000000000^3381 ≤ 1402515703269^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406814347 10000000000 1402515703269 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1958233941/10000000000 : ℝ), (5247829249/10000000000 : ℝ), (5406814347/10000000000 : ℝ)] ![(2987667979681/25000000000000 : ℝ), (21584412784717/50000000000000 : ℝ), (1402515703269/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1958233941/10000000000 : ℝ)|^4405 ≤ (2987667979681/25000000000000 : ℝ)^3381
        have hw : |(-1958233941/10000000000 : ℝ)|=(1958233941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247829249/10000000000 : ℝ)|^4405 ≤ (21584412784717/50000000000000 : ℝ)^3381
        have hw : |(5247829249/10000000000 : ℝ)|=(5247829249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406814347/10000000000 : ℝ)|^4405 ≤ (1402515703269/3125000000000 : ℝ)^3381
        have hw : |(5406814347/10000000000 : ℝ)|=(5406814347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_5 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305288009/10000000000 : ℝ)*x 0 + (-188018073/1000000000 : ℝ)*x 1 + (675851791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305288009/10000000000 : ℝ)^4405 ≤ (10946413790301/25000000000000 : ℝ)^3381 := by
    have hnat : (5305288009 : ℕ)^4405*25000000000000^3381 ≤ 10946413790301^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305288009 10000000000 10946413790301 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188018073/1000000000 : ℝ)^4405 ≤ (1416730315797/12500000000000 : ℝ)^3381 := by
    have hnat : (188018073 : ℕ)^4405*12500000000000^3381 ≤ 1416730315797^3381*1000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188018073 1000000000 1416730315797 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675851791/1250000000 : ℝ)^4405 ≤ (44880502299127/100000000000000 : ℝ)^3381 := by
    have hnat : (675851791 : ℕ)^4405*100000000000000^3381 ≤ 44880502299127^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675851791 1250000000 44880502299127 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305288009/10000000000 : ℝ), (-188018073/1000000000 : ℝ), (675851791/1250000000 : ℝ)] ![(10946413790301/25000000000000 : ℝ), (1416730315797/12500000000000 : ℝ), (44880502299127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305288009/10000000000 : ℝ)|^4405 ≤ (10946413790301/25000000000000 : ℝ)^3381
        have hw : |(5305288009/10000000000 : ℝ)|=(5305288009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188018073/1000000000 : ℝ)|^4405 ≤ (1416730315797/12500000000000 : ℝ)^3381
        have hw : |(-188018073/1000000000 : ℝ)|=(188018073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675851791/1250000000 : ℝ)|^4405 ≤ (44880502299127/100000000000000 : ℝ)^3381
        have hw : |(675851791/1250000000 : ℝ)|=(675851791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_6 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061057583/2000000000 : ℝ)*x 0 + (5406814387/10000000000 : ℝ)*x 1 + (-1880180777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061057583/2000000000 : ℝ)^4405 ≤ (10946413537609/25000000000000 : ℝ)^3381 := by
    have hnat : (1061057583 : ℕ)^4405*25000000000000^3381 ≤ 10946413537609^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061057583 2000000000 10946413537609 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406814387/10000000000 : ℝ)^4405 ≤ (22440251468599/50000000000000 : ℝ)^3381 := by
    have hnat : (5406814387 : ℕ)^4405*50000000000000^3381 ≤ 22440251468599^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406814387 10000000000 22440251468599 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1880180777/10000000000 : ℝ)^4405 ≤ (11333842895503/100000000000000 : ℝ)^3381 := by
    have hnat : (1880180777 : ℕ)^4405*100000000000000^3381 ≤ 11333842895503^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880180777 10000000000 11333842895503 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061057583/2000000000 : ℝ), (5406814387/10000000000 : ℝ), (-1880180777/10000000000 : ℝ)] ![(10946413537609/25000000000000 : ℝ), (22440251468599/50000000000000 : ℝ), (11333842895503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061057583/2000000000 : ℝ)|^4405 ≤ (10946413537609/25000000000000 : ℝ)^3381
        have hw : |(1061057583/2000000000 : ℝ)|=(1061057583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406814387/10000000000 : ℝ)|^4405 ≤ (22440251468599/50000000000000 : ℝ)^3381
        have hw : |(5406814387/10000000000 : ℝ)|=(5406814387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1880180777/10000000000 : ℝ)|^4405 ≤ (11333842895503/100000000000000 : ℝ)^3381
        have hw : |(-1880180777/10000000000 : ℝ)|=(1880180777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s6_7 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300412789/10000000000 : ℝ)*x 0 + (4476522439/10000000000 : ℝ)*x 1 + (2065283703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300412789/10000000000 : ℝ)^4405 ≤ (16652588207033/50000000000000 : ℝ)^3381 := by
    have hnat : (4300412789 : ℕ)^4405*50000000000000^3381 ≤ 16652588207033^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300412789 10000000000 16652588207033 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476522439/10000000000 : ℝ)^4405 ≤ (17546542719957/50000000000000 : ℝ)^3381 := by
    have hnat : (4476522439 : ℕ)^4405*50000000000000^3381 ≤ 17546542719957^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476522439 10000000000 17546542719957 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065283703/5000000000 : ℝ)^4405 ≤ (31601738121459/100000000000000 : ℝ)^3381 := by
    have hnat : (2065283703 : ℕ)^4405*100000000000000^3381 ≤ 31601738121459^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065283703 5000000000 31601738121459 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300412789/10000000000 : ℝ), (4476522439/10000000000 : ℝ), (2065283703/5000000000 : ℝ)] ![(16652588207033/50000000000000 : ℝ), (17546542719957/50000000000000 : ℝ), (31601738121459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300412789/10000000000 : ℝ)|^4405 ≤ (16652588207033/50000000000000 : ℝ)^3381
        have hw : |(4300412789/10000000000 : ℝ)|=(4300412789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476522439/10000000000 : ℝ)|^4405 ≤ (17546542719957/50000000000000 : ℝ)^3381
        have hw : |(4476522439/10000000000 : ℝ)|=(4476522439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065283703/5000000000 : ℝ)|^4405 ≤ (31601738121459/100000000000000 : ℝ)^3381
        have hw : |(2065283703/5000000000 : ℝ)|=(2065283703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1445_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2843/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11369/100000 : ℝ) ^ (1101/256 : ℝ) ≤ (8686964143232433/100000000000000000000 : ℝ) := by
    have hpowers : (11369/100000 : ℝ)^1101 ≤ (8686964143232433/100000000000000000000 : ℝ)^256 := by
      have hnat : (11369 : ℕ)^1101*100000000000000000000^256 ≤ 8686964143232433^256*100000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11369 100000 8686964143232433 100000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11369/100000 : ℝ)) (X := (8686964143232433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (1101/256 : ℝ) ≤ (3344600769947229/12500000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^1101 ≤ (3344600769947229/12500000000000000000 : ℝ)^256 := by
      have hnat : (923 : ℕ)^1101*12500000000000000000^256 ≤ 3344600769947229^256*6250^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 3344600769947229 12500000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (3344600769947229/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008686964143232433/50000000000000000000 : ℝ) ≤ (2000080788903489/2000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50008686964143232433/50000000000000000000 : ℝ)^256 ≤ (2000080788903489/2000000000000000 : ℝ)^1101 := by
      have hnat : (50008686964143232433 : ℕ)^256*2000000000000000^1101 ≤ 2000080788903489^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008686964143232433 50000000000000000000 2000080788903489 2000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000080788903489/2000000000000000 : ℝ)) (X := (50008686964143232433/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007088754060562053/20000000000000000000 : ℝ) ≤ (10000824011928253/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (20007088754060562053/20000000000000000000 : ℝ)^256 ≤ (10000824011928253/10000000000000000 : ℝ)^1101 := by
      have hnat : (20007088754060562053 : ℕ)^256*10000000000000000^1101 ≤ 10000824011928253^1101*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007088754060562053 20000000000000000000 10000824011928253 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000824011928253/10000000000000000 : ℝ)) (X := (20007088754060562053/20000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253344600769947229/6250000000000000000 : ℝ) ≤ (10001244079339061/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (6253344600769947229/6250000000000000000 : ℝ)^256 ≤ (10001244079339061/10000000000000000 : ℝ)^1101 := by
      have hnat : (6253344600769947229 : ℕ)^256*10000000000000000^1101 ≤ 10001244079339061^1101*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253344600769947229 6250000000000000000 10001244079339061 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001244079339061/10000000000000000 : ℝ)) (X := (6253344600769947229/6250000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8686964143232433/100000000000000000000 : ℝ) ≤ ((33981821514627843251/33990000000000000000 : ℝ)+2*(52508426351/42487500000000 : ℝ)*(11369/100000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (33981821514627843251/33990000000000000000 : ℝ)+2*(52508426351/42487500000000 : ℝ)*(11369/100000 : ℝ)=(2000080788903489/2000000000000000 : ℝ) by norm_num, show 1+2*(8686964143232433/100000000000000000000 : ℝ)=(50008686964143232433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3344600769947229/12500000000000000000 : ℝ)+(8686964143232433/100000000000000000000 : ℝ) ≤ ((33981821514627843251/33990000000000000000 : ℝ)+(52508426351/42487500000000 : ℝ)*((923/6250 : ℝ)+(11369/100000 : ℝ)))^(1101/256 : ℝ) := by
    rw [show (33981821514627843251/33990000000000000000 : ℝ)+(52508426351/42487500000000 : ℝ)*((923/6250 : ℝ)+(11369/100000 : ℝ))=(10000824011928253/10000000000000000 : ℝ) by norm_num, show 1+(3344600769947229/12500000000000000000 : ℝ)+(8686964143232433/100000000000000000000 : ℝ)=(20007088754060562053/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3344600769947229/12500000000000000000 : ℝ) ≤ ((33981821514627843251/33990000000000000000 : ℝ)+2*(52508426351/42487500000000 : ℝ)*(923/6250 : ℝ))^(1101/256 : ℝ) := by
    rw [show (33981821514627843251/33990000000000000000 : ℝ)+2*(52508426351/42487500000000 : ℝ)*(923/6250 : ℝ)=(10001244079339061/10000000000000000 : ℝ) by norm_num, show 1+2*(3344600769947229/12500000000000000000 : ℝ)=(6253344600769947229/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33981821514627843251/33990000000000000000 : ℝ)*(X 1 0+X 2 0)+(52508426351/42487500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (33981821514627843251/33990000000000000000 : ℝ)) (alpha := (52508426351/42487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33981821514627843251/33990000000000000000 : ℝ)*(X 0 1+X 2 1)+(52508426351/42487500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (33981821514627843251/33990000000000000000 : ℝ)) (alpha := (52508426351/42487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33981821514627843251/33990000000000000000 : ℝ)*(X 0 2+X 1 2)+(52508426351/42487500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (33981821514627843251/33990000000000000000 : ℝ)) (alpha := (52508426351/42487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-61194463/312500000 : ℝ)*X 0 0+(5407395761/10000000000 : ℝ)*X 0 1+(5247250789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346985639/10000000000 : ℝ)*X 1 0+(-40794887/200000000 : ℝ)*X 1 1+(2623625397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346985637/10000000000 : ℝ)*X 2 0+(655906349/1250000000 : ℝ)*X 2 1+(-407948871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075097121/2500000000 : ℝ)*X 0 0+(4129302101/10000000000 : ℝ)*X 0 1+(2238890597/5000000000 : ℝ)*X 0 2+(1075097121/2500000000 : ℝ)*X 1 0+(4129302101/10000000000 : ℝ)*X 1 1+(2238890597/5000000000 : ℝ)*X 1 2+(1075097121/2500000000 : ℝ)*X 2 0+(4129302101/10000000000 : ℝ)*X 2 1+(2238890597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1958233941/10000000000 : ℝ)*X 0 0+(5247829249/10000000000 : ℝ)*X 0 1+(5406814347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305288009/10000000000 : ℝ)*X 1 0+(-188018073/1000000000 : ℝ)*X 1 1+(675851791/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061057583/2000000000 : ℝ)*X 2 0+(5406814387/10000000000 : ℝ)*X 2 1+(-1880180777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300412789/10000000000 : ℝ)*X 0 0+(4476522439/10000000000 : ℝ)*X 0 1+(2065283703/5000000000 : ℝ)*X 0 2+(4300412789/10000000000 : ℝ)*X 1 0+(4476522439/10000000000 : ℝ)*X 1 1+(2065283703/5000000000 : ℝ)*X 1 2+(4300412789/10000000000 : ℝ)*X 2 0+(4476522439/10000000000 : ℝ)*X 2 1+(2065283703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14379276990725968616033229/1416250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (916801169/50000000000000 : ℝ)*(base19) + (852727321/50000000000000 : ℝ)*(base23) + (13454301/20000000000000 : ℝ)*(lower2) + (257251263/100000000000000 : ℝ)*(upper3) + (4967807/3125000000000 : ℝ)*(upper5) + (22785177483979/500000000000 : ℝ)*(major0) + (22785177483979/500000000000 : ℝ)*(major1) + (22785177483979/500000000000 : ℝ)*(major2) + (6244382822416469/100000000000000 : ℝ)*(sp0) + (6244419677858227/100000000000000 : ℝ)*(sp1) + (1561104951501481/25000000000000 : ℝ)*(sp2) + (358703727141187/12500000000000 : ℝ)*(sp3) + (38689044097/100000000000000 : ℝ)*(sp4) + (9663283031/50000000000000 : ℝ)*(sp7) + (1434824571847779/50000000000000 : ℝ)*(f.failure) + (1248884302292113/20000000000000 : ℝ)*(f.sum) + (24788779164119/3399000000000000000000000000 : ℝ)*base66 + (64889944808714757/5665000000000000000000000000000 : ℝ)*base68 + (1679646622514757/5665000000000000000000000000000 : ℝ)*base70 + (13388725416949757/5665000000000000000000000000000 : ℝ)*base72 + (428974685429/53109375000000000000000000 : ℝ)*base74 + (17450613459715243/5665000000000000000000000000000 : ℝ)*base75 + (46913694262724757/5665000000000000000000000000000 : ℝ)*base78 + (23711687184804757/5665000000000000000000000000000 : ℝ)*base80 + (424721520343/424875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (33986251/2500000000000000000000 : ℝ)*base89 + (33986251/2500000000000000000000 : ℝ)*base91 + (33986251/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1745530398194140837771549681/283250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1046286529/100000000000000 : ℝ)*(base19) + (1057782433/100000000000000 : ℝ)*(base23) + (371280949/100000000000000 : ℝ)*(lower1) + (16432299/20000000000000 : ℝ)*(upper3) + (69192063/100000000000000 : ℝ)*(lower4) + (7884529/6250000000000 : ℝ)*(upper5) + (2295102600016069/50000000000000 : ℝ)*(major0) + (2295102600016069/50000000000000 : ℝ)*(major1) + (2295102600016069/50000000000000 : ℝ)*(major2) + (475848887/50000000000000 : ℝ)*(sp1) + (3144936739098131/50000000000000 : ℝ)*(sp4) + (3144935740105979/50000000000000 : ℝ)*(sp5) + (6289872420413829/100000000000000 : ℝ)*(sp6) + (1445268358225537/50000000000000 : ℝ)*(sp7) + (1445268358225537/50000000000000 : ℝ)*(f.failure) + (3144936739098131/50000000000000 : ℝ)*(f.sum) + (9890761129069/4248750000000000000000000000 : ℝ)*base66 + (2664632179216533227/566500000000000000000000000000000 : ℝ)*base68 + (714966196222466773/566500000000000000000000000000000 : ℝ)*base69 + (1206915002428466773/566500000000000000000000000000000 : ℝ)*base71 + (57346814809133/8497500000000000000000000000 : ℝ)*base74 + (5135084788133466773/566500000000000000000000000000000 : ℝ)*base75 + (1336951733317033227/566500000000000000000000000000000 : ℝ)*base78 + (5467537304380966773/566500000000000000000000000000000 : ℝ)*base79 + (45876393705059/16995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (18130553/2500000000000000000000 : ℝ)*base89 + (18130553/2500000000000000000000 : ℝ)*base91 + (18130553/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1445_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1445_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1445_s7_0 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1958226081/10000000000 : ℝ)*x 0 + (5407374669/10000000000 : ℝ)*x 1 + (5247269651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958226081/10000000000 : ℝ)^4405 ≤ (2987652355733/25000000000000 : ℝ)^3381 := by
    have hnat : (1958226081 : ℕ)^4405*25000000000000^3381 ≤ 2987652355733^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958226081 10000000000 2987652355733 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407374669/10000000000 : ℝ)^4405 ≤ (44886562349181/100000000000000 : ℝ)^3381 := by
    have hnat : (5407374669 : ℕ)^4405*100000000000000^3381 ≤ 44886562349181^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407374669 10000000000 44886562349181 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247269651/10000000000 : ℝ)^4405 ≤ (43162828205271/100000000000000 : ℝ)^3381 := by
    have hnat : (5247269651 : ℕ)^4405*100000000000000^3381 ≤ 43162828205271^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247269651 10000000000 43162828205271 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1958226081/10000000000 : ℝ), (5407374669/10000000000 : ℝ), (5247269651/10000000000 : ℝ)] ![(2987652355733/25000000000000 : ℝ), (44886562349181/100000000000000 : ℝ), (43162828205271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1958226081/10000000000 : ℝ)|^4405 ≤ (2987652355733/25000000000000 : ℝ)^3381
        have hw : |(-1958226081/10000000000 : ℝ)|=(1958226081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407374669/10000000000 : ℝ)|^4405 ≤ (44886562349181/100000000000000 : ℝ)^3381
        have hw : |(5407374669/10000000000 : ℝ)|=(5407374669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247269651/10000000000 : ℝ)|^4405 ≤ (43162828205271/100000000000000 : ℝ)^3381
        have hw : |(5247269651/10000000000 : ℝ)|=(5247269651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s7_1 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855517/1600000 : ℝ)*x 0 + (-2039725983/10000000000 : ℝ)*x 1 + (1049453801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855517/1600000 : ℝ)^4405 ≤ (22117254471957/50000000000000 : ℝ)^3381 := by
    have hnat : (855517 : ℕ)^4405*50000000000000^3381 ≤ 22117254471957^3381*1600000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855517 1600000 22117254471957 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039725983/10000000000 : ℝ)^4405 ≤ (3150667441563/25000000000000 : ℝ)^3381 := by
    have hnat : (2039725983 : ℕ)^4405*25000000000000^3381 ≤ 3150667441563^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039725983 10000000000 3150667441563 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049453801/2000000000 : ℝ)^4405 ≤ (1726512851281/4000000000000 : ℝ)^3381 := by
    have hnat : (1049453801 : ℕ)^4405*4000000000000^3381 ≤ 1726512851281^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049453801 2000000000 1726512851281 4000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855517/1600000 : ℝ), (-2039725983/10000000000 : ℝ), (1049453801/2000000000 : ℝ)] ![(22117254471957/50000000000000 : ℝ), (3150667441563/25000000000000 : ℝ), (1726512851281/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855517/1600000 : ℝ)|^4405 ≤ (22117254471957/50000000000000 : ℝ)^3381
        have hw : |(855517/1600000 : ℝ)|=(855517/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039725983/10000000000 : ℝ)|^4405 ≤ (3150667441563/25000000000000 : ℝ)^3381
        have hw : |(-2039725983/10000000000 : ℝ)|=(2039725983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049453801/2000000000 : ℝ)|^4405 ≤ (1726512851281/4000000000000 : ℝ)^3381
        have hw : |(1049453801/2000000000 : ℝ)|=(1049453801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s7_2 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346980203/10000000000 : ℝ)*x 0 + (1049454171/2000000000 : ℝ)*x 1 + (-2039724921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346980203/10000000000 : ℝ)^4405 ≤ (8846899531791/20000000000000 : ℝ)^3381 := by
    have hnat : (5346980203 : ℕ)^4405*20000000000000^3381 ≤ 8846899531791^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346980203 10000000000 8846899531791 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049454171/2000000000 : ℝ)^4405 ≤ (43162841108659/100000000000000 : ℝ)^3381 := by
    have hnat : (1049454171 : ℕ)^4405*100000000000000^3381 ≤ 43162841108659^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049454171 2000000000 43162841108659 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2039724921/10000000000 : ℝ)^4405 ≤ (315066530431/2500000000000 : ℝ)^3381 := by
    have hnat : (2039724921 : ℕ)^4405*2500000000000^3381 ≤ 315066530431^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039724921 10000000000 315066530431 2500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346980203/10000000000 : ℝ), (1049454171/2000000000 : ℝ), (-2039724921/10000000000 : ℝ)] ![(8846899531791/20000000000000 : ℝ), (43162841108659/100000000000000 : ℝ), (315066530431/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346980203/10000000000 : ℝ)|^4405 ≤ (8846899531791/20000000000000 : ℝ)^3381
        have hw : |(5346980203/10000000000 : ℝ)|=(5346980203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049454171/2000000000 : ℝ)|^4405 ≤ (43162841108659/100000000000000 : ℝ)^3381
        have hw : |(1049454171/2000000000 : ℝ)|=(1049454171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2039724921/10000000000 : ℝ)|^4405 ≤ (315066530431/2500000000000 : ℝ)^3381
        have hw : |(-2039724921/10000000000 : ℝ)|=(2039724921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s7_3 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150194483/5000000000 : ℝ)*x 0 + (2064673911/5000000000 : ℝ)*x 1 + (895547221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150194483/5000000000 : ℝ)^4405 ≤ (1040779251063/3125000000000 : ℝ)^3381 := by
    have hnat : (2150194483 : ℕ)^4405*3125000000000^3381 ≤ 1040779251063^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150194483 5000000000 1040779251063 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064673911/5000000000 : ℝ)^4405 ≤ (15794791010281/50000000000000 : ℝ)^3381 := by
    have hnat : (2064673911 : ℕ)^4405*50000000000000^3381 ≤ 15794791010281^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064673911 5000000000 15794791010281 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895547221/2000000000 : ℝ)^4405 ≤ (17552740962251/50000000000000 : ℝ)^3381 := by
    have hnat : (895547221 : ℕ)^4405*50000000000000^3381 ≤ 17552740962251^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895547221 2000000000 17552740962251 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150194483/5000000000 : ℝ), (2064673911/5000000000 : ℝ), (895547221/2000000000 : ℝ)] ![(1040779251063/3125000000000 : ℝ), (15794791010281/50000000000000 : ℝ), (17552740962251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150194483/5000000000 : ℝ)|^4405 ≤ (1040779251063/3125000000000 : ℝ)^3381
        have hw : |(2150194483/5000000000 : ℝ)|=(2150194483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064673911/5000000000 : ℝ)|^4405 ≤ (15794791010281/50000000000000 : ℝ)^3381
        have hw : |(2064673911/5000000000 : ℝ)|=(2064673911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895547221/2000000000 : ℝ)|^4405 ≤ (17552740962251/50000000000000 : ℝ)^3381
        have hw : |(895547221/2000000000 : ℝ)|=(895547221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s7_4 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-489559063/2500000000 : ℝ)*x 0 + (2623924229/5000000000 : ℝ)*x 1 + (5406793611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489559063/2500000000 : ℝ)^4405 ≤ (11950690293773/100000000000000 : ℝ)^3381 := by
    have hnat : (489559063 : ℕ)^4405*100000000000000^3381 ≤ 11950690293773^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489559063 2500000000 11950690293773 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623924229/5000000000 : ℝ)^4405 ≤ (43169031440957/100000000000000 : ℝ)^3381 := by
    have hnat : (2623924229 : ℕ)^4405*100000000000000^3381 ≤ 43169031440957^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623924229 5000000000 43169031440957 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406793611/10000000000 : ℝ)^4405 ≤ (22440139124909/50000000000000 : ℝ)^3381 := by
    have hnat : (5406793611 : ℕ)^4405*50000000000000^3381 ≤ 22440139124909^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406793611 10000000000 22440139124909 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489559063/2500000000 : ℝ), (2623924229/5000000000 : ℝ), (5406793611/10000000000 : ℝ)] ![(11950690293773/100000000000000 : ℝ), (43169031440957/100000000000000 : ℝ), (22440139124909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489559063/2500000000 : ℝ)|^4405 ≤ (11950690293773/100000000000000 : ℝ)^3381
        have hw : |(-489559063/2500000000 : ℝ)|=(489559063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623924229/5000000000 : ℝ)|^4405 ≤ (43169031440957/100000000000000 : ℝ)^3381
        have hw : |(2623924229/5000000000 : ℝ)|=(2623924229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406793611/10000000000 : ℝ)|^4405 ≤ (22440139124909/50000000000000 : ℝ)^3381
        have hw : |(5406793611/10000000000 : ℝ)|=(5406793611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s7_5 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305293463/10000000000 : ℝ)*x 0 + (-1880201719/10000000000 : ℝ)*x 1 + (5406793663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305293463/10000000000 : ℝ)^4405 ≤ (21892856903631/50000000000000 : ℝ)^3381 := by
    have hnat : (5305293463 : ℕ)^4405*50000000000000^3381 ≤ 21892856903631^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305293463 10000000000 21892856903631 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880201719/10000000000 : ℝ)^4405 ≤ (5667003684743/50000000000000 : ℝ)^3381 := by
    have hnat : (1880201719 : ℕ)^4405*50000000000000^3381 ≤ 5667003684743^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880201719 10000000000 5667003684743 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406793663/10000000000 : ℝ)^4405 ≤ (8976055762437/20000000000000 : ℝ)^3381 := by
    have hnat : (5406793663 : ℕ)^4405*20000000000000^3381 ≤ 8976055762437^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406793663 10000000000 8976055762437 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305293463/10000000000 : ℝ), (-1880201719/10000000000 : ℝ), (5406793663/10000000000 : ℝ)] ![(21892856903631/50000000000000 : ℝ), (5667003684743/50000000000000 : ℝ), (8976055762437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305293463/10000000000 : ℝ)|^4405 ≤ (21892856903631/50000000000000 : ℝ)^3381
        have hw : |(5305293463/10000000000 : ℝ)|=(5305293463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1880201719/10000000000 : ℝ)|^4405 ≤ (5667003684743/50000000000000 : ℝ)^3381
        have hw : |(-1880201719/10000000000 : ℝ)|=(1880201719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406793663/10000000000 : ℝ)|^4405 ≤ (8976055762437/20000000000000 : ℝ)^3381
        have hw : |(5406793663/10000000000 : ℝ)|=(5406793663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_s7_6 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-25646753/10000000000 : ℝ)*x 0 + (5872279261/10000000000 : ℝ)*x 1 + (5872314407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25646753/10000000000 : ℝ)^4405 ≤ (42102577901/100000000000000 : ℝ)^3381 := by
    have hnat : (25646753 : ℕ)^4405*100000000000000^3381 ≤ 42102577901^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25646753 10000000000 42102577901 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5872279261/10000000000 : ℝ)^4405 ≤ (12494688460197/25000000000000 : ℝ)^3381 := by
    have hnat : (5872279261 : ℕ)^4405*25000000000000^3381 ≤ 12494688460197^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872279261 10000000000 12494688460197 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5872314407/10000000000 : ℝ)^4405 ≤ (49979143563543/100000000000000 : ℝ)^3381 := by
    have hnat : (5872314407 : ℕ)^4405*100000000000000^3381 ≤ 49979143563543^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872314407 10000000000 49979143563543 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25646753/10000000000 : ℝ), (5872279261/10000000000 : ℝ), (5872314407/10000000000 : ℝ)] ![(42102577901/100000000000000 : ℝ), (12494688460197/25000000000000 : ℝ), (49979143563543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25646753/10000000000 : ℝ)|^4405 ≤ (42102577901/100000000000000 : ℝ)^3381
        have hw : |(-25646753/10000000000 : ℝ)|=(25646753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5872279261/10000000000 : ℝ)|^4405 ≤ (12494688460197/25000000000000 : ℝ)^3381
        have hw : |(5872279261/10000000000 : ℝ)|=(5872279261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5872314407/10000000000 : ℝ)|^4405 ≤ (49979143563543/100000000000000 : ℝ)^3381
        have hw : |(5872314407/10000000000 : ℝ)|=(5872314407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1445_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2843/25000 : ℝ) ^ (1101/256 : ℝ) ≤ (2174206754405249/25000000000000000000 : ℝ) := by
    have hpowers : (2843/25000 : ℝ)^1101 ≤ (2174206754405249/25000000000000000000 : ℝ)^256 := by
      have hnat : (2843 : ℕ)^1101*25000000000000000000^256 ≤ 2174206754405249^256*25000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2843 25000 2174206754405249 25000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2843/25000 : ℝ)) (X := (2174206754405249/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (1101/256 : ℝ) ≤ (26733437403671217/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^1101 ≤ (26733437403671217/100000000000000000000 : ℝ)^256 := by
      have hnat : (2953 : ℕ)^1101*100000000000000000000^256 ≤ 26733437403671217^256*20000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 26733437403671217 100000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (26733437403671217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502174206754405249/12500000000000000000 : ℝ) ≤ (5000202201555637/5000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (12502174206754405249/12500000000000000000 : ℝ)^256 ≤ (5000202201555637/5000000000000000 : ℝ)^1101 := by
      have hnat : (12502174206754405249 : ℕ)^256*5000000000000000^1101 ≤ 5000202201555637^1101*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502174206754405249 12500000000000000000 5000202201555637 5000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000202201555637/5000000000000000 : ℝ)) (X := (12502174206754405249/12500000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035430264421292213/100000000000000000000 : ℝ) ≤ (10000823697980423/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (100035430264421292213/100000000000000000000 : ℝ)^256 ≤ (10000823697980423/10000000000000000 : ℝ)^1101 := by
      have hnat : (100035430264421292213 : ℕ)^256*10000000000000000^1101 ≤ 10000823697980423^1101*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035430264421292213 100000000000000000000 10000823697980423 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000823697980423/10000000000000000 : ℝ)) (X := (100035430264421292213/100000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026733437403671217/50000000000000000000 : ℝ) ≤ (2500310748212393/2500000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50026733437403671217/50000000000000000000 : ℝ)^256 ≤ (2500310748212393/2500000000000000 : ℝ)^1101 := by
      have hnat : (50026733437403671217 : ℕ)^256*2500000000000000^1101 ≤ 2500310748212393^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026733437403671217 50000000000000000000 2500310748212393 2500000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500310748212393/2500000000000000 : ℝ)) (X := (50026733437403671217/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2174206754405249/25000000000000000000 : ℝ) ≤ ((434895329451956767/435000000000000000 : ℝ)+2*(10751150491/8700000000000 : ℝ)*(2843/25000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (434895329451956767/435000000000000000 : ℝ)+2*(10751150491/8700000000000 : ℝ)*(2843/25000 : ℝ)=(5000202201555637/5000000000000000 : ℝ) by norm_num, show 1+2*(2174206754405249/25000000000000000000 : ℝ)=(12502174206754405249/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26733437403671217/100000000000000000000 : ℝ)+(2174206754405249/25000000000000000000 : ℝ) ≤ ((434895329451956767/435000000000000000 : ℝ)+(10751150491/8700000000000 : ℝ)*((2953/20000 : ℝ)+(2843/25000 : ℝ)))^(1101/256 : ℝ) := by
    rw [show (434895329451956767/435000000000000000 : ℝ)+(10751150491/8700000000000 : ℝ)*((2953/20000 : ℝ)+(2843/25000 : ℝ))=(10000823697980423/10000000000000000 : ℝ) by norm_num, show 1+(26733437403671217/100000000000000000000 : ℝ)+(2174206754405249/25000000000000000000 : ℝ)=(100035430264421292213/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26733437403671217/100000000000000000000 : ℝ) ≤ ((434895329451956767/435000000000000000 : ℝ)+2*(10751150491/8700000000000 : ℝ)*(2953/20000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (434895329451956767/435000000000000000 : ℝ)+2*(10751150491/8700000000000 : ℝ)*(2953/20000 : ℝ)=(2500310748212393/2500000000000000 : ℝ) by norm_num, show 1+2*(26733437403671217/100000000000000000000 : ℝ)=(50026733437403671217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (434895329451956767/435000000000000000 : ℝ)*(X 1 0+X 2 0)+(10751150491/8700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (434895329451956767/435000000000000000 : ℝ)) (alpha := (10751150491/8700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (434895329451956767/435000000000000000 : ℝ)*(X 0 1+X 2 1)+(10751150491/8700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (434895329451956767/435000000000000000 : ℝ)) (alpha := (10751150491/8700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (434895329451956767/435000000000000000 : ℝ)*(X 0 2+X 1 2)+(10751150491/8700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (434895329451956767/435000000000000000 : ℝ)) (alpha := (10751150491/8700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1958226081/10000000000 : ℝ)*X 0 0+(5407374669/10000000000 : ℝ)*X 0 1+(5247269651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((855517/1600000 : ℝ)*X 1 0+(-2039725983/10000000000 : ℝ)*X 1 1+(1049453801/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346980203/10000000000 : ℝ)*X 2 0+(1049454171/2000000000 : ℝ)*X 2 1+(-2039724921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150194483/5000000000 : ℝ)*X 0 0+(2064673911/5000000000 : ℝ)*X 0 1+(895547221/2000000000 : ℝ)*X 0 2+(2150194483/5000000000 : ℝ)*X 1 0+(2064673911/5000000000 : ℝ)*X 1 1+(895547221/2000000000 : ℝ)*X 1 2+(2150194483/5000000000 : ℝ)*X 2 0+(2064673911/5000000000 : ℝ)*X 2 1+(895547221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-489559063/2500000000 : ℝ)*X 0 0+(2623924229/5000000000 : ℝ)*X 0 1+(5406793611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305293463/10000000000 : ℝ)*X 1 0+(-1880201719/10000000000 : ℝ)*X 1 1+(5406793663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-25646753/10000000000 : ℝ)*X 0 0+(5872279261/10000000000 : ℝ)*X 0 1+(5872314407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_s7_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32278123725211878360448971/7250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11658831/12500000000000 : ℝ)*(lower2) + (2283081/4000000000000 : ℝ)*(lower3) + (46385907/10000000000000 : ℝ)*(lower4) + (249681447/50000000000000 : ℝ)*(lower5) + (4558164323166987/100000000000000 : ℝ)*(major0) + (4558164323166987/100000000000000 : ℝ)*(major1) + (4558164323166987/100000000000000 : ℝ)*(major2) + (249837853145663/4000000000000 : ℝ)*(sp0) + (1249180107693557/20000000000000 : ℝ)*(sp1) + (6245968511486503/100000000000000 : ℝ)*(sp2) + (71758999661057/2500000000000 : ℝ)*(sp3) + (3483208379/25000000000000 : ℝ)*(sp4) + (33986509359/50000000000000 : ℝ)*(sp5) + (2062502853/25000000000000 : ℝ)*(sp6) + (71758999661057/2500000000000 : ℝ)*(f.failure) + (6245968511486503/100000000000000 : ℝ)*(f.sum) + (5569203678087/72500000000000000000000000 : ℝ)*base65 + (1183819167310333/500000000000000000000000000000 : ℝ)*base68 + (9077522837689667/500000000000000000000000000000 : ℝ)*base69 + (3124115098189667/500000000000000000000000000000 : ℝ)*base71 + (59631968851/36250000000000000000000000 : ℝ)*base73 + (4431288500689667/500000000000000000000000000000 : ℝ)*base75 + (45855800885689667/500000000000000000000000000000 : ℝ)*base77 + (118949932310333/500000000000000000000000000000 : ℝ)*base80 + (441214841837/72500000000000000000000000 : ℝ)*base81 + (808567/125000000000000000000 : ℝ)*base90 + (808567/125000000000000000000 : ℝ)*base92 + (808567/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1445_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1445_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1445_box_0 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17987067/100000000 : ℝ)*x 0 + (5385570881/10000000000 : ℝ)*x 1 + (5385571007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17987067/100000000 : ℝ)^4405 ≤ (5349103033389/50000000000000 : ℝ)^3381 := by
    have hnat : (17987067 : ℕ)^4405*50000000000000^3381 ≤ 5349103033389^3381*100000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17987067 100000000 5349103033389 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385570881/10000000000 : ℝ)^4405 ≤ (44650896279983/100000000000000 : ℝ)^3381 := by
    have hnat : (5385570881 : ℕ)^4405*100000000000000^3381 ≤ 44650896279983^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385570881 10000000000 44650896279983 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385571007/10000000000 : ℝ)^4405 ≤ (44650897641019/100000000000000 : ℝ)^3381 := by
    have hnat : (5385571007 : ℕ)^4405*100000000000000^3381 ≤ 44650897641019^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385571007 10000000000 44650897641019 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17987067/100000000 : ℝ), (5385570881/10000000000 : ℝ), (5385571007/10000000000 : ℝ)] ![(5349103033389/50000000000000 : ℝ), (44650896279983/100000000000000 : ℝ), (44650897641019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17987067/100000000 : ℝ)|^4405 ≤ (5349103033389/50000000000000 : ℝ)^3381
        have hw : |(-17987067/100000000 : ℝ)|=(17987067/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385570881/10000000000 : ℝ)|^4405 ≤ (44650896279983/100000000000000 : ℝ)^3381
        have hw : |(5385570881/10000000000 : ℝ)|=(5385570881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385571007/10000000000 : ℝ)|^4405 ≤ (44650897641019/100000000000000 : ℝ)^3381
        have hw : |(5385571007/10000000000 : ℝ)|=(5385571007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_1 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286169981/10000000000 : ℝ)*x 0 + (-967666801/5000000000 : ℝ)*x 1 + (336598167/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286169981/10000000000 : ℝ)^4405 ≤ (21790097065481/50000000000000 : ℝ)^3381 := by
    have hnat : (5286169981 : ℕ)^4405*50000000000000^3381 ≤ 21790097065481^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286169981 10000000000 21790097065481 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967666801/5000000000 : ℝ)^4405 ≤ (9415129469/80000000000 : ℝ)^3381 := by
    have hnat : (967666801 : ℕ)^4405*80000000000^3381 ≤ 9415129469^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967666801 5000000000 9415129469 80000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336598167/625000000 : ℝ)^4405 ≤ (44650894022391/100000000000000 : ℝ)^3381 := by
    have hnat : (336598167 : ℕ)^4405*100000000000000^3381 ≤ 44650894022391^3381*625000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336598167 625000000 44650894022391 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286169981/10000000000 : ℝ), (-967666801/5000000000 : ℝ), (336598167/625000000 : ℝ)] ![(21790097065481/50000000000000 : ℝ), (9415129469/80000000000 : ℝ), (44650894022391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286169981/10000000000 : ℝ)|^4405 ≤ (21790097065481/50000000000000 : ℝ)^3381
        have hw : |(5286169981/10000000000 : ℝ)|=(5286169981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-967666801/5000000000 : ℝ)|^4405 ≤ (9415129469/80000000000 : ℝ)^3381
        have hw : |(-967666801/5000000000 : ℝ)|=(967666801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336598167/625000000 : ℝ)|^4405 ≤ (44650894022391/100000000000000 : ℝ)^3381
        have hw : |(336598167/625000000 : ℝ)|=(336598167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_2 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057233971/2000000000 : ℝ)*x 0 + (5385570597/10000000000 : ℝ)*x 1 + (-15482671/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057233971/2000000000 : ℝ)^4405 ≤ (43580192777583/100000000000000 : ℝ)^3381 := by
    have hnat : (1057233971 : ℕ)^4405*100000000000000^3381 ≤ 43580192777583^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057233971 2000000000 43580192777583 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385570597/10000000000 : ℝ)^4405 ≤ (178603572849/400000000000 : ℝ)^3381 := by
    have hnat : (5385570597 : ℕ)^4405*400000000000^3381 ≤ 178603572849^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385570597 10000000000 178603572849 400000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15482671/80000000 : ℝ)^4405 ≤ (11768913999187/100000000000000 : ℝ)^3381 := by
    have hnat : (15482671 : ℕ)^4405*100000000000000^3381 ≤ 11768913999187^3381*80000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15482671 80000000 11768913999187 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057233971/2000000000 : ℝ), (5385570597/10000000000 : ℝ), (-15482671/80000000 : ℝ)] ![(43580192777583/100000000000000 : ℝ), (178603572849/400000000000 : ℝ), (11768913999187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057233971/2000000000 : ℝ)|^4405 ≤ (43580192777583/100000000000000 : ℝ)^3381
        have hw : |(1057233971/2000000000 : ℝ)|=(1057233971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385570597/10000000000 : ℝ)|^4405 ≤ (178603572849/400000000000 : ℝ)^3381
        have hw : |(5385570597/10000000000 : ℝ)|=(5385570597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15482671/80000000 : ℝ)|^4405 ≤ (11768913999187/100000000000000 : ℝ)^3381
        have hw : |(-15482671/80000000 : ℝ)|=(15482671/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_3 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2223186773/5000000000 : ℝ)*x 0 + (2115538113/5000000000 : ℝ)*x 1 + (4231075859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2223186773/5000000000 : ℝ)^4405 ≤ (8696367338173/25000000000000 : ℝ)^3381 := by
    have hnat : (2223186773 : ℕ)^4405*25000000000000^3381 ≤ 8696367338173^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223186773 5000000000 8696367338173 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115538113/5000000000 : ℝ)^4405 ≤ (16303633577967/50000000000000 : ℝ)^3381 := by
    have hnat : (2115538113 : ℕ)^4405*50000000000000^3381 ≤ 16303633577967^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115538113 5000000000 16303633577967 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231075859/10000000000 : ℝ)^4405 ≤ (16303631735497/50000000000000 : ℝ)^3381 := by
    have hnat : (4231075859 : ℕ)^4405*50000000000000^3381 ≤ 16303631735497^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231075859 10000000000 16303631735497 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2223186773/5000000000 : ℝ), (2115538113/5000000000 : ℝ), (4231075859/10000000000 : ℝ)] ![(8696367338173/25000000000000 : ℝ), (16303633577967/50000000000000 : ℝ), (16303631735497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2223186773/5000000000 : ℝ)|^4405 ≤ (8696367338173/25000000000000 : ℝ)^3381
        have hw : |(2223186773/5000000000 : ℝ)|=(2223186773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115538113/5000000000 : ℝ)|^4405 ≤ (16303633577967/50000000000000 : ℝ)^3381
        have hw : |(2115538113/5000000000 : ℝ)|=(2115538113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231075859/10000000000 : ℝ)|^4405 ≤ (16303631735497/50000000000000 : ℝ)^3381
        have hw : |(4231075859/10000000000 : ℝ)|=(4231075859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_4 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060235267/5000000000 : ℝ)*x 0 + (1316687977/2500000000 : ℝ)*x 1 + (16458601/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060235267/5000000000 : ℝ)^4405 ≤ (6628259006769/50000000000000 : ℝ)^3381 := by
    have hnat : (1060235267 : ℕ)^4405*50000000000000^3381 ≤ 6628259006769^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060235267 5000000000 6628259006769 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316687977/2500000000 : ℝ)^4405 ≤ (43371738780539/100000000000000 : ℝ)^3381 := by
    have hnat : (1316687977 : ℕ)^4405*100000000000000^3381 ≤ 43371738780539^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316687977 2500000000 43371738780539 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16458601/31250000 : ℝ)^4405 ≤ (43371743200943/100000000000000 : ℝ)^3381 := by
    have hnat : (16458601 : ℕ)^4405*100000000000000^3381 ≤ 43371743200943^3381*31250000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16458601 31250000 43371743200943 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060235267/5000000000 : ℝ), (1316687977/2500000000 : ℝ), (16458601/31250000 : ℝ)] ![(6628259006769/50000000000000 : ℝ), (43371738780539/100000000000000 : ℝ), (43371743200943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060235267/5000000000 : ℝ)|^4405 ≤ (6628259006769/50000000000000 : ℝ)^3381
        have hw : |(-1060235267/5000000000 : ℝ)|=(1060235267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316687977/2500000000 : ℝ)|^4405 ≤ (43371738780539/100000000000000 : ℝ)^3381
        have hw : |(1316687977/2500000000 : ℝ)|=(1316687977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16458601/31250000 : ℝ)|^4405 ≤ (43371743200943/100000000000000 : ℝ)^3381
        have hw : |(16458601/31250000 : ℝ)|=(16458601/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_5 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073854119/2000000000 : ℝ)*x 0 + (-247959433/1250000000 : ℝ)*x 1 + (5266751947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073854119/2000000000 : ℝ)^4405 ≤ (22237451687361/50000000000000 : ℝ)^3381 := by
    have hnat : (1073854119 : ℕ)^4405*50000000000000^3381 ≤ 22237451687361^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073854119 2000000000 22237451687361 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247959433/1250000000 : ℝ)^4405 ≤ (1215335740443/10000000000000 : ℝ)^3381 := by
    have hnat : (247959433 : ℕ)^4405*10000000000000^3381 ≤ 1215335740443^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247959433 1250000000 1215335740443 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266751947/10000000000 : ℝ)^4405 ≤ (84710428123/195312500000 : ℝ)^3381 := by
    have hnat : (5266751947 : ℕ)^4405*195312500000^3381 ≤ 84710428123^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266751947 10000000000 84710428123 195312500000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073854119/2000000000 : ℝ), (-247959433/1250000000 : ℝ), (5266751947/10000000000 : ℝ)] ![(22237451687361/50000000000000 : ℝ), (1215335740443/10000000000000 : ℝ), (84710428123/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073854119/2000000000 : ℝ)|^4405 ≤ (22237451687361/50000000000000 : ℝ)^3381
        have hw : |(1073854119/2000000000 : ℝ)|=(1073854119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247959433/1250000000 : ℝ)|^4405 ≤ (1215335740443/10000000000000 : ℝ)^3381
        have hw : |(-247959433/1250000000 : ℝ)|=(247959433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266751947/10000000000 : ℝ)|^4405 ≤ (84710428123/195312500000 : ℝ)^3381
        have hw : |(5266751947/10000000000 : ℝ)|=(5266751947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_6 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134231763/250000000 : ℝ)*x 0 + (5266752481/10000000000 : ℝ)*x 1 + (-1983674849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134231763/250000000 : ℝ)^4405 ≤ (1778996102613/4000000000000 : ℝ)^3381 := by
    have hnat : (134231763 : ℕ)^4405*4000000000000^3381 ≤ 1778996102613^3381*250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134231763 250000000 1778996102613 4000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266752481/10000000000 : ℝ)^4405 ≤ (21685872464167/50000000000000 : ℝ)^3381 := by
    have hnat : (5266752481 : ℕ)^4405*50000000000000^3381 ≤ 21685872464167^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266752481 10000000000 21685872464167 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983674849/10000000000 : ℝ)^4405 ≤ (6076676247667/50000000000000 : ℝ)^3381 := by
    have hnat : (1983674849 : ℕ)^4405*50000000000000^3381 ≤ 6076676247667^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983674849 10000000000 6076676247667 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134231763/250000000 : ℝ), (5266752481/10000000000 : ℝ), (-1983674849/10000000000 : ℝ)] ![(1778996102613/4000000000000 : ℝ), (21685872464167/50000000000000 : ℝ), (6076676247667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134231763/250000000 : ℝ)|^4405 ≤ (1778996102613/4000000000000 : ℝ)^3381
        have hw : |(134231763/250000000 : ℝ)|=(134231763/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266752481/10000000000 : ℝ)|^4405 ≤ (21685872464167/50000000000000 : ℝ)^3381
        have hw : |(5266752481/10000000000 : ℝ)|=(5266752481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983674849/10000000000 : ℝ)|^4405 ≤ (6076676247667/50000000000000 : ℝ)^3381
        have hw : |(-1983674849/10000000000 : ℝ)|=(1983674849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_7 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038334241/2500000000 : ℝ)*x 0 + (4377543049/10000000000 : ℝ)*x 1 + (547193093/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038334241/2500000000 : ℝ)^4405 ≤ (31828891145319/100000000000000 : ℝ)^3381 := by
    have hnat : (1038334241 : ℕ)^4405*100000000000000^3381 ≤ 31828891145319^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038334241 2500000000 31828891145319 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4377543049/10000000000 : ℝ)^4405 ≤ (34085545822497/100000000000000 : ℝ)^3381 := by
    have hnat : (4377543049 : ℕ)^4405*100000000000000^3381 ≤ 34085545822497^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377543049 10000000000 34085545822497 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547193093/1250000000 : ℝ)^4405 ≤ (17042781508909/50000000000000 : ℝ)^3381 := by
    have hnat : (547193093 : ℕ)^4405*50000000000000^3381 ≤ 17042781508909^3381*1250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547193093 1250000000 17042781508909 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038334241/2500000000 : ℝ), (4377543049/10000000000 : ℝ), (547193093/1250000000 : ℝ)] ![(31828891145319/100000000000000 : ℝ), (34085545822497/100000000000000 : ℝ), (17042781508909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038334241/2500000000 : ℝ)|^4405 ≤ (31828891145319/100000000000000 : ℝ)^3381
        have hw : |(1038334241/2500000000 : ℝ)|=(1038334241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4377543049/10000000000 : ℝ)|^4405 ≤ (34085545822497/100000000000000 : ℝ)^3381
        have hw : |(4377543049/10000000000 : ℝ)|=(4377543049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547193093/1250000000 : ℝ)|^4405 ≤ (17042781508909/50000000000000 : ℝ)^3381
        have hw : |(547193093/1250000000 : ℝ)|=(547193093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_8 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026331581/5000000000 : ℝ)*x 0 + (2592247683/5000000000 : ℝ)*x 1 + (5399535073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026331581/5000000000 : ℝ)^4405 ≤ (12706912881073/100000000000000 : ℝ)^3381 := by
    have hnat : (1026331581 : ℕ)^4405*100000000000000^3381 ≤ 12706912881073^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026331581 5000000000 12706912881073 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592247683/5000000000 : ℝ)^4405 ≤ (1327852880217/3125000000000 : ℝ)^3381 := by
    have hnat : (2592247683 : ℕ)^4405*3125000000000^3381 ≤ 1327852880217^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592247683 5000000000 1327852880217 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399535073/10000000000 : ℝ)^4405 ≤ (22400897469299/50000000000000 : ℝ)^3381 := by
    have hnat : (5399535073 : ℕ)^4405*50000000000000^3381 ≤ 22400897469299^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399535073 10000000000 22400897469299 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026331581/5000000000 : ℝ), (2592247683/5000000000 : ℝ), (5399535073/10000000000 : ℝ)] ![(12706912881073/100000000000000 : ℝ), (1327852880217/3125000000000 : ℝ), (22400897469299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026331581/5000000000 : ℝ)|^4405 ≤ (12706912881073/100000000000000 : ℝ)^3381
        have hw : |(-1026331581/5000000000 : ℝ)|=(1026331581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592247683/5000000000 : ℝ)|^4405 ≤ (1327852880217/3125000000000 : ℝ)^3381
        have hw : |(2592247683/5000000000 : ℝ)|=(2592247683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399535073/10000000000 : ℝ)|^4405 ≤ (22400897469299/50000000000000 : ℝ)^3381
        have hw : |(5399535073/10000000000 : ℝ)|=(5399535073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_9 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527639949/1000000000 : ℝ)*x 0 + (-385905423/2000000000 : ℝ)*x 1 + (1079906987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527639949/1000000000 : ℝ)^4405 ≤ (8695055538477/20000000000000 : ℝ)^3381 := by
    have hnat : (527639949 : ℕ)^4405*20000000000000^3381 ≤ 8695055538477^3381*1000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527639949 1000000000 8695055538477 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385905423/2000000000 : ℝ)^4405 ≤ (11722928850027/100000000000000 : ℝ)^3381 := by
    have hnat : (385905423 : ℕ)^4405*100000000000000^3381 ≤ 11722928850027^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385905423 2000000000 11722928850027 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079906987/2000000000 : ℝ)^4405 ≤ (44801793446769/100000000000000 : ℝ)^3381 := by
    have hnat : (1079906987 : ℕ)^4405*100000000000000^3381 ≤ 44801793446769^3381*2000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079906987 2000000000 44801793446769 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527639949/1000000000 : ℝ), (-385905423/2000000000 : ℝ), (1079906987/2000000000 : ℝ)] ![(8695055538477/20000000000000 : ℝ), (11722928850027/100000000000000 : ℝ), (44801793446769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527639949/1000000000 : ℝ)|^4405 ≤ (8695055538477/20000000000000 : ℝ)^3381
        have hw : |(527639949/1000000000 : ℝ)|=(527639949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385905423/2000000000 : ℝ)|^4405 ≤ (11722928850027/100000000000000 : ℝ)^3381
        have hw : |(-385905423/2000000000 : ℝ)|=(385905423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079906987/2000000000 : ℝ)|^4405 ≤ (44801793446769/100000000000000 : ℝ)^3381
        have hw : |(1079906987/2000000000 : ℝ)|=(1079906987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_10 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638199561/5000000000 : ℝ)*x 0 + (2699767551/5000000000 : ℝ)*x 1 + (-964763693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638199561/5000000000 : ℝ)^4405 ≤ (21737636870937/50000000000000 : ℝ)^3381 := by
    have hnat : (2638199561 : ℕ)^4405*50000000000000^3381 ≤ 21737636870937^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638199561 5000000000 21737636870937 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699767551/5000000000 : ℝ)^4405 ≤ (22400897626049/50000000000000 : ℝ)^3381 := by
    have hnat : (2699767551 : ℕ)^4405*50000000000000^3381 ≤ 22400897626049^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699767551 5000000000 22400897626049 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964763693/5000000000 : ℝ)^4405 ≤ (2344586199033/20000000000000 : ℝ)^3381 := by
    have hnat : (964763693 : ℕ)^4405*20000000000000^3381 ≤ 2344586199033^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964763693 5000000000 2344586199033 20000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638199561/5000000000 : ℝ), (2699767551/5000000000 : ℝ), (-964763693/5000000000 : ℝ)] ![(21737636870937/50000000000000 : ℝ), (22400897626049/50000000000000 : ℝ), (2344586199033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638199561/5000000000 : ℝ)|^4405 ≤ (21737636870937/50000000000000 : ℝ)^3381
        have hw : |(2638199561/5000000000 : ℝ)|=(2638199561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699767551/5000000000 : ℝ)|^4405 ≤ (22400897626049/50000000000000 : ℝ)^3381
        have hw : |(2699767551/5000000000 : ℝ)|=(2699767551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964763693/5000000000 : ℝ)|^4405 ≤ (2344586199033/20000000000000 : ℝ)^3381
        have hw : |(-964763693/5000000000 : ℝ)|=(964763693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_11 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240128163/5000000000 : ℝ)*x 0 + (4213847851/10000000000 : ℝ)*x 1 + (1053461847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240128163/5000000000 : ℝ)^4405 ≤ (35131226920109/100000000000000 : ℝ)^3381 := by
    have hnat : (2240128163 : ℕ)^4405*100000000000000^3381 ≤ 35131226920109^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240128163 5000000000 35131226920109 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4213847851/10000000000 : ℝ)^4405 ≤ (3243438885773/10000000000000 : ℝ)^3381 := by
    have hnat : (4213847851 : ℕ)^4405*10000000000000^3381 ≤ 3243438885773^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213847851 10000000000 3243438885773 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053461847/2500000000 : ℝ)^4405 ≤ (1013574506707/3125000000000 : ℝ)^3381 := by
    have hnat : (1053461847 : ℕ)^4405*3125000000000^3381 ≤ 1013574506707^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053461847 2500000000 1013574506707 3125000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240128163/5000000000 : ℝ), (4213847851/10000000000 : ℝ), (1053461847/2500000000 : ℝ)] ![(35131226920109/100000000000000 : ℝ), (3243438885773/10000000000000 : ℝ), (1013574506707/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240128163/5000000000 : ℝ)|^4405 ≤ (35131226920109/100000000000000 : ℝ)^3381
        have hw : |(2240128163/5000000000 : ℝ)|=(2240128163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4213847851/10000000000 : ℝ)|^4405 ≤ (3243438885773/10000000000000 : ℝ)^3381
        have hw : |(4213847851/10000000000 : ℝ)|=(4213847851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053461847/2500000000 : ℝ)|^4405 ≤ (1013574506707/3125000000000 : ℝ)^3381
        have hw : |(1053461847/2500000000 : ℝ)|=(1053461847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_12 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46666693/250000000 : ℝ)*x 0 + (5465834651/10000000000 : ℝ)*x 1 + (2627809209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46666693/250000000 : ℝ)^4405 ≤ (11227830119899/100000000000000 : ℝ)^3381 := by
    have hnat : (46666693 : ℕ)^4405*100000000000000^3381 ≤ 11227830119899^3381*250000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46666693 250000000 11227830119899 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465834651/10000000000 : ℝ)^4405 ≤ (45519845547243/100000000000000 : ℝ)^3381 := by
    have hnat : (5465834651 : ℕ)^4405*100000000000000^3381 ≤ 45519845547243^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465834651 10000000000 45519845547243 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627809209/5000000000 : ℝ)^4405 ≤ (43252324320171/100000000000000 : ℝ)^3381 := by
    have hnat : (2627809209 : ℕ)^4405*100000000000000^3381 ≤ 43252324320171^3381*5000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627809209 5000000000 43252324320171 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46666693/250000000 : ℝ), (5465834651/10000000000 : ℝ), (2627809209/5000000000 : ℝ)] ![(11227830119899/100000000000000 : ℝ), (45519845547243/100000000000000 : ℝ), (43252324320171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46666693/250000000 : ℝ)|^4405 ≤ (11227830119899/100000000000000 : ℝ)^3381
        have hw : |(-46666693/250000000 : ℝ)|=(46666693/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465834651/10000000000 : ℝ)|^4405 ≤ (45519845547243/100000000000000 : ℝ)^3381
        have hw : |(5465834651/10000000000 : ℝ)|=(5465834651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627809209/5000000000 : ℝ)|^4405 ≤ (43252324320171/100000000000000 : ℝ)^3381
        have hw : |(2627809209/5000000000 : ℝ)|=(2627809209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_13 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10502063/19531250 : ℝ)*x 0 + (-1988105371/10000000000 : ℝ)*x 1 + (525561853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10502063/19531250 : ℝ)^4405 ≤ (22279472193607/50000000000000 : ℝ)^3381 := by
    have hnat : (10502063 : ℕ)^4405*50000000000000^3381 ≤ 22279472193607^3381*19531250^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10502063 19531250 22279472193607 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988105371/10000000000 : ℝ)^4405 ≤ (3047182517093/25000000000000 : ℝ)^3381 := by
    have hnat : (1988105371 : ℕ)^4405*25000000000000^3381 ≤ 3047182517093^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988105371 10000000000 3047182517093 25000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525561853/1000000000 : ℝ)^4405 ≤ (5406540690133/12500000000000 : ℝ)^3381 := by
    have hnat : (525561853 : ℕ)^4405*12500000000000^3381 ≤ 5406540690133^3381*1000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525561853 1000000000 5406540690133 12500000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10502063/19531250 : ℝ), (-1988105371/10000000000 : ℝ), (525561853/1000000000 : ℝ)] ![(22279472193607/50000000000000 : ℝ), (3047182517093/25000000000000 : ℝ), (5406540690133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10502063/19531250 : ℝ)|^4405 ≤ (22279472193607/50000000000000 : ℝ)^3381
        have hw : |(10502063/19531250 : ℝ)|=(10502063/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988105371/10000000000 : ℝ)|^4405 ≤ (3047182517093/25000000000000 : ℝ)^3381
        have hw : |(-1988105371/10000000000 : ℝ)|=(1988105371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525561853/1000000000 : ℝ)|^4405 ≤ (5406540690133/12500000000000 : ℝ)^3381
        have hw : |(525561853/1000000000 : ℝ)|=(525561853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_14 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344264037/2500000000 : ℝ)*x 0 + (5255618599/10000000000 : ℝ)*x 1 + (-79524217/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344264037/2500000000 : ℝ)^4405 ≤ (4455894322117/10000000000000 : ℝ)^3381 := by
    have hnat : (1344264037 : ℕ)^4405*10000000000000^3381 ≤ 4455894322117^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344264037 2500000000 4455894322117 10000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255618599/10000000000 : ℝ)^4405 ≤ (432523262609/1000000000000 : ℝ)^3381 := by
    have hnat : (5255618599 : ℕ)^4405*1000000000000^3381 ≤ 432523262609^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255618599 10000000000 432523262609 1000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79524217/400000000 : ℝ)^4405 ≤ (6094365249853/50000000000000 : ℝ)^3381 := by
    have hnat : (79524217 : ℕ)^4405*50000000000000^3381 ≤ 6094365249853^3381*400000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79524217 400000000 6094365249853 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344264037/2500000000 : ℝ), (5255618599/10000000000 : ℝ), (-79524217/400000000 : ℝ)] ![(4455894322117/10000000000000 : ℝ), (432523262609/1000000000000 : ℝ), (6094365249853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344264037/2500000000 : ℝ)|^4405 ≤ (4455894322117/10000000000000 : ℝ)^3381
        have hw : |(1344264037/2500000000 : ℝ)|=(1344264037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255618599/10000000000 : ℝ)|^4405 ≤ (432523262609/1000000000000 : ℝ)^3381
        have hw : |(5255618599/10000000000 : ℝ)|=(5255618599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79524217/400000000 : ℝ)|^4405 ≤ (6094365249853/50000000000000 : ℝ)^3381
        have hw : |(-79524217/400000000 : ℝ)|=(79524217/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1445_box_15 (p : ℝ) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206271387/500000000 : ℝ)*x 0 + (4391257673/10000000000 : ℝ)*x 1 + (1097814363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206271387/500000000 : ℝ)^4405 ≤ (31550516298589/100000000000000 : ℝ)^3381 := by
    have hnat : (206271387 : ℕ)^4405*100000000000000^3381 ≤ 31550516298589^3381*500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206271387 500000000 31550516298589 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4391257673/10000000000 : ℝ)^4405 ≤ (17112371482717/50000000000000 : ℝ)^3381 := by
    have hnat : (4391257673 : ℕ)^4405*50000000000000^3381 ≤ 17112371482717^3381*10000000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391257673 10000000000 17112371482717 50000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097814363/2500000000 : ℝ)^4405 ≤ (34224740721323/100000000000000 : ℝ)^3381 := by
    have hnat : (1097814363 : ℕ)^4405*100000000000000^3381 ≤ 34224740721323^3381*2500000000^4405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097814363 2500000000 34224740721323 100000000000000 4405 3381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4405/1024 : ℝ)) 4405 3381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206271387/500000000 : ℝ), (4391257673/10000000000 : ℝ), (1097814363/2500000000 : ℝ)] ![(31550516298589/100000000000000 : ℝ), (17112371482717/50000000000000 : ℝ), (34224740721323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206271387/500000000 : ℝ)|^4405 ≤ (31550516298589/100000000000000 : ℝ)^3381
        have hw : |(206271387/500000000 : ℝ)|=(206271387/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4391257673/10000000000 : ℝ)|^4405 ≤ (17112371482717/50000000000000 : ℝ)^3381
        have hw : |(4391257673/10000000000 : ℝ)|=(4391257673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097814363/2500000000 : ℝ)|^4405 ≤ (34224740721323/100000000000000 : ℝ)^3381
        have hw : |(1097814363/2500000000 : ℝ)|=(1097814363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1445_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6291/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11829/20000 : ℝ) ∧ (10067/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16949/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (1101/256 : ℝ) ≤ (348004662059627/4000000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^1101 ≤ (348004662059627/4000000000000000000 : ℝ)^256 := by
      have hnat : (11373 : ℕ)^1101*4000000000000000000^256 ≤ 348004662059627^256*100000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 348004662059627 4000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (348004662059627/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (1101/256 : ℝ) ≤ (26733437403671217/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^1101 ≤ (26733437403671217/100000000000000000000 : ℝ)^256 := by
      have hnat : (2953 : ℕ)^1101*100000000000000000000^256 ≤ 26733437403671217^256*20000^1101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 26733437403671217 100000000000000000000 1101 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (26733437403671217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000348004662059627/2000000000000000000 : ℝ) ≤ (5000202278032317/5000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (2000348004662059627/2000000000000000000 : ℝ)^256 ≤ (5000202278032317/5000000000000000 : ℝ)^1101 := by
      have hnat : (2000348004662059627 : ℕ)^256*5000000000000000^1101 ≤ 5000202278032317^1101*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000348004662059627 2000000000000000000 5000202278032317 5000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000202278032317/5000000000000000 : ℝ)) (X := (2000348004662059627/2000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008858388488790473/25000000000000000000 : ℝ) ≤ (10000823774446521/10000000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (25008858388488790473/25000000000000000000 : ℝ)^256 ≤ (10000823774446521/10000000000000000 : ℝ)^1101 := by
      have hnat : (25008858388488790473 : ℕ)^256*10000000000000000^1101 ≤ 10000823774446521^1101*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008858388488790473 25000000000000000000 10000823774446521 10000000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000823774446521/10000000000000000 : ℝ)) (X := (25008858388488790473/25000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026733437403671217/50000000000000000000 : ℝ) ≤ (1250155374103551/1250000000000000 : ℝ) ^ (1101/256 : ℝ) := by
    have hpowers : (50026733437403671217/50000000000000000000 : ℝ)^256 ≤ (1250155374103551/1250000000000000 : ℝ)^1101 := by
      have hnat : (50026733437403671217 : ℕ)^256*1250000000000000^1101 ≤ 1250155374103551^1101*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026733437403671217 50000000000000000000 1250155374103551 1250000000000000 256 1101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250155374103551/1250000000000000 : ℝ)) (X := (50026733437403671217/50000000000000000000 : ℝ)) (by norm_num) 1101 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(348004662059627/4000000000000000000 : ℝ) ≤ ((16955918356428418413/16960000000000000000 : ℝ)+2*(419218381887/339200000000000 : ℝ)*(11373/100000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (16955918356428418413/16960000000000000000 : ℝ)+2*(419218381887/339200000000000 : ℝ)*(11373/100000 : ℝ)=(5000202278032317/5000000000000000 : ℝ) by norm_num, show 1+2*(348004662059627/4000000000000000000 : ℝ)=(2000348004662059627/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26733437403671217/100000000000000000000 : ℝ)+(348004662059627/4000000000000000000 : ℝ) ≤ ((16955918356428418413/16960000000000000000 : ℝ)+(419218381887/339200000000000 : ℝ)*((2953/20000 : ℝ)+(11373/100000 : ℝ)))^(1101/256 : ℝ) := by
    rw [show (16955918356428418413/16960000000000000000 : ℝ)+(419218381887/339200000000000 : ℝ)*((2953/20000 : ℝ)+(11373/100000 : ℝ))=(10000823774446521/10000000000000000 : ℝ) by norm_num, show 1+(26733437403671217/100000000000000000000 : ℝ)+(348004662059627/4000000000000000000 : ℝ)=(25008858388488790473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26733437403671217/100000000000000000000 : ℝ) ≤ ((16955918356428418413/16960000000000000000 : ℝ)+2*(419218381887/339200000000000 : ℝ)*(2953/20000 : ℝ))^(1101/256 : ℝ) := by
    rw [show (16955918356428418413/16960000000000000000 : ℝ)+2*(419218381887/339200000000000 : ℝ)*(2953/20000 : ℝ)=(1250155374103551/1250000000000000 : ℝ) by norm_num, show 1+2*(26733437403671217/100000000000000000000 : ℝ)=(50026733437403671217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16955918356428418413/16960000000000000000 : ℝ)*(X 1 0+X 2 0)+(419218381887/339200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (16955918356428418413/16960000000000000000 : ℝ)) (alpha := (419218381887/339200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16955918356428418413/16960000000000000000 : ℝ)*(X 0 1+X 2 1)+(419218381887/339200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (16955918356428418413/16960000000000000000 : ℝ)) (alpha := (419218381887/339200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16955918356428418413/16960000000000000000 : ℝ)*(X 0 2+X 1 2)+(419218381887/339200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1101/256 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (16955918356428418413/16960000000000000000 : ℝ)) (alpha := (419218381887/339200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-17987067/100000000 : ℝ)*X 0 0+(5385570881/10000000000 : ℝ)*X 0 1+(5385571007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286169981/10000000000 : ℝ)*X 1 0+(-967666801/5000000000 : ℝ)*X 1 1+(336598167/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057233971/2000000000 : ℝ)*X 2 0+(5385570597/10000000000 : ℝ)*X 2 1+(-15482671/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2223186773/5000000000 : ℝ)*X 0 0+(2115538113/5000000000 : ℝ)*X 0 1+(4231075859/10000000000 : ℝ)*X 0 2+(2223186773/5000000000 : ℝ)*X 1 0+(2115538113/5000000000 : ℝ)*X 1 1+(4231075859/10000000000 : ℝ)*X 1 2+(2223186773/5000000000 : ℝ)*X 2 0+(2115538113/5000000000 : ℝ)*X 2 1+(4231075859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060235267/5000000000 : ℝ)*X 0 0+(1316687977/2500000000 : ℝ)*X 0 1+(16458601/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1073854119/2000000000 : ℝ)*X 1 0+(-247959433/1250000000 : ℝ)*X 1 1+(5266751947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((134231763/250000000 : ℝ)*X 2 0+(5266752481/10000000000 : ℝ)*X 2 1+(-1983674849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1038334241/2500000000 : ℝ)*X 0 0+(4377543049/10000000000 : ℝ)*X 0 1+(547193093/1250000000 : ℝ)*X 0 2+(1038334241/2500000000 : ℝ)*X 1 0+(4377543049/10000000000 : ℝ)*X 1 1+(547193093/1250000000 : ℝ)*X 1 2+(1038334241/2500000000 : ℝ)*X 2 0+(4377543049/10000000000 : ℝ)*X 2 1+(547193093/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1026331581/5000000000 : ℝ)*X 0 0+(2592247683/5000000000 : ℝ)*X 0 1+(5399535073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527639949/1000000000 : ℝ)*X 1 0+(-385905423/2000000000 : ℝ)*X 1 1+(1079906987/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638199561/5000000000 : ℝ)*X 2 0+(2699767551/5000000000 : ℝ)*X 2 1+(-964763693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2240128163/5000000000 : ℝ)*X 0 0+(4213847851/10000000000 : ℝ)*X 0 1+(1053461847/2500000000 : ℝ)*X 0 2+(2240128163/5000000000 : ℝ)*X 1 0+(4213847851/10000000000 : ℝ)*X 1 1+(1053461847/2500000000 : ℝ)*X 1 2+(2240128163/5000000000 : ℝ)*X 2 0+(4213847851/10000000000 : ℝ)*X 2 1+(1053461847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-46666693/250000000 : ℝ)*X 0 0+(5465834651/10000000000 : ℝ)*X 0 1+(2627809209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((10502063/19531250 : ℝ)*X 1 0+(-1988105371/10000000000 : ℝ)*X 1 1+(525561853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344264037/2500000000 : ℝ)*X 2 0+(5255618599/10000000000 : ℝ)*X 2 1+(-79524217/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((206271387/500000000 : ℝ)*X 0 0+(4391257673/10000000000 : ℝ)*X 0 1+(1097814363/2500000000 : ℝ)*X 0 2+(206271387/500000000 : ℝ)*X 1 0+(4391257673/10000000000 : ℝ)*X 1 1+(1097814363/2500000000 : ℝ)*X 1 2+(206271387/500000000 : ℝ)*X 2 0+(4391257673/10000000000 : ℝ)*X 2 1+(1097814363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1445_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6291/10000 : ℝ) ≤ (-266726201181176905614064051845327/424000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29313297/25000000000000 : ℝ)*(upper0) + (3299077/12500000000000 : ℝ)*(lower2) + (14132209/100000000000000 : ℝ)*(lower3) + (207935379/50000000000000 : ℝ)*(upper5) + (3034151815537007/100000000000000 : ℝ)*(major0) + (3034151815537007/100000000000000 : ℝ)*(major1) + (3034151815537007/100000000000000 : ℝ)*(major2) + (1491031791/12500000000000 : ℝ)*(sp1) + (4980985849/100000000000000 : ℝ)*(sp2) + (3396565457/100000000000000 : ℝ)*(sp3) + (1044652854376463/25000000000000 : ℝ)*(sp4) + (1044649872312881/25000000000000 : ℝ)*(sp5) + (2089303218260001/50000000000000 : ℝ)*(sp6) + (1910657857976061/100000000000000 : ℝ)*(sp7) + (955330627270759/50000000000000 : ℝ)*(f.failure) + (1044652854376463/25000000000000 : ℝ)*(f.sum) + (82926334919471/16960000000000000000000000000 : ℝ)*base66 + (12708103669459840109/1696000000000000000000000000000000 : ℝ)*base68 + (11152552312659840109/1696000000000000000000000000000000 : ℝ)*base70 + (5989472575411840109/1696000000000000000000000000000000 : ℝ)*base72 + (344766421003631/16960000000000000000000000000 : ℝ)*base74 + (14542871583443840109/1696000000000000000000000000000000 : ℝ)*base76 + (6863350799763840109/1696000000000000000000000000000000 : ℝ)*base78 + (1936956057036159891/1696000000000000000000000000000000 : ℝ)*base79 + (6721562089169/16960000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6661871/2500000000000000000000 : ℝ)*base89 + (6661871/2500000000000000000000 : ℝ)*base91 + (6661871/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11829/20000 : ℝ) ≤ (250786934015664576024669458774403/424000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75270803/100000000000000 : ℝ)*(lower0) + (94816743/100000000000000 : ℝ)*(upper2) + (10944923/12500000000000 : ℝ)*(lower5) + (1553146997953641/50000000000000 : ℝ)*(major0) + (1553146997953641/50000000000000 : ℝ)*(major1) + (1553146997953641/50000000000000 : ℝ)*(major2) + (1059194273726421/25000000000000 : ℝ)*(sp0) + (2118360552424301/50000000000000 : ℝ)*(sp1) + (4236678700830481/100000000000000 : ℝ)*(sp2) + (978043773320419/50000000000000 : ℝ)*(sp3) + (2966959437/100000000000000 : ℝ)*(sp7) + (483355469/800000000000 : ℝ)*(sp9) + (51411725873/50000000000000 : ℝ)*(sp10) + (4429376543/100000000000000 : ℝ)*(sp12) + (78243620544011/4000000000000 : ℝ)*(f.failure) + (1059195381070557/25000000000000 : ℝ)*(f.sum) + (30034360854313/8480000000000000000000000000 : ℝ)*base66 + (15492401500649141733/848000000000000000000000000000000 : ℝ)*base67 + (6680111145417141733/848000000000000000000000000000000 : ℝ)*base69 + (2581543217609141733/848000000000000000000000000000000 : ℝ)*base71 + (9412938245993/8480000000000000000000000000 : ℝ)*base74 + (6481070996281141733/848000000000000000000000000000000 : ℝ)*base75 + (4913501279769141733/848000000000000000000000000000000 : ℝ)*base77 + (12916706523753141733/848000000000000000000000000000000 : ℝ)*base79 + (218097801847/8480000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1057741/200000000000000000000 : ℝ)*base90 + (1057741/200000000000000000000 : ℝ)*base92 + (1057741/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10067/12500 : ℝ) ≤ (17074204140473443213259687979657/21200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11710901/12500000000000 : ℝ)*(upper1) + (139469819/100000000000000 : ℝ)*(upper2) + (3765047/25000000000000 : ℝ)*(upper3) + (16950989/12500000000000 : ℝ)*(lower5) + (85331840963537/2500000000000 : ℝ)*(major0) + (85331840963537/2500000000000 : ℝ)*(major1) + (85331840963537/2500000000000 : ℝ)*(major2) + (413996263/4000000000000 : ℝ)*(sp1) + (8550756851/20000000000000 : ℝ)*(sp2) + (7765044741/20000000000000 : ℝ)*(sp3) + (4650299798341999/100000000000000 : ℝ)*(sp8) + (145321545263607/3125000000000 : ℝ)*(sp9) + (930051408911549/20000000000000 : ℝ)*(sp10) + (2149362420591977/100000000000000 : ℝ)*(sp11) + (1074700622907841/50000000000000 : ℝ)*(f.failure) + (4650299798341999/100000000000000 : ℝ)*(f.sum) + (2420200309537/424000000000000000000000000 : ℝ)*base66 + (565291283049956781/42400000000000000000000000000000 : ℝ)*base67 + (284914108673156781/42400000000000000000000000000000 : ℝ)*base69 + (178914589107556781/42400000000000000000000000000000 : ℝ)*base71 + (269990543191/424000000000000000000000000 : ℝ)*base73 + (155625067638043219/42400000000000000000000000000000 : ℝ)*base76 + (293416071884443219/42400000000000000000000000000000 : ℝ)*base78 + (221667326791556781/42400000000000000000000000000000 : ℝ)*base79 + (210792191901/84800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9961529/2500000000000000000000 : ℝ)*base89 + (9961529/2500000000000000000000 : ℝ)*base91 + (9961529/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16949/20000 : ℝ) ≤ (-14372260070354497860835044201/16960000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22180759/100000000000000 : ℝ)*(lower0) + (34950551/50000000000000 : ℝ)*(upper3) + (9543317/50000000000000 : ℝ)*(lower4) + (3450942942091553/100000000000000 : ℝ)*(major0) + (3450942942091553/100000000000000 : ℝ)*(major1) + (3450942942091553/100000000000000 : ℝ)*(major2) + (1694340843/100000000000000 : ℝ)*(sp0) + (10368125539/25000000000000 : ℝ)*(sp5) + (5133137631/25000000000000 : ℝ)*(sp7) + (65420583/12500000000000 : ℝ)*(sp8) + (1189252183311321/25000000000000 : ℝ)*(sp12) + (951393895689727/20000000000000 : ℝ)*(sp13) + (594626368868849/12500000000000 : ℝ)*(sp14) + (2173101767172261/100000000000000 : ℝ)*(sp15) + (434624459944557/20000000000000 : ℝ)*(f.failure) + (594626368868849/12500000000000 : ℝ)*(f.sum) + (18631884230369/16960000000000000000000000000 : ℝ)*base66 + (12058604530742515389/1696000000000000000000000000000000 : ℝ)*base67 + (5070033825385484611/1696000000000000000000000000000000 : ℝ)*base70 + (3294792877513484611/1696000000000000000000000000000000 : ℝ)*base72 + (5309740325089/16960000000000000000000000000 : ℝ)*base74 + (1615150096502515389/1696000000000000000000000000000000 : ℝ)*base75 + (12254346775369484611/1696000000000000000000000000000000 : ℝ)*base78 + (14749300361110515389/1696000000000000000000000000000000 : ℝ)*base79 + (25326625446369/16960000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4252933/1000000000000000000000 : ℝ)*base89 + (4252933/1000000000000000000000 : ℝ)*base91 + (4252933/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1445_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11829/20000 : ℝ) else (10067/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16949/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1445_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1445_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11829/20000 : ℝ) else (10067/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16949/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1445_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1445_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1445_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1101/256 : ℝ) ≤ p) (hpb : p ≤ (4405/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79400569/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11829/20000 : ℝ) else (10067/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16949/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1445_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

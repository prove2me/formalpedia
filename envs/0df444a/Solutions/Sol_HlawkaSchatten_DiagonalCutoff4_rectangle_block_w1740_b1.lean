-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1740_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:08.757998+00:00
-- url     : https://prove2.me/submissions/0fe340d8-b2ad-40a5-9f43-ea829df16e33

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
theorem support_rectangle_w1740_s3_0 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1280291149/10000000000 : ℝ)*x 0 + (5510888351/10000000000 : ℝ)*x 1 + (5077836991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1280291149/10000000000 : ℝ)^5615 ≤ (1011831873649/12500000000000 : ℝ)^4591 := by
    have hnat : (1280291149 : ℕ)^5615*12500000000000^4591 ≤ 1011831873649^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280291149 10000000000 1011831873649 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510888351/10000000000 : ℝ)^5615 ≤ (9650112132977/20000000000000 : ℝ)^4591 := by
    have hnat : (5510888351 : ℕ)^5615*20000000000000^4591 ≤ 9650112132977^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510888351 10000000000 9650112132977 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5077836991/10000000000 : ℝ)^5615 ≤ (43654784327133/100000000000000 : ℝ)^4591 := by
    have hnat : (5077836991 : ℕ)^5615*100000000000000^4591 ≤ 43654784327133^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077836991 10000000000 43654784327133 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1280291149/10000000000 : ℝ), (5510888351/10000000000 : ℝ), (5077836991/10000000000 : ℝ)] ![(1011831873649/12500000000000 : ℝ), (9650112132977/20000000000000 : ℝ), (43654784327133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1280291149/10000000000 : ℝ)|^5615 ≤ (1011831873649/12500000000000 : ℝ)^4591
        have hw : |(-1280291149/10000000000 : ℝ)|=(1280291149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510888351/10000000000 : ℝ)|^5615 ≤ (9650112132977/20000000000000 : ℝ)^4591
        have hw : |(5510888351/10000000000 : ℝ)|=(5510888351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5077836991/10000000000 : ℝ)|^5615 ≤ (43654784327133/100000000000000 : ℝ)^4591
        have hw : |(5077836991/10000000000 : ℝ)|=(5077836991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_1 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343329237/10000000000 : ℝ)*x 0 + (-1507240469/10000000000 : ℝ)*x 1 + (1015567441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343329237/10000000000 : ℝ)^5615 ≤ (46462409015863/100000000000000 : ℝ)^4591 := by
    have hnat : (5343329237 : ℕ)^5615*100000000000000^4591 ≤ 46462409015863^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343329237 10000000000 46462409015863 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507240469/10000000000 : ℝ)^5615 ≤ (9882804398223/100000000000000 : ℝ)^4591 := by
    have hnat : (1507240469 : ℕ)^5615*100000000000000^4591 ≤ 9882804398223^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507240469 10000000000 9882804398223 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015567441/2000000000 : ℝ)^5615 ≤ (5456848322159/12500000000000 : ℝ)^4591 := by
    have hnat : (1015567441 : ℕ)^5615*12500000000000^4591 ≤ 5456848322159^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015567441 2000000000 5456848322159 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343329237/10000000000 : ℝ), (-1507240469/10000000000 : ℝ), (1015567441/2000000000 : ℝ)] ![(46462409015863/100000000000000 : ℝ), (9882804398223/100000000000000 : ℝ), (5456848322159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343329237/10000000000 : ℝ)|^5615 ≤ (46462409015863/100000000000000 : ℝ)^4591
        have hw : |(5343329237/10000000000 : ℝ)|=(5343329237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1507240469/10000000000 : ℝ)|^5615 ≤ (9882804398223/100000000000000 : ℝ)^4591
        have hw : |(-1507240469/10000000000 : ℝ)|=(1507240469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015567441/2000000000 : ℝ)|^5615 ≤ (5456848322159/12500000000000 : ℝ)^4591
        have hw : |(1015567441/2000000000 : ℝ)|=(1015567441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_2 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671664601/5000000000 : ℝ)*x 0 + (317364821/625000000 : ℝ)*x 1 + (-376810151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671664601/5000000000 : ℝ)^5615 ≤ (23231204321821/50000000000000 : ℝ)^4591 := by
    have hnat : (2671664601 : ℕ)^5615*50000000000000^4591 ≤ 23231204321821^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671664601 5000000000 23231204321821 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317364821/625000000 : ℝ)^5615 ≤ (545684823147/1250000000000 : ℝ)^4591 := by
    have hnat : (317364821 : ℕ)^5615*1250000000000^4591 ≤ 545684823147^4591*625000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317364821 625000000 545684823147 1250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376810151/2500000000 : ℝ)^5615 ≤ (4941402740419/50000000000000 : ℝ)^4591 := by
    have hnat : (376810151 : ℕ)^5615*50000000000000^4591 ≤ 4941402740419^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376810151 2500000000 4941402740419 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671664601/5000000000 : ℝ), (317364821/625000000 : ℝ), (-376810151/2500000000 : ℝ)] ![(23231204321821/50000000000000 : ℝ), (545684823147/1250000000000 : ℝ), (4941402740419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671664601/5000000000 : ℝ)|^5615 ≤ (23231204321821/50000000000000 : ℝ)^4591
        have hw : |(2671664601/5000000000 : ℝ)|=(2671664601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(317364821/625000000 : ℝ)|^5615 ≤ (545684823147/1250000000000 : ℝ)^4591
        have hw : |(317364821/625000000 : ℝ)|=(317364821/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-376810151/2500000000 : ℝ)|^5615 ≤ (4941402740419/50000000000000 : ℝ)^4591
        have hw : |(-376810151/2500000000 : ℝ)|=(376810151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_3 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (404234119/1000000000 : ℝ)*x 0 + (3392756357/10000000000 : ℝ)*x 1 + (4757633311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404234119/1000000000 : ℝ)^5615 ≤ (2064307544009/6250000000000 : ℝ)^4591 := by
    have hnat : (404234119 : ℕ)^5615*6250000000000^4591 ≤ 2064307544009^4591*1000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404234119 1000000000 2064307544009 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3392756357/10000000000 : ℝ)^5615 ≤ (26659055108919/100000000000000 : ℝ)^4591 := by
    have hnat : (3392756357 : ℕ)^5615*100000000000000^4591 ≤ 26659055108919^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3392756357 10000000000 26659055108919 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4757633311/10000000000 : ℝ)^5615 ≤ (2519501511343/6250000000000 : ℝ)^4591 := by
    have hnat : (4757633311 : ℕ)^5615*6250000000000^4591 ≤ 2519501511343^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4757633311 10000000000 2519501511343 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(404234119/1000000000 : ℝ), (3392756357/10000000000 : ℝ), (4757633311/10000000000 : ℝ)] ![(2064307544009/6250000000000 : ℝ), (26659055108919/100000000000000 : ℝ), (2519501511343/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(404234119/1000000000 : ℝ)|^5615 ≤ (2064307544009/6250000000000 : ℝ)^4591
        have hw : |(404234119/1000000000 : ℝ)|=(404234119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3392756357/10000000000 : ℝ)|^5615 ≤ (26659055108919/100000000000000 : ℝ)^4591
        have hw : |(3392756357/10000000000 : ℝ)|=(3392756357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4757633311/10000000000 : ℝ)|^5615 ≤ (2519501511343/6250000000000 : ℝ)^4591
        have hw : |(4757633311/10000000000 : ℝ)|=(4757633311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_4 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1280663917/10000000000 : ℝ)*x 0 + (1016953049/2000000000 : ℝ)*x 1 + (275190709/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1280663917/10000000000 : ℝ)^5615 ≤ (8097537591911/100000000000000 : ℝ)^4591 := by
    have hnat : (1280663917 : ℕ)^5615*100000000000000^4591 ≤ 8097537591911^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280663917 10000000000 8097537591911 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016953049/2000000000 : ℝ)^5615 ≤ (874552873957/2000000000000 : ℝ)^4591 := by
    have hnat : (1016953049 : ℕ)^5615*2000000000000^4591 ≤ 874552873957^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016953049 2000000000 874552873957 2000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275190709/500000000 : ℝ)^5615 ≤ (24087409349321/50000000000000 : ℝ)^4591 := by
    have hnat : (275190709 : ℕ)^5615*50000000000000^4591 ≤ 24087409349321^4591*500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275190709 500000000 24087409349321 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1280663917/10000000000 : ℝ), (1016953049/2000000000 : ℝ), (275190709/500000000 : ℝ)] ![(8097537591911/100000000000000 : ℝ), (874552873957/2000000000000 : ℝ), (24087409349321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1280663917/10000000000 : ℝ)|^5615 ≤ (8097537591911/100000000000000 : ℝ)^4591
        have hw : |(-1280663917/10000000000 : ℝ)|=(1280663917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016953049/2000000000 : ℝ)|^5615 ≤ (874552873957/2000000000000 : ℝ)^4591
        have hw : |(1016953049/2000000000 : ℝ)|=(1016953049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275190709/500000000 : ℝ)|^5615 ≤ (24087409349321/50000000000000 : ℝ)^4591
        have hw : |(275190709/500000000 : ℝ)|=(275190709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_5 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5228269013/10000000000 : ℝ)*x 0 + (-1081263653/10000000000 : ℝ)*x 1 + (2751907039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5228269013/10000000000 : ℝ)^5615 ≤ (45241713389289/100000000000000 : ℝ)^4591 := by
    have hnat : (5228269013 : ℕ)^5615*100000000000000^4591 ≤ 45241713389289^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228269013 10000000000 45241713389289 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081263653/10000000000 : ℝ)^5615 ≤ (658346898241/10000000000000 : ℝ)^4591 := by
    have hnat : (1081263653 : ℕ)^5615*10000000000000^4591 ≤ 658346898241^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081263653 10000000000 658346898241 10000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751907039/5000000000 : ℝ)^5615 ≤ (24087408803351/50000000000000 : ℝ)^4591 := by
    have hnat : (2751907039 : ℕ)^5615*50000000000000^4591 ≤ 24087408803351^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751907039 5000000000 24087408803351 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5228269013/10000000000 : ℝ), (-1081263653/10000000000 : ℝ), (2751907039/5000000000 : ℝ)] ![(45241713389289/100000000000000 : ℝ), (658346898241/10000000000000 : ℝ), (24087408803351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5228269013/10000000000 : ℝ)|^5615 ≤ (45241713389289/100000000000000 : ℝ)^4591
        have hw : |(5228269013/10000000000 : ℝ)|=(5228269013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081263653/10000000000 : ℝ)|^5615 ≤ (658346898241/10000000000000 : ℝ)^4591
        have hw : |(-1081263653/10000000000 : ℝ)|=(1081263653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751907039/5000000000 : ℝ)|^5615 ≤ (24087408803351/50000000000000 : ℝ)^4591
        have hw : |(2751907039/5000000000 : ℝ)|=(2751907039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_6 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41826153/80000000 : ℝ)*x 0 + (5503813913/10000000000 : ℝ)*x 1 + (-270315933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41826153/80000000 : ℝ)^5615 ≤ (361933716597/800000000000 : ℝ)^4591 := by
    have hnat : (41826153 : ℕ)^5615*800000000000^4591 ≤ 361933716597^4591*80000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41826153 80000000 361933716597 800000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503813913/10000000000 : ℝ)^5615 ≤ (48174815840327/100000000000000 : ℝ)^4591 := by
    have hnat : (5503813913 : ℕ)^5615*100000000000000^4591 ≤ 48174815840327^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503813913 10000000000 48174815840327 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270315933/2500000000 : ℝ)^5615 ≤ (3291734785351/50000000000000 : ℝ)^4591 := by
    have hnat : (270315933 : ℕ)^5615*50000000000000^4591 ≤ 3291734785351^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270315933 2500000000 3291734785351 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41826153/80000000 : ℝ), (5503813913/10000000000 : ℝ), (-270315933/2500000000 : ℝ)] ![(361933716597/800000000000 : ℝ), (48174815840327/100000000000000 : ℝ), (3291734785351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41826153/80000000 : ℝ)|^5615 ≤ (361933716597/800000000000 : ℝ)^4591
        have hw : |(41826153/80000000 : ℝ)|=(41826153/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503813913/10000000000 : ℝ)|^5615 ≤ (48174815840327/100000000000000 : ℝ)^4591
        have hw : |(5503813913/10000000000 : ℝ)|=(5503813913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270315933/2500000000 : ℝ)|^5615 ≤ (3291734785351/50000000000000 : ℝ)^4591
        have hw : |(-270315933/2500000000 : ℝ)|=(270315933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s3_7 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (404351617/1000000000 : ℝ)*x 0 + (947159347/2000000000 : ℝ)*x 1 + (853763291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404351617/1000000000 : ℝ)^5615 ≤ (6608132575211/20000000000000 : ℝ)^4591 := by
    have hnat : (404351617 : ℕ)^5615*20000000000000^4591 ≤ 6608132575211^4591*1000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404351617 1000000000 6608132575211 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947159347/2000000000 : ℝ)^5615 ≤ (10021461849113/25000000000000 : ℝ)^4591 := by
    have hnat : (947159347 : ℕ)^5615*25000000000000^4591 ≤ 10021461849113^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947159347 2000000000 10021461849113 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853763291/2500000000 : ℝ)^5615 ≤ (13436744855397/50000000000000 : ℝ)^4591 := by
    have hnat : (853763291 : ℕ)^5615*50000000000000^4591 ≤ 13436744855397^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853763291 2500000000 13436744855397 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(404351617/1000000000 : ℝ), (947159347/2000000000 : ℝ), (853763291/2500000000 : ℝ)] ![(6608132575211/20000000000000 : ℝ), (10021461849113/25000000000000 : ℝ), (13436744855397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(404351617/1000000000 : ℝ)|^5615 ≤ (6608132575211/20000000000000 : ℝ)^4591
        have hw : |(404351617/1000000000 : ℝ)|=(404351617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(947159347/2000000000 : ℝ)|^5615 ≤ (10021461849113/25000000000000 : ℝ)^4591
        have hw : |(947159347/2000000000 : ℝ)|=(947159347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(853763291/2500000000 : ℝ)|^5615 ≤ (13436744855397/50000000000000 : ℝ)^4591
        have hw : |(853763291/2500000000 : ℝ)|=(853763291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1740_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (89/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4543/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9087/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4449/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9087/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4449/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9087/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4449/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9087/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4449/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9087/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4449/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9087/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4449/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4449/50000 : ℝ) ^ (5599/1024 : ℝ) ≤ (179874210959063/100000000000000000000 : ℝ) := by
    have hpowers : (4449/50000 : ℝ)^5599 ≤ (179874210959063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4449 : ℕ)^5599*100000000000000000000^1024 ≤ 179874210959063^1024*50000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4449 50000 179874210959063 100000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4449/50000 : ℝ)) (X := (179874210959063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9087/50000 : ℝ) ^ (5599/1024 : ℝ) ≤ (8929831095050091/100000000000000000000 : ℝ) := by
    have hpowers : (9087/50000 : ℝ)^5599 ≤ (8929831095050091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9087 : ℕ)^5599*100000000000000000000^1024 ≤ 8929831095050091^1024*50000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9087 50000 8929831095050091 100000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9087/50000 : ℝ)) (X := (8929831095050091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000179874210959063/50000000000000000000 : ℝ) ≤ (10000006579422087/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50000179874210959063/50000000000000000000 : ℝ)^1024 ≤ (10000006579422087/10000000000000000 : ℝ)^5599 := by
      have hnat : (50000179874210959063 : ℕ)^1024*10000000000000000^5599 ≤ 10000006579422087^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000179874210959063 50000000000000000000 10000006579422087 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006579422087/10000000000000000 : ℝ)) (X := (50000179874210959063/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004554852653004577/50000000000000000000 : ℝ) ≤ (1000016660101927/1000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50004554852653004577/50000000000000000000 : ℝ)^1024 ≤ (1000016660101927/1000000000000000 : ℝ)^5599 := by
      have hnat : (50004554852653004577 : ℕ)^1024*1000000000000000^5599 ≤ 1000016660101927^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004554852653004577 50000000000000000000 1000016660101927 1000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000016660101927/1000000000000000 : ℝ)) (X := (50004554852653004577/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008929831095050091/50000000000000000000 : ℝ) ≤ (10000326622616453/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50008929831095050091/50000000000000000000 : ℝ)^1024 ≤ (10000326622616453/10000000000000000 : ℝ)^5599 := by
      have hnat : (50008929831095050091 : ℕ)^1024*10000000000000000^5599 ≤ 10000326622616453^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008929831095050091 50000000000000000000 10000326622616453 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000326622616453/10000000000000000 : ℝ)) (X := (50008929831095050091/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(179874210959063/100000000000000000000 : ℝ) ≤ ((3864883886932325431/3865000000000000000 : ℝ)+2*(160021597183/927600000000000 : ℝ)*(4449/50000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (3864883886932325431/3865000000000000000 : ℝ)+2*(160021597183/927600000000000 : ℝ)*(4449/50000 : ℝ)=(10000006579422087/10000000000000000 : ℝ) by norm_num, show 1+2*(179874210959063/100000000000000000000 : ℝ)=(50000179874210959063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8929831095050091/100000000000000000000 : ℝ)+(179874210959063/100000000000000000000 : ℝ) ≤ ((3864883886932325431/3865000000000000000 : ℝ)+(160021597183/927600000000000 : ℝ)*((9087/50000 : ℝ)+(4449/50000 : ℝ)))^(5599/1024 : ℝ) := by
    rw [show (3864883886932325431/3865000000000000000 : ℝ)+(160021597183/927600000000000 : ℝ)*((9087/50000 : ℝ)+(4449/50000 : ℝ))=(1000016660101927/1000000000000000 : ℝ) by norm_num, show 1+(8929831095050091/100000000000000000000 : ℝ)+(179874210959063/100000000000000000000 : ℝ)=(50004554852653004577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8929831095050091/100000000000000000000 : ℝ) ≤ ((3864883886932325431/3865000000000000000 : ℝ)+2*(160021597183/927600000000000 : ℝ)*(9087/50000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (3864883886932325431/3865000000000000000 : ℝ)+2*(160021597183/927600000000000 : ℝ)*(9087/50000 : ℝ)=(10000326622616453/10000000000000000 : ℝ) by norm_num, show 1+2*(8929831095050091/100000000000000000000 : ℝ)=(50008929831095050091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3864883886932325431/3865000000000000000 : ℝ)*(X 1 0+X 2 0)+(160021597183/927600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (4449/50000 : ℝ)) (hi := (9087/50000 : ℝ)) (c := (3864883886932325431/3865000000000000000 : ℝ)) (alpha := (160021597183/927600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3864883886932325431/3865000000000000000 : ℝ)*(X 0 1+X 2 1)+(160021597183/927600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (4449/50000 : ℝ)) (hi := (9087/50000 : ℝ)) (c := (3864883886932325431/3865000000000000000 : ℝ)) (alpha := (160021597183/927600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3864883886932325431/3865000000000000000 : ℝ)*(X 0 2+X 1 2)+(160021597183/927600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (4449/50000 : ℝ)) (hi := (9087/50000 : ℝ)) (c := (3864883886932325431/3865000000000000000 : ℝ)) (alpha := (160021597183/927600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1280291149/10000000000 : ℝ)*X 0 0+(5510888351/10000000000 : ℝ)*X 0 1+(5077836991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343329237/10000000000 : ℝ)*X 1 0+(-1507240469/10000000000 : ℝ)*X 1 1+(1015567441/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2671664601/5000000000 : ℝ)*X 2 0+(317364821/625000000 : ℝ)*X 2 1+(-376810151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((404234119/1000000000 : ℝ)*X 0 0+(3392756357/10000000000 : ℝ)*X 0 1+(4757633311/10000000000 : ℝ)*X 0 2+(404234119/1000000000 : ℝ)*X 1 0+(3392756357/10000000000 : ℝ)*X 1 1+(4757633311/10000000000 : ℝ)*X 1 2+(404234119/1000000000 : ℝ)*X 2 0+(3392756357/10000000000 : ℝ)*X 2 1+(4757633311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1280663917/10000000000 : ℝ)*X 0 0+(1016953049/2000000000 : ℝ)*X 0 1+(275190709/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5228269013/10000000000 : ℝ)*X 1 0+(-1081263653/10000000000 : ℝ)*X 1 1+(2751907039/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41826153/80000000 : ℝ)*X 2 0+(5503813913/10000000000 : ℝ)*X 2 1+(-270315933/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((404351617/1000000000 : ℝ)*X 0 0+(947159347/2000000000 : ℝ)*X 0 1+(853763291/2500000000 : ℝ)*X 0 2+(404351617/1000000000 : ℝ)*X 1 0+(947159347/2000000000 : ℝ)*X 1 1+(853763291/2500000000 : ℝ)*X 1 2+(404351617/1000000000 : ℝ)*X 2 0+(947159347/2000000000 : ℝ)*X 2 1+(853763291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (509934616361544105572920071/193250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26878501/6250000000000 : ℝ)*(base19) + (206487531/50000000000000 : ℝ)*(base23) + (108451343/100000000000000 : ℝ)*(upper3) + (1044707/100000000000000 : ℝ)*(upper4) + (9422889/25000000000000 : ℝ)*(upper5) + (1520936275585147/100000000000000 : ℝ)*(major0) + (1520936275585147/100000000000000 : ℝ)*(major1) + (1520936275585147/100000000000000 : ℝ)*(major2) + (288649932257007/12500000000000 : ℝ)*(sp0) + (461840522287089/20000000000000 : ℝ)*(sp1) + (5773006571291/250000000000 : ℝ)*(sp2) + (146533588046367/20000000000000 : ℝ)*(sp3) + (716687081/20000000000000 : ℝ)*(sp4) + (296297863/20000000000000 : ℝ)*(sp7) + (14653388434423/2000000000000 : ℝ)*(f.failure) + (1154601520745731/50000000000000 : ℝ)*(f.sum) + (110014618735921/46380000000000000000000000000 : ℝ)*base65 + (1036450980963682571/1159500000000000000000000000000000 : ℝ)*base67 + (365029990316317429/1159500000000000000000000000000000 : ℝ)*base70 + (3467924609805682571/1159500000000000000000000000000000 : ℝ)*base71 + (19512840343201/46380000000000000000000000000 : ℝ)*base73 + (2469894491541817429/1159500000000000000000000000000000 : ℝ)*base76 + (1459147245126817429/1159500000000000000000000000000000 : ℝ)*base78 + (12115905377316817429/1159500000000000000000000000000000 : ℝ)*base80 + (38105257672199/46380000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (720513/100000000000000000000 : ℝ)*base90 + (720513/100000000000000000000 : ℝ)*base92 + (720513/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (679483437041487289138673499/48312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1876037917/100000000000000 : ℝ)*(base19) + (1980447/97656250000 : ℝ)*(base23) + (532824501/100000000000000 : ℝ)*(lower1) + (2777929/1000000000000 : ℝ)*(upper3) + (1100377/2000000000000 : ℝ)*(lower4) + (325098391/100000000000000 : ℝ)*(upper5) + (785872257795907/50000000000000 : ℝ)*(major0) + (785872257795907/50000000000000 : ℝ)*(major1) + (785872257795907/50000000000000 : ℝ)*(major2) + (6267521/3125000000000 : ℝ)*(sp1) + (238634366168339/10000000000000 : ℝ)*(sp4) + (745731745339/31250000000 : ℝ)*(sp5) + (1193170816852831/50000000000000 : ℝ)*(sp6) + (94643112586111/12500000000000 : ℝ)*(sp7) + (94643112586111/12500000000000 : ℝ)*(f.failure) + (238634366168339/10000000000000 : ℝ)*(f.sum) + (45154522722719/23190000000000000000000000000 : ℝ)*base66 + (4198386820843695251/579750000000000000000000000000000 : ℝ)*base67 + (733713509334195251/579750000000000000000000000000000 : ℝ)*base69 + (3724483289172195251/579750000000000000000000000000000 : ℝ)*base71 + (121022912042701/23190000000000000000000000000 : ℝ)*base73 + (3833784039024195251/579750000000000000000000000000000 : ℝ)*base75 + (139559786686304749/579750000000000000000000000000000 : ℝ)*base78 + (2692952978077695251/579750000000000000000000000000000 : ℝ)*base79 + (141656911726861/23190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5313241/625000000000000000000 : ℝ)*base90 + (5313241/625000000000000000000 : ℝ)*base92 + (5313241/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1740_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4543/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1740_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1740_box_0 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438149589/5000000000 : ℝ)*x 0 + (5436428503/10000000000 : ℝ)*x 1 + (1359107129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438149589/5000000000 : ℝ)^5615 ≤ (254557689767/5000000000000 : ℝ)^4591 := by
    have hnat : (438149589 : ℕ)^5615*5000000000000^4591 ≤ 254557689767^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438149589 5000000000 254557689767 5000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436428503/10000000000 : ℝ)^5615 ≤ (5931802877967/12500000000000 : ℝ)^4591 := by
    have hnat : (5436428503 : ℕ)^5615*12500000000000^4591 ≤ 5931802877967^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436428503 10000000000 5931802877967 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359107129/2500000000 : ℝ)^5615 ≤ (47454423162523/100000000000000 : ℝ)^4591 := by
    have hnat : (1359107129 : ℕ)^5615*100000000000000^4591 ≤ 47454423162523^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359107129 2500000000 47454423162523 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438149589/5000000000 : ℝ), (5436428503/10000000000 : ℝ), (1359107129/2500000000 : ℝ)] ![(254557689767/5000000000000 : ℝ), (5931802877967/12500000000000 : ℝ), (47454423162523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438149589/5000000000 : ℝ)|^5615 ≤ (254557689767/5000000000000 : ℝ)^4591
        have hw : |(-438149589/5000000000 : ℝ)|=(438149589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436428503/10000000000 : ℝ)|^5615 ≤ (5931802877967/12500000000000 : ℝ)^4591
        have hw : |(5436428503/10000000000 : ℝ)|=(5436428503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359107129/2500000000 : ℝ)|^5615 ≤ (47454423162523/100000000000000 : ℝ)^4591
        have hw : |(1359107129/2500000000 : ℝ)|=(1359107129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_1 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039033849/2000000000 : ℝ)*x 0 + (-611503047/5000000000 : ℝ)*x 1 + (5436428519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039033849/2000000000 : ℝ)^5615 ≤ (2805728397011/6250000000000 : ℝ)^4591 := by
    have hnat : (1039033849 : ℕ)^5615*6250000000000^4591 ≤ 2805728397011^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039033849 2000000000 2805728397011 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611503047/5000000000 : ℝ)^5615 ≤ (3826961222451/50000000000000 : ℝ)^4591 := by
    have hnat : (611503047 : ℕ)^5615*50000000000000^4591 ≤ 3826961222451^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611503047 5000000000 3826961222451 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436428519/10000000000 : ℝ)^5615 ≤ (47454423194551/100000000000000 : ℝ)^4591 := by
    have hnat : (5436428519 : ℕ)^5615*100000000000000^4591 ≤ 47454423194551^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436428519 10000000000 47454423194551 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039033849/2000000000 : ℝ), (-611503047/5000000000 : ℝ), (5436428519/10000000000 : ℝ)] ![(2805728397011/6250000000000 : ℝ), (3826961222451/50000000000000 : ℝ), (47454423194551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039033849/2000000000 : ℝ)|^5615 ≤ (2805728397011/6250000000000 : ℝ)^4591
        have hw : |(1039033849/2000000000 : ℝ)|=(1039033849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-611503047/5000000000 : ℝ)|^5615 ≤ (3826961222451/50000000000000 : ℝ)^4591
        have hw : |(-611503047/5000000000 : ℝ)|=(611503047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436428519/10000000000 : ℝ)|^5615 ≤ (47454423194551/100000000000000 : ℝ)^4591
        have hw : |(5436428519/10000000000 : ℝ)|=(5436428519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_2 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195169221/10000000000 : ℝ)*x 0 + (2718214271/5000000000 : ℝ)*x 1 + (-611503047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195169221/10000000000 : ℝ)^5615 ≤ (8978330819707/20000000000000 : ℝ)^4591 := by
    have hnat : (5195169221 : ℕ)^5615*20000000000000^4591 ≤ 8978330819707^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195169221 10000000000 8978330819707 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718214271/5000000000 : ℝ)^5615 ≤ (47454423440097/100000000000000 : ℝ)^4591 := by
    have hnat : (2718214271 : ℕ)^5615*100000000000000^4591 ≤ 47454423440097^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718214271 5000000000 47454423440097 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611503047/5000000000 : ℝ)^5615 ≤ (3826961222451/50000000000000 : ℝ)^4591 := by
    have hnat : (611503047 : ℕ)^5615*50000000000000^4591 ≤ 3826961222451^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611503047 5000000000 3826961222451 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195169221/10000000000 : ℝ), (2718214271/5000000000 : ℝ), (-611503047/5000000000 : ℝ)] ![(8978330819707/20000000000000 : ℝ), (47454423440097/100000000000000 : ℝ), (3826961222451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195169221/10000000000 : ℝ)|^5615 ≤ (8978330819707/20000000000000 : ℝ)^4591
        have hw : |(5195169221/10000000000 : ℝ)|=(5195169221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718214271/5000000000 : ℝ)|^5615 ≤ (47454423440097/100000000000000 : ℝ)^4591
        have hw : |(2718214271/5000000000 : ℝ)|=(2718214271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-611503047/5000000000 : ℝ)|^5615 ≤ (3826961222451/50000000000000 : ℝ)^4591
        have hw : |(-611503047/5000000000 : ℝ)|=(611503047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_3 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2285327/5000000 : ℝ)*x 0 + (954687857/2500000000 : ℝ)*x 1 + (3818751409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285327/5000000 : ℝ)^5615 ≤ (19191467765353/50000000000000 : ℝ)^4591 := by
    have hnat : (2285327 : ℕ)^5615*50000000000000^4591 ≤ 19191467765353^4591*5000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285327 5000000 19191467765353 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954687857/2500000000 : ℝ)^5615 ≤ (1232341292727/4000000000000 : ℝ)^4591 := by
    have hnat : (954687857 : ℕ)^5615*4000000000000^4591 ≤ 1232341292727^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954687857 2500000000 1232341292727 4000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3818751409/10000000000 : ℝ)^5615 ≤ (30808532130699/100000000000000 : ℝ)^4591 := by
    have hnat : (3818751409 : ℕ)^5615*100000000000000^4591 ≤ 30808532130699^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3818751409 10000000000 30808532130699 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2285327/5000000 : ℝ), (954687857/2500000000 : ℝ), (3818751409/10000000000 : ℝ)] ![(19191467765353/50000000000000 : ℝ), (1232341292727/4000000000000 : ℝ), (30808532130699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2285327/5000000 : ℝ)|^5615 ≤ (19191467765353/50000000000000 : ℝ)^4591
        have hw : |(2285327/5000000 : ℝ)|=(2285327/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954687857/2500000000 : ℝ)|^5615 ≤ (1232341292727/4000000000000 : ℝ)^4591
        have hw : |(954687857/2500000000 : ℝ)|=(954687857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3818751409/10000000000 : ℝ)|^5615 ≤ (30808532130699/100000000000000 : ℝ)^4591
        have hw : |(3818751409/10000000000 : ℝ)|=(3818751409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_4 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-862364727/5000000000 : ℝ)*x 0 + (5127068623/10000000000 : ℝ)*x 1 + (5127068369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862364727/5000000000 : ℝ)^5615 ≤ (233080177101/2000000000000 : ℝ)^4591 := by
    have hnat : (862364727 : ℕ)^5615*2000000000000^4591 ≤ 233080177101^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862364727 5000000000 233080177101 2000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127068623/10000000000 : ℝ)^5615 ≤ (22086498452029/50000000000000 : ℝ)^4591 := by
    have hnat : (5127068623 : ℕ)^5615*50000000000000^4591 ≤ 22086498452029^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127068623 10000000000 22086498452029 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127068369/10000000000 : ℝ)^5615 ≤ (22086497113789/50000000000000 : ℝ)^4591 := by
    have hnat : (5127068369 : ℕ)^5615*50000000000000^4591 ≤ 22086497113789^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127068369 10000000000 22086497113789 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-862364727/5000000000 : ℝ), (5127068623/10000000000 : ℝ), (5127068369/10000000000 : ℝ)] ![(233080177101/2000000000000 : ℝ), (22086498452029/50000000000000 : ℝ), (22086497113789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-862364727/5000000000 : ℝ)|^5615 ≤ (233080177101/2000000000000 : ℝ)^4591
        have hw : |(-862364727/5000000000 : ℝ)|=(862364727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127068623/10000000000 : ℝ)|^5615 ≤ (22086498452029/50000000000000 : ℝ)^4591
        have hw : |(5127068623/10000000000 : ℝ)|=(5127068623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127068369/10000000000 : ℝ)|^5615 ≤ (22086497113789/50000000000000 : ℝ)^4591
        have hw : |(5127068369/10000000000 : ℝ)|=(5127068369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_5 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135078911/250000000 : ℝ)*x 0 + (-680785253/5000000000 : ℝ)*x 1 + (5127068943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135078911/250000000 : ℝ)^5615 ≤ (47099455829591/100000000000000 : ℝ)^4591 := by
    have hnat : (135078911 : ℕ)^5615*100000000000000^4591 ≤ 47099455829591^4591*250000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135078911 250000000 47099455829591 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680785253/5000000000 : ℝ)^5615 ≤ (4363771938211/50000000000000 : ℝ)^4591 := by
    have hnat : (680785253 : ℕ)^5615*50000000000000^4591 ≤ 4363771938211^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680785253 5000000000 4363771938211 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127068943/10000000000 : ℝ)^5615 ≤ (44173000276001/100000000000000 : ℝ)^4591 := by
    have hnat : (5127068943 : ℕ)^5615*100000000000000^4591 ≤ 44173000276001^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127068943 10000000000 44173000276001 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135078911/250000000 : ℝ), (-680785253/5000000000 : ℝ), (5127068943/10000000000 : ℝ)] ![(47099455829591/100000000000000 : ℝ), (4363771938211/50000000000000 : ℝ), (44173000276001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135078911/250000000 : ℝ)|^5615 ≤ (47099455829591/100000000000000 : ℝ)^4591
        have hw : |(135078911/250000000 : ℝ)|=(135078911/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680785253/5000000000 : ℝ)|^5615 ≤ (4363771938211/50000000000000 : ℝ)^4591
        have hw : |(-680785253/5000000000 : ℝ)|=(680785253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127068943/10000000000 : ℝ)|^5615 ≤ (44173000276001/100000000000000 : ℝ)^4591
        have hw : |(5127068943/10000000000 : ℝ)|=(5127068943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_6 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350789249/2500000000 : ℝ)*x 0 + (1281767087/2500000000 : ℝ)*x 1 + (-1361570551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350789249/2500000000 : ℝ)^5615 ≤ (23549730878641/50000000000000 : ℝ)^4591 := by
    have hnat : (1350789249 : ℕ)^5615*50000000000000^4591 ≤ 23549730878641^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350789249 2500000000 23549730878641 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281767087/2500000000 : ℝ)^5615 ≤ (8834598801259/20000000000000 : ℝ)^4591 := by
    have hnat : (1281767087 : ℕ)^5615*20000000000000^4591 ≤ 8834598801259^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281767087 2500000000 8834598801259 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361570551/10000000000 : ℝ)^5615 ≤ (2181886057301/25000000000000 : ℝ)^4591 := by
    have hnat : (1361570551 : ℕ)^5615*25000000000000^4591 ≤ 2181886057301^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361570551 10000000000 2181886057301 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350789249/2500000000 : ℝ), (1281767087/2500000000 : ℝ), (-1361570551/10000000000 : ℝ)] ![(23549730878641/50000000000000 : ℝ), (8834598801259/20000000000000 : ℝ), (2181886057301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350789249/2500000000 : ℝ)|^5615 ≤ (23549730878641/50000000000000 : ℝ)^4591
        have hw : |(1350789249/2500000000 : ℝ)|=(1350789249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281767087/2500000000 : ℝ)|^5615 ≤ (8834598801259/20000000000000 : ℝ)^4591
        have hw : |(1281767087/2500000000 : ℝ)|=(1281767087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1361570551/10000000000 : ℝ)|^5615 ≤ (2181886057301/25000000000000 : ℝ)^4591
        have hw : |(-1361570551/10000000000 : ℝ)|=(1361570551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_7 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1739598423/5000000000 : ℝ)*x 0 + (4362294991/10000000000 : ℝ)*x 1 + (2181147551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1739598423/5000000000 : ℝ)^5615 ≤ (27492114517193/100000000000000 : ℝ)^4591 := by
    have hnat : (1739598423 : ℕ)^5615*100000000000000^4591 ≤ 27492114517193^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739598423 5000000000 27492114517193 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4362294991/10000000000 : ℝ)^5615 ≤ (1812697108589/5000000000000 : ℝ)^4591 := by
    have hnat : (4362294991 : ℕ)^5615*5000000000000^4591 ≤ 1812697108589^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362294991 10000000000 1812697108589 5000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181147551/5000000000 : ℝ)^5615 ≤ (36253943300031/100000000000000 : ℝ)^4591 := by
    have hnat : (2181147551 : ℕ)^5615*100000000000000^4591 ≤ 36253943300031^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181147551 5000000000 36253943300031 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1739598423/5000000000 : ℝ), (4362294991/10000000000 : ℝ), (2181147551/5000000000 : ℝ)] ![(27492114517193/100000000000000 : ℝ), (1812697108589/5000000000000 : ℝ), (36253943300031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1739598423/5000000000 : ℝ)|^5615 ≤ (27492114517193/100000000000000 : ℝ)^4591
        have hw : |(1739598423/5000000000 : ℝ)|=(1739598423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4362294991/10000000000 : ℝ)|^5615 ≤ (1812697108589/5000000000000 : ℝ)^4591
        have hw : |(4362294991/10000000000 : ℝ)|=(4362294991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2181147551/5000000000 : ℝ)|^5615 ≤ (36253943300031/100000000000000 : ℝ)^4591
        have hw : |(2181147551/5000000000 : ℝ)|=(2181147551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_8 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1540552319/10000000000 : ℝ)*x 0 + (978523233/2000000000 : ℝ)*x 1 + (2750007643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540552319/10000000000 : ℝ)^5615 ≤ (5075299539367/50000000000000 : ℝ)^4591 := by
    have hnat : (1540552319 : ℕ)^5615*50000000000000^4591 ≤ 5075299539367^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540552319 10000000000 5075299539367 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978523233/2000000000 : ℝ)^5615 ≤ (41715247378327/100000000000000 : ℝ)^4591 := by
    have hnat : (978523233 : ℕ)^5615*100000000000000^4591 ≤ 41715247378327^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978523233 2000000000 41715247378327 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750007643/5000000000 : ℝ)^5615 ≤ (48134153534277/100000000000000 : ℝ)^4591 := by
    have hnat : (2750007643 : ℕ)^5615*100000000000000^4591 ≤ 48134153534277^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750007643 5000000000 48134153534277 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1540552319/10000000000 : ℝ), (978523233/2000000000 : ℝ), (2750007643/5000000000 : ℝ)] ![(5075299539367/50000000000000 : ℝ), (41715247378327/100000000000000 : ℝ), (48134153534277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1540552319/10000000000 : ℝ)|^5615 ≤ (5075299539367/50000000000000 : ℝ)^4591
        have hw : |(-1540552319/10000000000 : ℝ)|=(1540552319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(978523233/2000000000 : ℝ)|^5615 ≤ (41715247378327/100000000000000 : ℝ)^4591
        have hw : |(978523233/2000000000 : ℝ)|=(978523233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750007643/5000000000 : ℝ)|^5615 ≤ (48134153534277/100000000000000 : ℝ)^4591
        have hw : |(2750007643/5000000000 : ℝ)|=(2750007643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_9 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152475359/10000000000 : ℝ)*x 0 + (-37281623/312500000 : ℝ)*x 1 + (2750008051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152475359/10000000000 : ℝ)^5615 ≤ (1388776987337/3125000000000 : ℝ)^4591 := by
    have hnat : (5152475359 : ℕ)^5615*3125000000000^4591 ≤ 1388776987337^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152475359 10000000000 1388776987337 3125000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37281623/312500000 : ℝ)^5615 ≤ (1484994823973/20000000000000 : ℝ)^4591 := by
    have hnat : (37281623 : ℕ)^5615*20000000000000^4591 ≤ 1484994823973^4591*312500000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37281623 312500000 1484994823973 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750008051/5000000000 : ℝ)^5615 ≤ (6016770283557/12500000000000 : ℝ)^4591 := by
    have hnat : (2750008051 : ℕ)^5615*12500000000000^4591 ≤ 6016770283557^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750008051 5000000000 6016770283557 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152475359/10000000000 : ℝ), (-37281623/312500000 : ℝ), (2750008051/5000000000 : ℝ)] ![(1388776987337/3125000000000 : ℝ), (1484994823973/20000000000000 : ℝ), (6016770283557/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152475359/10000000000 : ℝ)|^5615 ≤ (1388776987337/3125000000000 : ℝ)^4591
        have hw : |(5152475359/10000000000 : ℝ)|=(5152475359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37281623/312500000 : ℝ)|^5615 ≤ (1484994823973/20000000000000 : ℝ)^4591
        have hw : |(-37281623/312500000 : ℝ)|=(37281623/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750008051/5000000000 : ℝ)|^5615 ≤ (6016770283557/12500000000000 : ℝ)^4591
        have hw : |(2750008051/5000000000 : ℝ)|=(2750008051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_10 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152475257/10000000000 : ℝ)*x 0 + (5500016013/10000000000 : ℝ)*x 1 + (-1193012203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152475257/10000000000 : ℝ)^5615 ≤ (44440862518791/100000000000000 : ℝ)^4591 := by
    have hnat : (5152475257 : ℕ)^5615*100000000000000^4591 ≤ 44440862518791^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152475257 10000000000 44440862518791 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500016013/10000000000 : ℝ)^5615 ≤ (48134161315831/100000000000000 : ℝ)^4591 := by
    have hnat : (5500016013 : ℕ)^5615*100000000000000^4591 ≤ 48134161315831^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500016013 10000000000 48134161315831 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193012203/10000000000 : ℝ)^5615 ≤ (92812201903/1250000000000 : ℝ)^4591 := by
    have hnat : (1193012203 : ℕ)^5615*1250000000000^4591 ≤ 92812201903^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193012203 10000000000 92812201903 1250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152475257/10000000000 : ℝ), (5500016013/10000000000 : ℝ), (-1193012203/10000000000 : ℝ)] ![(44440862518791/100000000000000 : ℝ), (48134161315831/100000000000000 : ℝ), (92812201903/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152475257/10000000000 : ℝ)|^5615 ≤ (44440862518791/100000000000000 : ℝ)^4591
        have hw : |(5152475257/10000000000 : ℝ)|=(5152475257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500016013/10000000000 : ℝ)|^5615 ≤ (48134161315831/100000000000000 : ℝ)^4591
        have hw : |(5500016013/10000000000 : ℝ)|=(5500016013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1193012203/10000000000 : ℝ)|^5615 ≤ (92812201903/1250000000000 : ℝ)^4591
        have hw : |(-1193012203/10000000000 : ℝ)|=(1193012203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_11 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4784309947/10000000000 : ℝ)*x 0 + (3706611079/10000000000 : ℝ)*x 1 + (3706610871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4784309947/10000000000 : ℝ)^5615 ≤ (20294323583953/50000000000000 : ℝ)^4591 := by
    have hnat : (4784309947 : ℕ)^5615*50000000000000^4591 ≤ 20294323583953^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784309947 10000000000 20294323583953 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3706611079/10000000000 : ℝ)^5615 ≤ (29705677430209/100000000000000 : ℝ)^4591 := by
    have hnat : (3706611079 : ℕ)^5615*100000000000000^4591 ≤ 29705677430209^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3706611079 10000000000 29705677430209 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3706610871/10000000000 : ℝ)^5615 ≤ (29705675391439/100000000000000 : ℝ)^4591 := by
    have hnat : (3706610871 : ℕ)^5615*100000000000000^4591 ≤ 29705675391439^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3706610871 10000000000 29705675391439 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4784309947/10000000000 : ℝ), (3706611079/10000000000 : ℝ), (3706610871/10000000000 : ℝ)] ![(20294323583953/50000000000000 : ℝ), (29705677430209/100000000000000 : ℝ), (29705675391439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4784309947/10000000000 : ℝ)|^5615 ≤ (20294323583953/50000000000000 : ℝ)^4591
        have hw : |(4784309947/10000000000 : ℝ)|=(4784309947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3706611079/10000000000 : ℝ)|^5615 ≤ (29705677430209/100000000000000 : ℝ)^4591
        have hw : |(3706611079/10000000000 : ℝ)|=(3706611079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3706610871/10000000000 : ℝ)|^5615 ≤ (29705675391439/100000000000000 : ℝ)^4591
        have hw : |(3706610871/10000000000 : ℝ)|=(3706610871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_12 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-523713351/5000000000 : ℝ)*x 0 + (2828292803/5000000000 : ℝ)*x 1 + (2548307483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523713351/5000000000 : ℝ)^5615 ≤ (1583095232171/25000000000000 : ℝ)^4591 := by
    have hnat : (523713351 : ℕ)^5615*25000000000000^4591 ≤ 1583095232171^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523713351 5000000000 1583095232171 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2828292803/5000000000 : ℝ)^5615 ≤ (498153092083/1000000000000 : ℝ)^4591 := by
    have hnat : (2828292803 : ℕ)^5615*1000000000000^4591 ≤ 498153092083^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2828292803 5000000000 498153092083 1000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548307483/5000000000 : ℝ)^5615 ≤ (21926154924303/50000000000000 : ℝ)^4591 := by
    have hnat : (2548307483 : ℕ)^5615*50000000000000^4591 ≤ 21926154924303^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548307483 5000000000 21926154924303 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523713351/5000000000 : ℝ), (2828292803/5000000000 : ℝ), (2548307483/5000000000 : ℝ)] ![(1583095232171/25000000000000 : ℝ), (498153092083/1000000000000 : ℝ), (21926154924303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523713351/5000000000 : ℝ)|^5615 ≤ (1583095232171/25000000000000 : ℝ)^4591
        have hw : |(-523713351/5000000000 : ℝ)|=(523713351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2828292803/5000000000 : ℝ)|^5615 ≤ (498153092083/1000000000000 : ℝ)^4591
        have hw : |(2828292803/5000000000 : ℝ)|=(2828292803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2548307483/5000000000 : ℝ)|^5615 ≤ (21926154924303/50000000000000 : ℝ)^4591
        have hw : |(2548307483/5000000000 : ℝ)|=(2548307483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_13 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (677962653/1250000000 : ℝ)*x 0 + (-274902231/2000000000 : ℝ)*x 1 + (5096615567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677962653/1250000000 : ℝ)^5615 ≤ (47318583053771/100000000000000 : ℝ)^4591 := by
    have hnat : (677962653 : ℕ)^5615*100000000000000^4591 ≤ 47318583053771^4591*1250000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677962653 1250000000 47318583053771 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274902231/2000000000 : ℝ)^5615 ≤ (8829100764197/100000000000000 : ℝ)^4591 := by
    have hnat : (274902231 : ℕ)^5615*100000000000000^4591 ≤ 8829100764197^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274902231 2000000000 8829100764197 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5096615567/10000000000 : ℝ)^5615 ≤ (43852316173127/100000000000000 : ℝ)^4591 := by
    have hnat : (5096615567 : ℕ)^5615*100000000000000^4591 ≤ 43852316173127^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096615567 10000000000 43852316173127 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677962653/1250000000 : ℝ), (-274902231/2000000000 : ℝ), (5096615567/10000000000 : ℝ)] ![(47318583053771/100000000000000 : ℝ), (8829100764197/100000000000000 : ℝ), (43852316173127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677962653/1250000000 : ℝ)|^5615 ≤ (47318583053771/100000000000000 : ℝ)^4591
        have hw : |(677962653/1250000000 : ℝ)|=(677962653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274902231/2000000000 : ℝ)|^5615 ≤ (8829100764197/100000000000000 : ℝ)^4591
        have hw : |(-274902231/2000000000 : ℝ)|=(274902231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5096615567/10000000000 : ℝ)|^5615 ≤ (43852316173127/100000000000000 : ℝ)^4591
        have hw : |(5096615567/10000000000 : ℝ)|=(5096615567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_14 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5423701039/10000000000 : ℝ)*x 0 + (5096615159/10000000000 : ℝ)*x 1 + (-85906997/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423701039/10000000000 : ℝ)^5615 ≤ (47318581079757/100000000000000 : ℝ)^4591 := by
    have hnat : (5423701039 : ℕ)^5615*100000000000000^4591 ≤ 47318581079757^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423701039 10000000000 47318581079757 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5096615159/10000000000 : ℝ)^5615 ≤ (43852311879609/100000000000000 : ℝ)^4591 := by
    have hnat : (5096615159 : ℕ)^5615*100000000000000^4591 ≤ 43852311879609^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096615159 10000000000 43852311879609 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85906997/625000000 : ℝ)^5615 ≤ (4414553512781/50000000000000 : ℝ)^4591 := by
    have hnat : (85906997 : ℕ)^5615*50000000000000^4591 ≤ 4414553512781^4591*625000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85906997 625000000 4414553512781 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423701039/10000000000 : ℝ), (5096615159/10000000000 : ℝ), (-85906997/625000000 : ℝ)] ![(47318581079757/100000000000000 : ℝ), (43852311879609/100000000000000 : ℝ), (4414553512781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423701039/10000000000 : ℝ)|^5615 ≤ (47318581079757/100000000000000 : ℝ)^4591
        have hw : |(5423701039/10000000000 : ℝ)|=(5423701039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5096615159/10000000000 : ℝ)|^5615 ≤ (43852311879609/100000000000000 : ℝ)^4591
        have hw : |(5096615159/10000000000 : ℝ)|=(5096615159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85906997/625000000 : ℝ)|^5615 ≤ (4414553512781/50000000000000 : ℝ)^4591
        have hw : |(-85906997/625000000 : ℝ)|=(85906997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_box_15 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3366536817/10000000000 : ℝ)*x 0 + (2207793111/5000000000 : ℝ)*x 1 + (4415586103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3366536817/10000000000 : ℝ)^5615 ≤ (26407296458367/100000000000000 : ℝ)^4591 := by
    have hnat : (3366536817 : ℕ)^5615*100000000000000^4591 ≤ 26407296458367^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3366536817 10000000000 26407296458367 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207793111/5000000000 : ℝ)^5615 ≤ (7359270474003/20000000000000 : ℝ)^4591 := by
    have hnat : (2207793111 : ℕ)^5615*20000000000000^4591 ≤ 7359270474003^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207793111 5000000000 7359270474003 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415586103/10000000000 : ℝ)^5615 ≤ (2299771947323/6250000000000 : ℝ)^4591 := by
    have hnat : (4415586103 : ℕ)^5615*6250000000000^4591 ≤ 2299771947323^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415586103 10000000000 2299771947323 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3366536817/10000000000 : ℝ), (2207793111/5000000000 : ℝ), (4415586103/10000000000 : ℝ)] ![(26407296458367/100000000000000 : ℝ), (7359270474003/20000000000000 : ℝ), (2299771947323/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3366536817/10000000000 : ℝ)|^5615 ≤ (26407296458367/100000000000000 : ℝ)^4591
        have hw : |(3366536817/10000000000 : ℝ)|=(3366536817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207793111/5000000000 : ℝ)|^5615 ≤ (7359270474003/20000000000000 : ℝ)^4591
        have hw : |(2207793111/5000000000 : ℝ)|=(2207793111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4415586103/10000000000 : ℝ)|^5615 ≤ (2299771947323/6250000000000 : ℝ)^4591
        have hw : |(4415586103/10000000000 : ℝ)|=(4415586103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1740_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4543/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/1000 : ℝ)*pair X i i ≤ pair X i h) :
    -(17183/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57611/100000 : ℝ) ∧ (20241/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (9271/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4543/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4543/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4543/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4543/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4543/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4543/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (89/1000 : ℝ) ^ (5599/1024 : ℝ) ≤ (180095385468363/100000000000000000000 : ℝ) := by
    have hpowers : (89/1000 : ℝ)^5599 ≤ (180095385468363/100000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^5599*100000000000000000000^1024 ≤ 180095385468363^1024*1000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 1000 180095385468363 100000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/1000 : ℝ)) (X := (180095385468363/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4543/25000 : ℝ) ^ (5599/1024 : ℝ) ≤ (8924459213057859/100000000000000000000 : ℝ) := by
    have hpowers : (4543/25000 : ℝ)^5599 ≤ (8924459213057859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4543 : ℕ)^5599*100000000000000000000^1024 ≤ 8924459213057859^1024*25000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4543 25000 8924459213057859 100000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4543/25000 : ℝ)) (X := (8924459213057859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000180095385468363/50000000000000000000 : ℝ) ≤ (400000263500487/400000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50000180095385468363/50000000000000000000 : ℝ)^1024 ≤ (400000263500487/400000000000000 : ℝ)^5599 := by
      have hnat : (50000180095385468363 : ℕ)^1024*400000000000000^5599 ≤ 400000263500487^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000180095385468363 50000000000000000000 400000263500487 400000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000263500487/400000000000000 : ℝ)) (X := (50000180095385468363/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004552277299263111/50000000000000000000 : ℝ) ≤ (2500041626706273/2500000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50004552277299263111/50000000000000000000 : ℝ)^1024 ≤ (2500041626706273/2500000000000000 : ℝ)^5599 := by
      have hnat : (50004552277299263111 : ℕ)^1024*2500000000000000^5599 ≤ 2500041626706273^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004552277299263111 50000000000000000000 2500041626706273 2500000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500041626706273/2500000000000000 : ℝ)) (X := (50004552277299263111/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008924459213057859/50000000000000000000 : ℝ) ≤ (10000326426138009/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50008924459213057859/50000000000000000000 : ℝ)^1024 ≤ (10000326426138009/10000000000000000 : ℝ)^5599 := by
      have hnat : (50008924459213057859 : ℕ)^1024*10000000000000000^5599 ≤ 10000326426138009^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008924459213057859 50000000000000000000 10000326426138009 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000326426138009/10000000000000000 : ℝ)) (X := (50008924459213057859/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(180095385468363/100000000000000000000 : ℝ) ≤ ((1219963348890039/1220000000000000 : ℝ)+2*(8416805943/48800000000000 : ℝ)*(89/1000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (1219963348890039/1220000000000000 : ℝ)+2*(8416805943/48800000000000 : ℝ)*(89/1000 : ℝ)=(400000263500487/400000000000000 : ℝ) by norm_num, show 1+2*(180095385468363/100000000000000000000 : ℝ)=(50000180095385468363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8924459213057859/100000000000000000000 : ℝ)+(180095385468363/100000000000000000000 : ℝ) ≤ ((1219963348890039/1220000000000000 : ℝ)+(8416805943/48800000000000 : ℝ)*((4543/25000 : ℝ)+(89/1000 : ℝ)))^(5599/1024 : ℝ) := by
    rw [show (1219963348890039/1220000000000000 : ℝ)+(8416805943/48800000000000 : ℝ)*((4543/25000 : ℝ)+(89/1000 : ℝ))=(2500041626706273/2500000000000000 : ℝ) by norm_num, show 1+(8924459213057859/100000000000000000000 : ℝ)+(180095385468363/100000000000000000000 : ℝ)=(50004552277299263111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8924459213057859/100000000000000000000 : ℝ) ≤ ((1219963348890039/1220000000000000 : ℝ)+2*(8416805943/48800000000000 : ℝ)*(4543/25000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (1219963348890039/1220000000000000 : ℝ)+2*(8416805943/48800000000000 : ℝ)*(4543/25000 : ℝ)=(10000326426138009/10000000000000000 : ℝ) by norm_num, show 1+2*(8924459213057859/100000000000000000000 : ℝ)=(50008924459213057859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1219963348890039/1220000000000000 : ℝ)*(X 1 0+X 2 0)+(8416805943/48800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (89/1000 : ℝ)) (hi := (4543/25000 : ℝ)) (c := (1219963348890039/1220000000000000 : ℝ)) (alpha := (8416805943/48800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1219963348890039/1220000000000000 : ℝ)*(X 0 1+X 2 1)+(8416805943/48800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (89/1000 : ℝ)) (hi := (4543/25000 : ℝ)) (c := (1219963348890039/1220000000000000 : ℝ)) (alpha := (8416805943/48800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1219963348890039/1220000000000000 : ℝ)*(X 0 2+X 1 2)+(8416805943/48800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (89/1000 : ℝ)) (hi := (4543/25000 : ℝ)) (c := (1219963348890039/1220000000000000 : ℝ)) (alpha := (8416805943/48800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-438149589/5000000000 : ℝ)*X 0 0+(5436428503/10000000000 : ℝ)*X 0 1+(1359107129/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1039033849/2000000000 : ℝ)*X 1 0+(-611503047/5000000000 : ℝ)*X 1 1+(5436428519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5195169221/10000000000 : ℝ)*X 2 0+(2718214271/5000000000 : ℝ)*X 2 1+(-611503047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2285327/5000000 : ℝ)*X 0 0+(954687857/2500000000 : ℝ)*X 0 1+(3818751409/10000000000 : ℝ)*X 0 2+(2285327/5000000 : ℝ)*X 1 0+(954687857/2500000000 : ℝ)*X 1 1+(3818751409/10000000000 : ℝ)*X 1 2+(2285327/5000000 : ℝ)*X 2 0+(954687857/2500000000 : ℝ)*X 2 1+(3818751409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-862364727/5000000000 : ℝ)*X 0 0+(5127068623/10000000000 : ℝ)*X 0 1+(5127068369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((135078911/250000000 : ℝ)*X 1 0+(-680785253/5000000000 : ℝ)*X 1 1+(5127068943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1350789249/2500000000 : ℝ)*X 2 0+(1281767087/2500000000 : ℝ)*X 2 1+(-1361570551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1739598423/5000000000 : ℝ)*X 0 0+(4362294991/10000000000 : ℝ)*X 0 1+(2181147551/5000000000 : ℝ)*X 0 2+(1739598423/5000000000 : ℝ)*X 1 0+(4362294991/10000000000 : ℝ)*X 1 1+(2181147551/5000000000 : ℝ)*X 1 2+(1739598423/5000000000 : ℝ)*X 2 0+(4362294991/10000000000 : ℝ)*X 2 1+(2181147551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1540552319/10000000000 : ℝ)*X 0 0+(978523233/2000000000 : ℝ)*X 0 1+(2750007643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152475359/10000000000 : ℝ)*X 1 0+(-37281623/312500000 : ℝ)*X 1 1+(2750008051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152475257/10000000000 : ℝ)*X 2 0+(5500016013/10000000000 : ℝ)*X 2 1+(-1193012203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4784309947/10000000000 : ℝ)*X 0 0+(3706611079/10000000000 : ℝ)*X 0 1+(3706610871/10000000000 : ℝ)*X 0 2+(4784309947/10000000000 : ℝ)*X 1 0+(3706611079/10000000000 : ℝ)*X 1 1+(3706610871/10000000000 : ℝ)*X 1 2+(4784309947/10000000000 : ℝ)*X 2 0+(3706611079/10000000000 : ℝ)*X 2 1+(3706610871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-523713351/5000000000 : ℝ)*X 0 0+(2828292803/5000000000 : ℝ)*X 0 1+(2548307483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((677962653/1250000000 : ℝ)*X 1 0+(-274902231/2000000000 : ℝ)*X 1 1+(5096615567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5423701039/10000000000 : ℝ)*X 2 0+(5096615159/10000000000 : ℝ)*X 2 1+(-85906997/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3366536817/10000000000 : ℝ)*X 0 0+(2207793111/5000000000 : ℝ)*X 0 1+(4415586103/10000000000 : ℝ)*X 0 2+(3366536817/10000000000 : ℝ)*X 1 0+(2207793111/5000000000 : ℝ)*X 1 1+(4415586103/10000000000 : ℝ)*X 1 2+(3366536817/10000000000 : ℝ)*X 2 0+(2207793111/5000000000 : ℝ)*X 2 1+(4415586103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-17183/25000 : ℝ) ≤ (-20962497334832227982356865973/30500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15166713/50000000000000 : ℝ)*(lower1) + (48677753/100000000000000 : ℝ)*(lower2) + (2628777/50000000000000 : ℝ)*(lower4) + (3872523/100000000000000 : ℝ)*(lower5) + (507624754671731/50000000000000 : ℝ)*(major0) + (507624754671731/50000000000000 : ℝ)*(major1) + (507624754671731/50000000000000 : ℝ)*(major2) + (420888967/50000000000000 : ℝ)*(sp2) + (1564339629784491/100000000000000 : ℝ)*(sp4) + (782163754780297/50000000000000 : ℝ)*(sp5) + (1564339346992949/100000000000000 : ℝ)*(sp6) + (244534331534429/50000000000000 : ℝ)*(sp7) + (69873299/12500000000000 : ℝ)*(sp8) + (12679210289/100000000000000 : ℝ)*(sp13) + (244534331534429/50000000000000 : ℝ)*(f.failure) + (782170094385441/50000000000000 : ℝ)*(f.sum) + (10010372192013/1220000000000000000000000000 : ℝ)*base65 + (150206690345083/30500000000000000000000000000 : ℝ)*base68 + (63194581003083/30500000000000000000000000000 : ℝ)*base70 + (101888067208417/30500000000000000000000000000 : ℝ)*base71 + (4215675723847/1220000000000000000000000000 : ℝ)*base74 + (17418586280083/30500000000000000000000000000 : ℝ)*base76 + (140264035787417/30500000000000000000000000000 : ℝ)*base77 + (47974286508583/30500000000000000000000000000 : ℝ)*base80 + (1405617135713/1220000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2944501/2500000000000000000000 : ℝ)*base89 + (2944501/2500000000000000000000 : ℝ)*base91 + (2944501/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57611/100000 : ℝ) ≤ (8786130530655727928481674331/15250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6665699/100000000000000 : ℝ)*(upper2) + (27943/800000000000 : ℝ)*(upper3) + (1350053/25000000000000 : ℝ)*(upper4) + (289349/50000000000000 : ℝ)*(upper5) + (283212855886307/25000000000000 : ℝ)*(major0) + (283212855886307/25000000000000 : ℝ)*(major1) + (283212855886307/25000000000000 : ℝ)*(major2) + (1700777937226989/100000000000000 : ℝ)*(sp0) + (1700778017389387/100000000000000 : ℝ)*(sp1) + (850388944852637/50000000000000 : ℝ)*(sp2) + (272860083196299/50000000000000 : ℝ)*(sp3) + (134094969/100000000000000 : ℝ)*(sp6) + (6410857/100000000000000 : ℝ)*(sp9) + (17314651/20000000000000 : ℝ)*(sp12) + (272860083196299/50000000000000 : ℝ)*(f.failure) + (425194505950061/25000000000000 : ℝ)*(f.sum) + (2529607534221/610000000000000000000000000 : ℝ)*base65 + (36447073078999/15250000000000000000000000000 : ℝ)*base67 + (31172315919751/15250000000000000000000000000 : ℝ)*base70 + (212628759389749/15250000000000000000000000000 : ℝ)*base71 + (785922090039/610000000000000000000000000 : ℝ)*base74 + (32538633768001/15250000000000000000000000000 : ℝ)*base76 + (46822384089749/15250000000000000000000000000 : ℝ)*base77 + (114993163053249/15250000000000000000000000000 : ℝ)*base79 + (2761014550769/610000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (18580531/2500000000000000000000 : ℝ)*base89 + (18580531/2500000000000000000000 : ℝ)*base91 + (18580531/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20241/25000 : ℝ) ≤ (49389828253026925359874183371/61000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28374839/100000000000000 : ℝ)*(upper2) + (23261429/50000000000000 : ℝ)*(upper3) + (341111/100000000000000 : ℝ)*(lower5) + (1102138911863571/100000000000000 : ℝ)*(major0) + (1102138911863571/100000000000000 : ℝ)*(major1) + (1102138911863571/100000000000000 : ℝ)*(major2) + (96562351/20000000000000 : ℝ)*(sp0) + (14293742717/100000000000000 : ℝ)*(sp1) + (2895234357/25000000000000 : ℝ)*(sp2) + (57478173/2500000000000 : ℝ)*(sp3) + (1646363109216013/100000000000000 : ℝ)*(sp8) + (411587324571263/25000000000000 : ℝ)*(sp9) + (82317600554517/5000000000000 : ℝ)*(sp10) + (530922955385003/100000000000000 : ℝ)*(sp11) + (530925254511923/100000000000000 : ℝ)*(f.failure) + (205795449003471/12500000000000 : ℝ)*(f.sum) + (6150722740693/2440000000000000000000000000 : ℝ)*base65 + (327956867861703/61000000000000000000000000000 : ℝ)*base68 + (19710770185703/61000000000000000000000000000 : ℝ)*base70 + (344499108148703/61000000000000000000000000000 : ℝ)*base72 + (8657902299427/2440000000000000000000000000 : ℝ)*base74 + (337842431054703/61000000000000000000000000000 : ℝ)*base76 + (468027074883703/61000000000000000000000000000 : ℝ)*base78 + (214422538507703/61000000000000000000000000000 : ℝ)*base80 + (394739958413/2440000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1623013/5000000000000000000000 : ℝ)*base90 + (1623013/5000000000000000000000 : ℝ)*base92 + (1623013/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-9271/10000 : ℝ) ≤ (-28275649434296567106426135897/30500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82666367/100000000000000 : ℝ)*(lower0) + (101627/6250000000000 : ℝ)*(lower1) + (70423419/50000000000000 : ℝ)*(lower4) + (577928050528503/50000000000000 : ℝ)*(major0) + (577928050528503/50000000000000 : ℝ)*(major1) + (577928050528503/50000000000000 : ℝ)*(major2) + (2246242793/50000000000000 : ℝ)*(sp0) + (15420112349/100000000000000 : ℝ)*(sp5) + (67897830201/100000000000000 : ℝ)*(sp6) + (8153680993/100000000000000 : ℝ)*(sp7) + (1785808018606431/100000000000000 : ℝ)*(sp12) + (446449272744917/25000000000000 : ℝ)*(sp13) + (223218076657727/12500000000000 : ℝ)*(sp14) + (69599235806189/12500000000000 : ℝ)*(sp15) + (69600255016313/12500000000000 : ℝ)*(f.failure) + (1785812511092017/100000000000000 : ℝ)*(f.sum) + (5886782971311/1220000000000000000000000000 : ℝ)*base66 + (353120292658079/30500000000000000000000000000 : ℝ)*base68 + (405526157384579/30500000000000000000000000000 : ℝ)*base70 + (323739731199579/30500000000000000000000000000 : ℝ)*base72 + (12797097310131/1220000000000000000000000000 : ℝ)*base74 + (502825797685079/30500000000000000000000000000 : ℝ)*base76 + (313304821953579/30500000000000000000000000000 : ℝ)*base78 + (611344173472079/30500000000000000000000000000 : ℝ)*base80 + (9677359482251/1220000000000000000000000000 : ℝ)*base82 + (1778897/625000000000000000000 : ℝ)*base89 + (1778897/625000000000000000000 : ℝ)*base91 + (1778897/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1740_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4543/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17183/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(57611/100000 : ℝ) else (20241/25000 : ℝ) ≤ X j i ∧ X j i ≤ (9271/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1740_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1740_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17183/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(57611/100000 : ℝ) else (20241/25000 : ℝ) ≤ X j i ∧ X j i ≤ (9271/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1740_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1740_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17183/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(57611/100000 : ℝ) else (20241/25000 : ℝ) ≤ X j i ∧ X j i ≤ (9271/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1740_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

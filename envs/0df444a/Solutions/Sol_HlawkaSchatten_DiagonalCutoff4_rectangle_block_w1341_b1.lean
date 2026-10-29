-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:09.692168+00:00
-- url     : https://prove2.me/submissions/33d28427-0105-419a-a7ea-727575782791

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
theorem support_rectangle_w1341_s3_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-255383179/1250000000 : ℝ)*x 0 + (5427298933/10000000000 : ℝ)*x 1 + (2615599791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255383179/1250000000 : ℝ)^4301 ≤ (497529266639/4000000000000 : ℝ)^3277 := by
    have hnat : (255383179 : ℕ)^4301*4000000000000^3277 ≤ 497529266639^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255383179 1250000000 497529266639 4000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427298933/10000000000 : ℝ)^4301 ≤ (22418999592727/50000000000000 : ℝ)^3277 := by
    have hnat : (5427298933 : ℕ)^4301*50000000000000^3277 ≤ 22418999592727^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427298933 10000000000 22418999592727 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615599791/5000000000 : ℝ)^4301 ≤ (21361884566397/50000000000000 : ℝ)^3277 := by
    have hnat : (2615599791 : ℕ)^4301*50000000000000^3277 ≤ 21361884566397^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615599791 5000000000 21361884566397 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-255383179/1250000000 : ℝ), (5427298933/10000000000 : ℝ), (2615599791/5000000000 : ℝ)] ![(497529266639/4000000000000 : ℝ), (22418999592727/50000000000000 : ℝ), (21361884566397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-255383179/1250000000 : ℝ)|^4301 ≤ (497529266639/4000000000000 : ℝ)^3277
        have hw : |(-255383179/1250000000 : ℝ)|=(255383179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427298933/10000000000 : ℝ)|^4301 ≤ (22418999592727/50000000000000 : ℝ)^3277
        have hw : |(5427298933/10000000000 : ℝ)|=(5427298933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615599791/5000000000 : ℝ)|^4301 ≤ (21361884566397/50000000000000 : ℝ)^3277
        have hw : |(2615599791/5000000000 : ℝ)|=(2615599791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676361307/5000000000 : ℝ)*x 0 + (-1071644749/5000000000 : ℝ)*x 1 + (5231199431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676361307/5000000000 : ℝ)^4301 ≤ (44031098508493/100000000000000 : ℝ)^3277 := by
    have hnat : (2676361307 : ℕ)^4301*100000000000000^3277 ≤ 44031098508493^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676361307 5000000000 44031098508493 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071644749/5000000000 : ℝ)^4301 ≤ (13245133958627/100000000000000 : ℝ)^3277 := by
    have hnat : (1071644749 : ℕ)^4301*100000000000000^3277 ≤ 13245133958627^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071644749 5000000000 13245133958627 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231199431/10000000000 : ℝ)^4301 ≤ (42723767514199/100000000000000 : ℝ)^3277 := by
    have hnat : (5231199431 : ℕ)^4301*100000000000000^3277 ≤ 42723767514199^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231199431 10000000000 42723767514199 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676361307/5000000000 : ℝ), (-1071644749/5000000000 : ℝ), (5231199431/10000000000 : ℝ)] ![(44031098508493/100000000000000 : ℝ), (13245133958627/100000000000000 : ℝ), (42723767514199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676361307/5000000000 : ℝ)|^4301 ≤ (44031098508493/100000000000000 : ℝ)^3277
        have hw : |(2676361307/5000000000 : ℝ)|=(2676361307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071644749/5000000000 : ℝ)|^4301 ≤ (13245133958627/100000000000000 : ℝ)^3277
        have hw : |(-1071644749/5000000000 : ℝ)|=(1071644749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231199431/10000000000 : ℝ)|^4301 ≤ (42723767514199/100000000000000 : ℝ)^3277
        have hw : |(5231199431/10000000000 : ℝ)|=(5231199431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669090333/1250000000 : ℝ)*x 0 + (5231199163/10000000000 : ℝ)*x 1 + (-428657957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669090333/1250000000 : ℝ)^4301 ≤ (44031099048311/100000000000000 : ℝ)^3277 := by
    have hnat : (669090333 : ℕ)^4301*100000000000000^3277 ≤ 44031099048311^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669090333 1250000000 44031099048311 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231199163/10000000000 : ℝ)^4301 ≤ (42723764641461/100000000000000 : ℝ)^3277 := by
    have hnat : (5231199163 : ℕ)^4301*100000000000000^3277 ≤ 42723764641461^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231199163 10000000000 42723764641461 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428657957/2000000000 : ℝ)^4301 ≤ (3311284071613/25000000000000 : ℝ)^3277 := by
    have hnat : (428657957 : ℕ)^4301*25000000000000^3277 ≤ 3311284071613^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428657957 2000000000 3311284071613 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669090333/1250000000 : ℝ), (5231199163/10000000000 : ℝ), (-428657957/2000000000 : ℝ)] ![(44031099048311/100000000000000 : ℝ), (42723764641461/100000000000000 : ℝ), (3311284071613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669090333/1250000000 : ℝ)|^4301 ≤ (44031099048311/100000000000000 : ℝ)^3277
        have hw : |(669090333/1250000000 : ℝ)|=(669090333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231199163/10000000000 : ℝ)|^4301 ≤ (42723764641461/100000000000000 : ℝ)^3277
        have hw : |(5231199163/10000000000 : ℝ)|=(5231199163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428657957/2000000000 : ℝ)|^4301 ≤ (3311284071613/25000000000000 : ℝ)^3277
        have hw : |(-428657957/2000000000 : ℝ)|=(428657957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325810349/10000000000 : ℝ)*x 0 + (32227087/78125000 : ℝ)*x 1 + (4535657081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325810349/10000000000 : ℝ)^4301 ≤ (33292430543547/100000000000000 : ℝ)^3277 := by
    have hnat : (4325810349 : ℕ)^4301*100000000000000^3277 ≤ 33292430543547^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325810349 10000000000 33292430543547 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32227087/78125000 : ℝ)^4301 ≤ (31279553844083/100000000000000 : ℝ)^3277 := by
    have hnat : (32227087 : ℕ)^4301*100000000000000^3277 ≤ 31279553844083^3277*78125000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32227087 78125000 31279553844083 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535657081/10000000000 : ℝ)^4301 ≤ (8857003899627/25000000000000 : ℝ)^3277 := by
    have hnat : (4535657081 : ℕ)^4301*25000000000000^3277 ≤ 8857003899627^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535657081 10000000000 8857003899627 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325810349/10000000000 : ℝ), (32227087/78125000 : ℝ), (4535657081/10000000000 : ℝ)] ![(33292430543547/100000000000000 : ℝ), (31279553844083/100000000000000 : ℝ), (8857003899627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325810349/10000000000 : ℝ)|^4301 ≤ (33292430543547/100000000000000 : ℝ)^3277
        have hw : |(4325810349/10000000000 : ℝ)|=(4325810349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32227087/78125000 : ℝ)|^4301 ≤ (31279553844083/100000000000000 : ℝ)^3277
        have hw : |(32227087/78125000 : ℝ)|=(32227087/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535657081/10000000000 : ℝ)|^4301 ≤ (8857003899627/25000000000000 : ℝ)^3277
        have hw : |(4535657081/10000000000 : ℝ)|=(4535657081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043084701/10000000000 : ℝ)*x 0 + (20437567/39062500 : ℝ)*x 1 + (678309559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043084701/10000000000 : ℝ)^4301 ≤ (155479820419/1250000000000 : ℝ)^3277 := by
    have hnat : (2043084701 : ℕ)^4301*1250000000000^3277 ≤ 155479820419^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043084701 10000000000 155479820419 1250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20437567/39062500 : ℝ)^4301 ≤ (10683133255217/25000000000000 : ℝ)^3277 := by
    have hnat : (20437567 : ℕ)^4301*25000000000000^3277 ≤ 10683133255217^3277*39062500^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20437567 39062500 10683133255217 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678309559/1250000000 : ℝ)^4301 ≤ (44829081328267/100000000000000 : ℝ)^3277 := by
    have hnat : (678309559 : ℕ)^4301*100000000000000^3277 ≤ 44829081328267^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678309559 1250000000 44829081328267 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043084701/10000000000 : ℝ), (20437567/39062500 : ℝ), (678309559/1250000000 : ℝ)] ![(155479820419/1250000000000 : ℝ), (10683133255217/25000000000000 : ℝ), (44829081328267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043084701/10000000000 : ℝ)|^4301 ≤ (155479820419/1250000000000 : ℝ)^3277
        have hw : |(-2043084701/10000000000 : ℝ)|=(2043084701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20437567/39062500 : ℝ)|^4301 ≤ (10683133255217/25000000000000 : ℝ)^3277
        have hw : |(20437567/39062500 : ℝ)|=(20437567/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678309559/1250000000 : ℝ)|^4301 ≤ (44829081328267/100000000000000 : ℝ)^3277
        have hw : |(678309559/1250000000 : ℝ)|=(678309559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651108197/5000000000 : ℝ)*x 0 + (-77920491/400000000 : ℝ)*x 1 + (1356619117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651108197/5000000000 : ℝ)^4301 ≤ (21743310128143/50000000000000 : ℝ)^3277 := by
    have hnat : (2651108197 : ℕ)^4301*50000000000000^3277 ≤ 21743310128143^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651108197 5000000000 21743310128143 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77920491/400000000 : ℝ)^4301 ≤ (11684298439747/100000000000000 : ℝ)^3277 := by
    have hnat : (77920491 : ℕ)^4301*100000000000000^3277 ≤ 11684298439747^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77920491 400000000 11684298439747 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356619117/2500000000 : ℝ)^4301 ≤ (1400908790153/3125000000000 : ℝ)^3277 := by
    have hnat : (1356619117 : ℕ)^4301*3125000000000^3277 ≤ 1400908790153^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356619117 2500000000 1400908790153 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651108197/5000000000 : ℝ), (-77920491/400000000 : ℝ), (1356619117/2500000000 : ℝ)] ![(21743310128143/50000000000000 : ℝ), (11684298439747/100000000000000 : ℝ), (1400908790153/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651108197/5000000000 : ℝ)|^4301 ≤ (21743310128143/50000000000000 : ℝ)^3277
        have hw : |(2651108197/5000000000 : ℝ)|=(2651108197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77920491/400000000 : ℝ)|^4301 ≤ (11684298439747/100000000000000 : ℝ)^3277
        have hw : |(-77920491/400000000 : ℝ)|=(77920491/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356619117/2500000000 : ℝ)|^4301 ≤ (1400908790153/3125000000000 : ℝ)^3277
        have hw : |(1356619117/2500000000 : ℝ)|=(1356619117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302216139/10000000000 : ℝ)*x 0 + (1085295329/2000000000 : ℝ)*x 1 + (-97400619/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302216139/10000000000 : ℝ)^4301 ≤ (10871654377839/25000000000000 : ℝ)^3277 := by
    have hnat : (5302216139 : ℕ)^4301*25000000000000^3277 ≤ 10871654377839^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302216139 10000000000 10871654377839 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085295329/2000000000 : ℝ)^4301 ≤ (44829083204043/100000000000000 : ℝ)^3277 := by
    have hnat : (1085295329 : ℕ)^4301*100000000000000^3277 ≤ 44829083204043^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085295329 2000000000 44829083204043 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97400619/500000000 : ℝ)^4301 ≤ (11684299266343/100000000000000 : ℝ)^3277 := by
    have hnat : (97400619 : ℕ)^4301*100000000000000^3277 ≤ 11684299266343^3277*500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97400619 500000000 11684299266343 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302216139/10000000000 : ℝ), (1085295329/2000000000 : ℝ), (-97400619/500000000 : ℝ)] ![(10871654377839/25000000000000 : ℝ), (44829083204043/100000000000000 : ℝ), (11684299266343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302216139/10000000000 : ℝ)|^4301 ≤ (10871654377839/25000000000000 : ℝ)^3277
        have hw : |(5302216139/10000000000 : ℝ)|=(5302216139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085295329/2000000000 : ℝ)|^4301 ≤ (44829083204043/100000000000000 : ℝ)^3277
        have hw : |(1085295329/2000000000 : ℝ)|=(1085295329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97400619/500000000 : ℝ)|^4301 ≤ (11684299266343/100000000000000 : ℝ)^3277
        have hw : |(-97400619/500000000 : ℝ)|=(97400619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s3_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325850419/10000000000 : ℝ)*x 0 + (4533945271/10000000000 : ℝ)*x 1 + (515848697/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325850419/10000000000 : ℝ)^4301 ≤ (260100275761/781250000000 : ℝ)^3277 := by
    have hnat : (4325850419 : ℕ)^4301*781250000000^3277 ≤ 260100275761^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325850419 10000000000 260100275761 781250000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533945271/10000000000 : ℝ)^4301 ≤ (35410467520221/100000000000000 : ℝ)^3277 := by
    have hnat : (4533945271 : ℕ)^4301*100000000000000^3277 ≤ 35410467520221^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533945271 10000000000 35410467520221 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515848697/1250000000 : ℝ)^4301 ≤ (31296697165261/100000000000000 : ℝ)^3277 := by
    have hnat : (515848697 : ℕ)^4301*100000000000000^3277 ≤ 31296697165261^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515848697 1250000000 31296697165261 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325850419/10000000000 : ℝ), (4533945271/10000000000 : ℝ), (515848697/1250000000 : ℝ)] ![(260100275761/781250000000 : ℝ), (35410467520221/100000000000000 : ℝ), (31296697165261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325850419/10000000000 : ℝ)|^4301 ≤ (260100275761/781250000000 : ℝ)^3277
        have hw : |(4325850419/10000000000 : ℝ)|=(4325850419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533945271/10000000000 : ℝ)|^4301 ≤ (35410467520221/100000000000000 : ℝ)^3277
        have hw : |(4533945271/10000000000 : ℝ)|=(4533945271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515848697/1250000000 : ℝ)|^4301 ≤ (31296697165261/100000000000000 : ℝ)^3277
        have hw : |(515848697/1250000000 : ℝ)|=(515848697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1501/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4027/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1969/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4027/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1969/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4027/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1969/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4027/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1969/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4027/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1969/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4027/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1969/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1969/20000 : ℝ) ^ (1075/256 : ℝ) ≤ (5919602926443743/100000000000000000000 : ℝ) := by
    have hpowers : (1969/20000 : ℝ)^1075 ≤ (5919602926443743/100000000000000000000 : ℝ)^256 := by
      have hnat : (1969 : ℕ)^1075*100000000000000000000^256 ≤ 5919602926443743^256*20000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1969 20000 5919602926443743 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1969/20000 : ℝ)) (X := (5919602926443743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (4027/25000 : ℝ) ^ (1075/256 : ℝ) ≤ (46794445637655143/100000000000000000000 : ℝ) := by
    have hpowers : (4027/25000 : ℝ)^1075 ≤ (46794445637655143/100000000000000000000 : ℝ)^256 := by
      have hnat : (4027 : ℕ)^1075*100000000000000000000^256 ≤ 46794445637655143^256*25000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4027 25000 46794445637655143 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4027/25000 : ℝ)) (X := (46794445637655143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005919602926443743/50000000000000000000 : ℝ) ≤ (10000281925583237/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50005919602926443743/50000000000000000000 : ℝ)^256 ≤ (10000281925583237/10000000000000000 : ℝ)^1075 := by
      have hnat : (50005919602926443743 : ℕ)^256*10000000000000000^1075 ≤ 10000281925583237^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005919602926443743 50000000000000000000 10000281925583237 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281925583237/10000000000000000 : ℝ)) (X := (50005919602926443743/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026357024282049443/50000000000000000000 : ℝ) ≤ (10001255077903751/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50026357024282049443/50000000000000000000 : ℝ)^256 ≤ (10001255077903751/10000000000000000 : ℝ)^1075 := by
      have hnat : (50026357024282049443 : ℕ)^256*10000000000000000^1075 ≤ 10001255077903751^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026357024282049443 50000000000000000000 10001255077903751 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001255077903751/10000000000000000 : ℝ)) (X := (50026357024282049443/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046794445637655143/50000000000000000000 : ℝ) ≤ (2000445646044853/2000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50046794445637655143/50000000000000000000 : ℝ)^256 ≤ (2000445646044853/2000000000000000 : ℝ)^1075 := by
      have hnat : (50046794445637655143 : ℕ)^256*2000000000000000^1075 ≤ 2000445646044853^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046794445637655143 50000000000000000000 2000445646044853 2000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000445646044853/2000000000000000 : ℝ)) (X := (50046794445637655143/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5919602926443743/100000000000000000000 : ℝ) ≤ ((62612604330736892671/62630000000000000000 : ℝ)+2*(486576160257/313150000000000 : ℝ)*(1969/20000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (62612604330736892671/62630000000000000000 : ℝ)+2*(486576160257/313150000000000 : ℝ)*(1969/20000 : ℝ)=(10000281925583237/10000000000000000 : ℝ) by norm_num, show 1+2*(5919602926443743/100000000000000000000 : ℝ)=(50005919602926443743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46794445637655143/100000000000000000000 : ℝ)+(5919602926443743/100000000000000000000 : ℝ) ≤ ((62612604330736892671/62630000000000000000 : ℝ)+(486576160257/313150000000000 : ℝ)*((4027/25000 : ℝ)+(1969/20000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (62612604330736892671/62630000000000000000 : ℝ)+(486576160257/313150000000000 : ℝ)*((4027/25000 : ℝ)+(1969/20000 : ℝ))=(10001255077903751/10000000000000000 : ℝ) by norm_num, show 1+(46794445637655143/100000000000000000000 : ℝ)+(5919602926443743/100000000000000000000 : ℝ)=(50026357024282049443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46794445637655143/100000000000000000000 : ℝ) ≤ ((62612604330736892671/62630000000000000000 : ℝ)+2*(486576160257/313150000000000 : ℝ)*(4027/25000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (62612604330736892671/62630000000000000000 : ℝ)+2*(486576160257/313150000000000 : ℝ)*(4027/25000 : ℝ)=(2000445646044853/2000000000000000 : ℝ) by norm_num, show 1+2*(46794445637655143/100000000000000000000 : ℝ)=(50046794445637655143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62612604330736892671/62630000000000000000 : ℝ)*(X 1 0+X 2 0)+(486576160257/313150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1969/20000 : ℝ)) (hi := (4027/25000 : ℝ)) (c := (62612604330736892671/62630000000000000000 : ℝ)) (alpha := (486576160257/313150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62612604330736892671/62630000000000000000 : ℝ)*(X 0 1+X 2 1)+(486576160257/313150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1969/20000 : ℝ)) (hi := (4027/25000 : ℝ)) (c := (62612604330736892671/62630000000000000000 : ℝ)) (alpha := (486576160257/313150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62612604330736892671/62630000000000000000 : ℝ)*(X 0 2+X 1 2)+(486576160257/313150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1969/20000 : ℝ)) (hi := (4027/25000 : ℝ)) (c := (62612604330736892671/62630000000000000000 : ℝ)) (alpha := (486576160257/313150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-255383179/1250000000 : ℝ)*X 0 0+(5427298933/10000000000 : ℝ)*X 0 1+(2615599791/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676361307/5000000000 : ℝ)*X 1 0+(-1071644749/5000000000 : ℝ)*X 1 1+(5231199431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669090333/1250000000 : ℝ)*X 2 0+(5231199163/10000000000 : ℝ)*X 2 1+(-428657957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325810349/10000000000 : ℝ)*X 0 0+(32227087/78125000 : ℝ)*X 0 1+(4535657081/10000000000 : ℝ)*X 0 2+(4325810349/10000000000 : ℝ)*X 1 0+(32227087/78125000 : ℝ)*X 1 1+(4535657081/10000000000 : ℝ)*X 1 2+(4325810349/10000000000 : ℝ)*X 2 0+(32227087/78125000 : ℝ)*X 2 1+(4535657081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2043084701/10000000000 : ℝ)*X 0 0+(20437567/39062500 : ℝ)*X 0 1+(678309559/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651108197/5000000000 : ℝ)*X 1 0+(-77920491/400000000 : ℝ)*X 1 1+(1356619117/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302216139/10000000000 : ℝ)*X 2 0+(1085295329/2000000000 : ℝ)*X 2 1+(-97400619/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325850419/10000000000 : ℝ)*X 0 0+(4533945271/10000000000 : ℝ)*X 0 1+(515848697/1250000000 : ℝ)*X 0 2+(4325850419/10000000000 : ℝ)*X 1 0+(4533945271/10000000000 : ℝ)*X 1 1+(515848697/1250000000 : ℝ)*X 1 2+(4325850419/10000000000 : ℝ)*X 2 0+(4533945271/10000000000 : ℝ)*X 2 1+(515848697/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2864091086427945040786463097/782875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (360609607/50000000000000 : ℝ)*(base19) + (410258181/50000000000000 : ℝ)*(base23) + (37005339/100000000000000 : ℝ)*(lower2) + (25879429/10000000000000 : ℝ)*(upper3) + (32329513/50000000000000 : ℝ)*(lower4) + (941873899025469/25000000000000 : ℝ)*(major0) + (941873899025469/25000000000000 : ℝ)*(major1) + (941873899025469/25000000000000 : ℝ)*(major2) + (5099464994467917/100000000000000 : ℝ)*(sp0) + (5099464690033453/100000000000000 : ℝ)*(sp1) + (318716536921019/6250000000000 : ℝ)*(sp2) + (2435521154429883/100000000000000 : ℝ)*(sp3) + (1667139/400000000000 : ℝ)*(sp4) + (4504573627/100000000000000 : ℝ)*(sp7) + (243552565900351/10000000000000 : ℝ)*(f.failure) + (5099465411252667/100000000000000 : ℝ)*(f.sum) + (35091259181337/15657500000000000000000000000 : ℝ)*base65 + (11282423509709462301/1565750000000000000000000000000000 : ℝ)*base68 + (4280888675506712301/1565750000000000000000000000000000 : ℝ)*base70 + (2686780833941462301/1565750000000000000000000000000000 : ℝ)*base72 + (6164874773799/31315000000000000000000000000 : ℝ)*base73 + (9468975820896537699/1565750000000000000000000000000000 : ℝ)*base75 + (9856017697136962301/1565750000000000000000000000000000 : ℝ)*base78 + (30194843582632287699/1565750000000000000000000000000000 : ℝ)*base79 + (147733957753239/31315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1057759/500000000000000000000 : ℝ)*base89 + (1057759/500000000000000000000 : ℝ)*base91 + (1057759/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (474402597623527446907307241/195718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546700603/100000000000000 : ℝ)*(base19) + (311722933/100000000000000 : ℝ)*(base23) + (1234879/4000000000000 : ℝ)*(upper3) + (26313039/100000000000000 : ℝ)*(lower4) + (7149099/10000000000000 : ℝ)*(upper5) + (237453879713269/6250000000000 : ℝ)*(major0) + (237453879713269/6250000000000 : ℝ)*(major1) + (237453879713269/6250000000000 : ℝ)*(major2) + (11117838021/100000000000000 : ℝ)*(sp1) + (900415943/12500000000000 : ℝ)*(sp2) + (5142462733282227/100000000000000 : ℝ)*(sp4) + (5142451068743603/100000000000000 : ℝ)*(sp5) + (20569820872927/400000000000 : ℝ)*(sp6) + (1228030668372861/50000000000000 : ℝ)*(sp7) + (1228030668372861/50000000000000 : ℝ)*(f.failure) + (5142462733282227/100000000000000 : ℝ)*(f.sum) + (78367163840091/31315000000000000000000000000 : ℝ)*base65 + (3208686544819473501/391437500000000000000000000000000 : ℝ)*base68 + (2145862823416348501/391437500000000000000000000000000 : ℝ)*base70 + (2360423408867223501/391437500000000000000000000000000 : ℝ)*base72 + (193167891585871/31315000000000000000000000000 : ℝ)*base73 + (4204486306303411001/391437500000000000000000000000000 : ℝ)*base76 + (900962777952848501/391437500000000000000000000000000 : ℝ)*base78 + (5416146232784098501/391437500000000000000000000000000 : ℝ)*base80 + (9932729518761/1957187500000000000000000000 : ℝ)*base81 + (256349/2500000000000000000000 : ℝ)*base89 + (256349/2500000000000000000000 : ℝ)*base91 + (256349/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1341_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1501/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_s4_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204453423/1000000000 : ℝ)*x 0 + (216613347/400000000 : ℝ)*x 1 + (2621100217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204453423/1000000000 : ℝ)^4301 ≤ (3112492322609/25000000000000 : ℝ)^3277 := by
    have hnat : (204453423 : ℕ)^4301*25000000000000^3277 ≤ 3112492322609^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204453423 1000000000 3112492322609 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216613347/400000000 : ℝ)^4301 ≤ (5588537850689/12500000000000 : ℝ)^3277 := by
    have hnat : (216613347 : ℕ)^4301*12500000000000^3277 ≤ 5588537850689^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216613347 400000000 5588537850689 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621100217/5000000000 : ℝ)^4301 ≤ (1071043197289/2500000000000 : ℝ)^3277 := by
    have hnat : (2621100217 : ℕ)^4301*2500000000000^3277 ≤ 1071043197289^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621100217 5000000000 1071043197289 2500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204453423/1000000000 : ℝ), (216613347/400000000 : ℝ), (2621100217/5000000000 : ℝ)] ![(3112492322609/25000000000000 : ℝ), (5588537850689/12500000000000 : ℝ), (1071043197289/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204453423/1000000000 : ℝ)|^4301 ≤ (3112492322609/25000000000000 : ℝ)^3277
        have hw : |(-204453423/1000000000 : ℝ)|=(204453423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216613347/400000000 : ℝ)|^4301 ≤ (5588537850689/12500000000000 : ℝ)^3277
        have hw : |(216613347/400000000 : ℝ)|=(216613347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621100217/5000000000 : ℝ)|^4301 ≤ (1071043197289/2500000000000 : ℝ)^3277
        have hw : |(2621100217/5000000000 : ℝ)|=(2621100217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349673641/10000000000 : ℝ)*x 0 + (-2132796361/10000000000 : ℝ)*x 1 + (1310550063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349673641/10000000000 : ℝ)^4301 ≤ (43998183596011/100000000000000 : ℝ)^3277 := by
    have hnat : (5349673641 : ℕ)^4301*100000000000000^3277 ≤ 43998183596011^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349673641 10000000000 43998183596011 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132796361/10000000000 : ℝ)^4301 ≤ (6580045225893/50000000000000 : ℝ)^3277 := by
    have hnat : (2132796361 : ℕ)^4301*50000000000000^3277 ≤ 6580045225893^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132796361 10000000000 6580045225893 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310550063/2500000000 : ℝ)^4301 ≤ (4284172593939/10000000000000 : ℝ)^3277 := by
    have hnat : (1310550063 : ℕ)^4301*10000000000000^3277 ≤ 4284172593939^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310550063 2500000000 4284172593939 10000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349673641/10000000000 : ℝ), (-2132796361/10000000000 : ℝ), (1310550063/2500000000 : ℝ)] ![(43998183596011/100000000000000 : ℝ), (6580045225893/50000000000000 : ℝ), (4284172593939/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349673641/10000000000 : ℝ)|^4301 ≤ (43998183596011/100000000000000 : ℝ)^3277
        have hw : |(5349673641/10000000000 : ℝ)|=(5349673641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132796361/10000000000 : ℝ)|^4301 ≤ (6580045225893/50000000000000 : ℝ)^3277
        have hw : |(-2132796361/10000000000 : ℝ)|=(2132796361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310550063/2500000000 : ℝ)|^4301 ≤ (4284172593939/10000000000000 : ℝ)^3277
        have hw : |(1310550063/2500000000 : ℝ)|=(1310550063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349674101/10000000000 : ℝ)*x 0 + (1310549977/2500000000 : ℝ)*x 1 + (-533199051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349674101/10000000000 : ℝ)^4301 ≤ (43998188561457/100000000000000 : ℝ)^3277 := by
    have hnat : (5349674101 : ℕ)^4301*100000000000000^3277 ≤ 43998188561457^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349674101 10000000000 43998188561457 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310549977/2500000000 : ℝ)^4301 ≤ (42841722249573/100000000000000 : ℝ)^3277 := by
    have hnat : (1310549977 : ℕ)^4301*100000000000000^3277 ≤ 42841722249573^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310549977 2500000000 42841722249573 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533199051/2500000000 : ℝ)^4301 ≤ (1645011147541/12500000000000 : ℝ)^3277 := by
    have hnat : (533199051 : ℕ)^4301*12500000000000^3277 ≤ 1645011147541^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533199051 2500000000 1645011147541 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349674101/10000000000 : ℝ), (1310549977/2500000000 : ℝ), (-533199051/2500000000 : ℝ)] ![(43998188561457/100000000000000 : ℝ), (42841722249573/100000000000000 : ℝ), (1645011147541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349674101/10000000000 : ℝ)|^4301 ≤ (43998188561457/100000000000000 : ℝ)^3277
        have hw : |(5349674101/10000000000 : ℝ)|=(5349674101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310549977/2500000000 : ℝ)|^4301 ≤ (42841722249573/100000000000000 : ℝ)^3277
        have hw : |(1310549977/2500000000 : ℝ)|=(1310549977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533199051/2500000000 : ℝ)|^4301 ≤ (1645011147541/12500000000000 : ℝ)^3277
        have hw : |(-533199051/2500000000 : ℝ)|=(533199051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216335141/500000000 : ℝ)*x 0 + (4148999119/10000000000 : ℝ)*x 1 + (225575187/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216335141/500000000 : ℝ)^4301 ≤ (8325361455471/25000000000000 : ℝ)^3277 := by
    have hnat : (216335141 : ℕ)^4301*25000000000000^3277 ≤ 8325361455471^3277*500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216335141 500000000 8325361455471 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148999119/10000000000 : ℝ)^4301 ≤ (31517947217611/100000000000000 : ℝ)^3277 := by
    have hnat : (4148999119 : ℕ)^4301*100000000000000^3277 ≤ 31517947217611^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148999119 10000000000 31517947217611 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225575187/500000000 : ℝ)^4301 ≤ (8795151734603/25000000000000 : ℝ)^3277 := by
    have hnat : (225575187 : ℕ)^4301*25000000000000^3277 ≤ 8795151734603^3277*500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225575187 500000000 8795151734603 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216335141/500000000 : ℝ), (4148999119/10000000000 : ℝ), (225575187/500000000 : ℝ)] ![(8325361455471/25000000000000 : ℝ), (31517947217611/100000000000000 : ℝ), (8795151734603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216335141/500000000 : ℝ)|^4301 ≤ (8325361455471/25000000000000 : ℝ)^3277
        have hw : |(216335141/500000000 : ℝ)|=(216335141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148999119/10000000000 : ℝ)|^4301 ≤ (31517947217611/100000000000000 : ℝ)^3277
        have hw : |(4148999119/10000000000 : ℝ)|=(4148999119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225575187/500000000 : ℝ)|^4301 ≤ (8795151734603/25000000000000 : ℝ)^3277
        have hw : |(225575187/500000000 : ℝ)|=(225575187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204454793/1000000000 : ℝ)*x 0 + (5242838023/10000000000 : ℝ)*x 1 + (2707346199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204454793/1000000000 : ℝ)^4301 ≤ (1245007878383/10000000000000 : ℝ)^3277 := by
    have hnat : (204454793 : ℕ)^4301*10000000000000^3277 ≤ 1245007878383^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204454793 1000000000 1245007878383 10000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242838023/10000000000 : ℝ)^4301 ≤ (42848566936003/100000000000000 : ℝ)^3277 := by
    have hnat : (5242838023 : ℕ)^4301*100000000000000^3277 ≤ 42848566936003^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242838023 10000000000 42848566936003 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707346199/5000000000 : ℝ)^4301 ≤ (44701354265037/100000000000000 : ℝ)^3277 := by
    have hnat : (2707346199 : ℕ)^4301*100000000000000^3277 ≤ 44701354265037^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707346199 5000000000 44701354265037 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204454793/1000000000 : ℝ), (5242838023/10000000000 : ℝ), (2707346199/5000000000 : ℝ)] ![(1245007878383/10000000000000 : ℝ), (42848566936003/100000000000000 : ℝ), (44701354265037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204454793/1000000000 : ℝ)|^4301 ≤ (1245007878383/10000000000000 : ℝ)^3277
        have hw : |(-204454793/1000000000 : ℝ)|=(204454793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242838023/10000000000 : ℝ)|^4301 ≤ (42848566936003/100000000000000 : ℝ)^3277
        have hw : |(5242838023/10000000000 : ℝ)|=(5242838023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707346199/5000000000 : ℝ)|^4301 ≤ (44701354265037/100000000000000 : ℝ)^3277
        have hw : |(2707346199/5000000000 : ℝ)|=(2707346199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305083539/10000000000 : ℝ)*x 0 + (-1960304361/10000000000 : ℝ)*x 1 + (169209133/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305083539/10000000000 : ℝ)^4301 ≤ (10879371514321/25000000000000 : ℝ)^3277 := by
    have hnat : (5305083539 : ℕ)^4301*25000000000000^3277 ≤ 10879371514321^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305083539 10000000000 10879371514321 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960304361/10000000000 : ℝ)^4301 ≤ (2356232241793/20000000000000 : ℝ)^3277 := by
    have hnat : (1960304361 : ℕ)^4301*20000000000000^3277 ≤ 2356232241793^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960304361 10000000000 2356232241793 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169209133/312500000 : ℝ)^4301 ≤ (11175338181607/25000000000000 : ℝ)^3277 := by
    have hnat : (169209133 : ℕ)^4301*25000000000000^3277 ≤ 11175338181607^3277*312500000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169209133 312500000 11175338181607 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305083539/10000000000 : ℝ), (-1960304361/10000000000 : ℝ), (169209133/312500000 : ℝ)] ![(10879371514321/25000000000000 : ℝ), (2356232241793/20000000000000 : ℝ), (11175338181607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305083539/10000000000 : ℝ)|^4301 ≤ (10879371514321/25000000000000 : ℝ)^3277
        have hw : |(5305083539/10000000000 : ℝ)|=(5305083539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960304361/10000000000 : ℝ)|^4301 ≤ (2356232241793/20000000000000 : ℝ)^3277
        have hw : |(-1960304361/10000000000 : ℝ)|=(1960304361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169209133/312500000 : ℝ)|^4301 ≤ (11175338181607/25000000000000 : ℝ)^3277
        have hw : |(169209133/312500000 : ℝ)|=(169209133/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26525417/50000000 : ℝ)*x 0 + (1353673081/2500000000 : ℝ)*x 1 + (-245038057/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26525417/50000000 : ℝ)^4301 ≤ (1740699382431/4000000000000 : ℝ)^3277 := by
    have hnat : (26525417 : ℕ)^4301*4000000000000^3277 ≤ 1740699382431^3277*50000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26525417 50000000 1740699382431 4000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353673081/2500000000 : ℝ)^4301 ≤ (44701353463227/100000000000000 : ℝ)^3277 := by
    have hnat : (1353673081 : ℕ)^4301*100000000000000^3277 ≤ 44701353463227^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353673081 2500000000 44701353463227 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245038057/1250000000 : ℝ)^4301 ≤ (11781161958309/100000000000000 : ℝ)^3277 := by
    have hnat : (245038057 : ℕ)^4301*100000000000000^3277 ≤ 11781161958309^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245038057 1250000000 11781161958309 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26525417/50000000 : ℝ), (1353673081/2500000000 : ℝ), (-245038057/1250000000 : ℝ)] ![(1740699382431/4000000000000 : ℝ), (44701353463227/100000000000000 : ℝ), (11781161958309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26525417/50000000 : ℝ)|^4301 ≤ (1740699382431/4000000000000 : ℝ)^3277
        have hw : |(26525417/50000000 : ℝ)|=(26525417/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353673081/2500000000 : ℝ)|^4301 ≤ (44701353463227/100000000000000 : ℝ)^3277
        have hw : |(1353673081/2500000000 : ℝ)|=(1353673081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245038057/1250000000 : ℝ)|^4301 ≤ (11781161958309/100000000000000 : ℝ)^3277
        have hw : |(-245038057/1250000000 : ℝ)|=(245038057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s4_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270420639/625000000 : ℝ)*x 0 + (4510168057/10000000000 : ℝ)*x 1 + (518792791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270420639/625000000 : ℝ)^4301 ≤ (666034453041/2000000000000 : ℝ)^3277 := by
    have hnat : (270420639 : ℕ)^4301*2000000000000^3277 ≤ 666034453041^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270420639 625000000 666034453041 2000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510168057/10000000000 : ℝ)^4301 ≤ (35166937259463/100000000000000 : ℝ)^3277 := by
    have hnat : (4510168057 : ℕ)^4301*100000000000000^3277 ≤ 35166937259463^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510168057 10000000000 35166937259463 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518792791/1250000000 : ℝ)^4301 ≤ (7882835017951/25000000000000 : ℝ)^3277 := by
    have hnat : (518792791 : ℕ)^4301*25000000000000^3277 ≤ 7882835017951^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518792791 1250000000 7882835017951 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270420639/625000000 : ℝ), (4510168057/10000000000 : ℝ), (518792791/1250000000 : ℝ)] ![(666034453041/2000000000000 : ℝ), (35166937259463/100000000000000 : ℝ), (7882835017951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270420639/625000000 : ℝ)|^4301 ≤ (666034453041/2000000000000 : ℝ)^3277
        have hw : |(270420639/625000000 : ℝ)|=(270420639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510168057/10000000000 : ℝ)|^4301 ≤ (35166937259463/100000000000000 : ℝ)^3277
        have hw : |(4510168057/10000000000 : ℝ)|=(4510168057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518792791/1250000000 : ℝ)|^4301 ≤ (7882835017951/25000000000000 : ℝ)^3277
        have hw : |(518792791/1250000000 : ℝ)|=(518792791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1501/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1387/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1501/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1501/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1501/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1501/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1501/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1501/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10861/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (8941418950275321/100000000000000000000 : ℝ) := by
    have hpowers : (10861/100000 : ℝ)^1075 ≤ (8941418950275321/100000000000000000000 : ℝ)^256 := by
      have hnat : (10861 : ℕ)^1075*100000000000000000000^256 ≤ 8941418950275321^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10861 100000 8941418950275321 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10861/100000 : ℝ)) (X := (8941418950275321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1501/10000 : ℝ) ^ (1075/256 : ℝ) ≤ (8697258305881019/25000000000000000000 : ℝ) := by
    have hpowers : (1501/10000 : ℝ)^1075 ≤ (8697258305881019/25000000000000000000 : ℝ)^256 := by
      have hnat : (1501 : ℕ)^1075*25000000000000000000^256 ≤ 8697258305881019^256*10000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1501 10000 8697258305881019 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1501/10000 : ℝ)) (X := (8697258305881019/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008941418950275321/50000000000000000000 : ℝ) ≤ (10000425832062911/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50008941418950275321/50000000000000000000 : ℝ)^256 ≤ (10000425832062911/10000000000000000 : ℝ)^1075 := by
      have hnat : (50008941418950275321 : ℕ)^256*10000000000000000^1075 ≤ 10000425832062911^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008941418950275321 50000000000000000000 10000425832062911 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000425832062911/10000000000000000 : ℝ)) (X := (50008941418950275321/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043730452173799397/100000000000000000000 : ℝ) ≤ (2500260305380111/2500000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (100043730452173799397/100000000000000000000 : ℝ)^256 ≤ (2500260305380111/2500000000000000 : ℝ)^1075 := by
      have hnat : (100043730452173799397 : ℕ)^256*2500000000000000^1075 ≤ 2500260305380111^1075*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043730452173799397 100000000000000000000 2500260305380111 2500000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500260305380111/2500000000000000 : ℝ)) (X := (100043730452173799397/100000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508697258305881019/12500000000000000000 : ℝ) ≤ (10001656610977977/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12508697258305881019/12500000000000000000 : ℝ)^256 ≤ (10001656610977977/10000000000000000 : ℝ)^1075 := by
      have hnat : (12508697258305881019 : ℕ)^256*10000000000000000^1075 ≤ 10001656610977977^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508697258305881019 12500000000000000000 10001656610977977 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001656610977977/10000000000000000 : ℝ)) (X := (12508697258305881019/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8941418950275321/100000000000000000000 : ℝ) ≤ ((41478399287432485913/41490000000000000000 : ℝ)+2*(615389457533/414900000000000 : ℝ)*(10861/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (41478399287432485913/41490000000000000000 : ℝ)+2*(615389457533/414900000000000 : ℝ)*(10861/100000 : ℝ)=(10000425832062911/10000000000000000 : ℝ) by norm_num, show 1+2*(8941418950275321/100000000000000000000 : ℝ)=(50008941418950275321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8697258305881019/25000000000000000000 : ℝ)+(8941418950275321/100000000000000000000 : ℝ) ≤ ((41478399287432485913/41490000000000000000 : ℝ)+(615389457533/414900000000000 : ℝ)*((1501/10000 : ℝ)+(10861/100000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (41478399287432485913/41490000000000000000 : ℝ)+(615389457533/414900000000000 : ℝ)*((1501/10000 : ℝ)+(10861/100000 : ℝ))=(2500260305380111/2500000000000000 : ℝ) by norm_num, show 1+(8697258305881019/25000000000000000000 : ℝ)+(8941418950275321/100000000000000000000 : ℝ)=(100043730452173799397/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8697258305881019/25000000000000000000 : ℝ) ≤ ((41478399287432485913/41490000000000000000 : ℝ)+2*(615389457533/414900000000000 : ℝ)*(1501/10000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (41478399287432485913/41490000000000000000 : ℝ)+2*(615389457533/414900000000000 : ℝ)*(1501/10000 : ℝ)=(10001656610977977/10000000000000000 : ℝ) by norm_num, show 1+2*(8697258305881019/25000000000000000000 : ℝ)=(12508697258305881019/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41478399287432485913/41490000000000000000 : ℝ)*(X 1 0+X 2 0)+(615389457533/414900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (1501/10000 : ℝ)) (c := (41478399287432485913/41490000000000000000 : ℝ)) (alpha := (615389457533/414900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41478399287432485913/41490000000000000000 : ℝ)*(X 0 1+X 2 1)+(615389457533/414900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (1501/10000 : ℝ)) (c := (41478399287432485913/41490000000000000000 : ℝ)) (alpha := (615389457533/414900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41478399287432485913/41490000000000000000 : ℝ)*(X 0 2+X 1 2)+(615389457533/414900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (1501/10000 : ℝ)) (c := (41478399287432485913/41490000000000000000 : ℝ)) (alpha := (615389457533/414900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-204453423/1000000000 : ℝ)*X 0 0+(216613347/400000000 : ℝ)*X 0 1+(2621100217/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349673641/10000000000 : ℝ)*X 1 0+(-2132796361/10000000000 : ℝ)*X 1 1+(1310550063/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349674101/10000000000 : ℝ)*X 2 0+(1310549977/2500000000 : ℝ)*X 2 1+(-533199051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216335141/500000000 : ℝ)*X 0 0+(4148999119/10000000000 : ℝ)*X 0 1+(225575187/500000000 : ℝ)*X 0 2+(216335141/500000000 : ℝ)*X 1 0+(4148999119/10000000000 : ℝ)*X 1 1+(225575187/500000000 : ℝ)*X 1 2+(216335141/500000000 : ℝ)*X 2 0+(4148999119/10000000000 : ℝ)*X 2 1+(225575187/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204454793/1000000000 : ℝ)*X 0 0+(5242838023/10000000000 : ℝ)*X 0 1+(2707346199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305083539/10000000000 : ℝ)*X 1 0+(-1960304361/10000000000 : ℝ)*X 1 1+(169209133/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26525417/50000000 : ℝ)*X 2 0+(1353673081/2500000000 : ℝ)*X 2 1+(-245038057/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270420639/625000000 : ℝ)*X 0 0+(4510168057/10000000000 : ℝ)*X 0 1+(518792791/1250000000 : ℝ)*X 0 2+(270420639/625000000 : ℝ)*X 1 0+(4510168057/10000000000 : ℝ)*X 1 1+(518792791/1250000000 : ℝ)*X 1 2+(270420639/625000000 : ℝ)*X 2 0+(4510168057/10000000000 : ℝ)*X 2 1+(518792791/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1310497501610297333226011903/691500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (857331991/100000000000000 : ℝ)*(base19) + (963864687/100000000000000 : ℝ)*(base23) + (57666679/20000000000000 : ℝ)*(lower2) + (7021633/50000000000000 : ℝ)*(upper3) + (79632453/100000000000000 : ℝ)*(lower4) + (4267264516917769/100000000000000 : ℝ)*(major0) + (4267264516917769/100000000000000 : ℝ)*(major1) + (4267264516917769/100000000000000 : ℝ)*(major2) + (5775907222038421/100000000000000 : ℝ)*(sp0) + (360995193988947/6250000000000 : ℝ)*(sp1) + (721990374661307/12500000000000 : ℝ)*(sp2) + (689648366604141/25000000000000 : ℝ)*(sp3) + (16739116721/100000000000000 : ℝ)*(sp4) + (2308618419/20000000000000 : ℝ)*(sp7) + (1379302504754329/50000000000000 : ℝ)*(f.failure) + (5775923961155143/100000000000000 : ℝ)*(f.sum) + (124759390939123/20745000000000000000000000000 : ℝ)*base66 + (15644709875598588097/4149000000000000000000000000000000 : ℝ)*base67 + (57412881539948411903/4149000000000000000000000000000000 : ℝ)*base70 + (26176116978051588097/4149000000000000000000000000000000 : ℝ)*base71 + (38327582118539/10372500000000000000000000000 : ℝ)*base74 + (41702994390116411903/4149000000000000000000000000000000 : ℝ)*base76 + (13489538682075588097/4149000000000000000000000000000000 : ℝ)*base77 + (3141829940388588097/4149000000000000000000000000000000 : ℝ)*base79 + (111804472350643/20745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (7437639/2500000000000000000000 : ℝ)*base90 + (7437639/2500000000000000000000 : ℝ)*base92 + (7437639/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3914246022698773587513515203/345750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1106159597/50000000000000 : ℝ)*(base19) + (2184051307/100000000000000 : ℝ)*(base23) + (27561421/12500000000000 : ℝ)*(upper3) + (39437023/50000000000000 : ℝ)*(lower4) + (72101889/25000000000000 : ℝ)*(upper5) + (2149500218106331/50000000000000 : ℝ)*(major0) + (2149500218106331/50000000000000 : ℝ)*(major1) + (2149500218106331/50000000000000 : ℝ)*(major2) + (41236518849/100000000000000 : ℝ)*(sp1) + (958081243/2500000000000 : ℝ)*(sp2) + (727359945444627/12500000000000 : ℝ)*(sp4) + (5818836114718973/100000000000000 : ℝ)*(sp5) + (581883905625599/10000000000000 : ℝ)*(sp6) + (694780232875161/25000000000000 : ℝ)*(sp7) + (694780232875161/25000000000000 : ℝ)*(f.failure) + (727359945444627/12500000000000 : ℝ)*(f.sum) + (57448722633863/10372500000000000000000000000 : ℝ)*base65 + (7769644923173915203/2074500000000000000000000000000000 : ℝ)*base67 + (10160000351364084797/2074500000000000000000000000000000 : ℝ)*base70 + (7891919031108084797/2074500000000000000000000000000000 : ℝ)*base72 + (15511475466647/2593125000000000000000000000 : ℝ)*base73 + (30966632991869915203/2074500000000000000000000000000000 : ℝ)*base75 + (7001591477376084797/2074500000000000000000000000000000 : ℝ)*base78 + (15182264503650084797/2074500000000000000000000000000000 : ℝ)*base80 + (35166336241703/10372500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1642951/1250000000000000000000 : ℝ)*base90 + (1642951/1250000000000000000000 : ℝ)*base92 + (1642951/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1341_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1501/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_s5_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63899539/312500000 : ℝ)*x 0 + (5413151449/10000000000 : ℝ)*x 1 + (524421763/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63899539/312500000 : ℝ)^4301 ≤ (1556496939691/12500000000000 : ℝ)^3277 := by
    have hnat : (63899539 : ℕ)^4301*12500000000000^3277 ≤ 1556496939691^3277*312500000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63899539 312500000 1556496939691 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413151449/10000000000 : ℝ)^4301 ≤ (2792791150193/6250000000000 : ℝ)^3277 := by
    have hnat : (5413151449 : ℕ)^4301*6250000000000^3277 ≤ 2792791150193^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413151449 10000000000 2792791150193 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524421763/1000000000 : ℝ)^4301 ≤ (21431683031643/50000000000000 : ℝ)^3277 := by
    have hnat : (524421763 : ℕ)^4301*50000000000000^3277 ≤ 21431683031643^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524421763 1000000000 21431683031643 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63899539/312500000 : ℝ), (5413151449/10000000000 : ℝ), (524421763/1000000000 : ℝ)] ![(1556496939691/12500000000000 : ℝ), (2792791150193/6250000000000 : ℝ), (21431683031643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63899539/312500000 : ℝ)|^4301 ≤ (1556496939691/12500000000000 : ℝ)^3277
        have hw : |(-63899539/312500000 : ℝ)|=(63899539/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413151449/10000000000 : ℝ)|^4301 ≤ (2792791150193/6250000000000 : ℝ)^3277
        have hw : |(5413151449/10000000000 : ℝ)|=(5413151449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524421763/1000000000 : ℝ)|^4301 ≤ (21431683031643/50000000000000 : ℝ)^3277
        have hw : |(524421763/1000000000 : ℝ)|=(524421763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349116839/10000000000 : ℝ)*x 0 + (-85234637/400000000 : ℝ)*x 1 + (524421777/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349116839/10000000000 : ℝ)^4301 ≤ (2749510832701/6250000000000 : ℝ)^3277 := by
    have hnat : (5349116839 : ℕ)^4301*6250000000000^3277 ≤ 2749510832701^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349116839 10000000000 2749510832701 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85234637/400000000 : ℝ)^4301 ≤ (3286114775703/25000000000000 : ℝ)^3277 := by
    have hnat : (85234637 : ℕ)^4301*25000000000000^3277 ≤ 3286114775703^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85234637 400000000 3286114775703 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524421777/1000000000 : ℝ)^4301 ≤ (2678960472821/6250000000000 : ℝ)^3277 := by
    have hnat : (524421777 : ℕ)^4301*6250000000000^3277 ≤ 2678960472821^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524421777 1000000000 2678960472821 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349116839/10000000000 : ℝ), (-85234637/400000000 : ℝ), (524421777/1000000000 : ℝ)] ![(2749510832701/6250000000000 : ℝ), (3286114775703/25000000000000 : ℝ), (2678960472821/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349116839/10000000000 : ℝ)|^4301 ≤ (2749510832701/6250000000000 : ℝ)^3277
        have hw : |(5349116839/10000000000 : ℝ)|=(5349116839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85234637/400000000 : ℝ)|^4301 ≤ (3286114775703/25000000000000 : ℝ)^3277
        have hw : |(-85234637/400000000 : ℝ)|=(85234637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524421777/1000000000 : ℝ)|^4301 ≤ (2678960472821/6250000000000 : ℝ)^3277
        have hw : |(524421777/1000000000 : ℝ)|=(524421777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069823323/2000000000 : ℝ)*x 0 + (2622108923/5000000000 : ℝ)*x 1 + (-1065433061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069823323/2000000000 : ℝ)^4301 ≤ (43992170905339/100000000000000 : ℝ)^3277 := by
    have hnat : (1069823323 : ℕ)^4301*100000000000000^3277 ≤ 43992170905339^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069823323 2000000000 43992170905339 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622108923/5000000000 : ℝ)^4301 ≤ (21431684190213/50000000000000 : ℝ)^3277 := by
    have hnat : (2622108923 : ℕ)^4301*50000000000000^3277 ≤ 21431684190213^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622108923 5000000000 21431684190213 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065433061/5000000000 : ℝ)^4301 ≤ (13144460697757/100000000000000 : ℝ)^3277 := by
    have hnat : (1065433061 : ℕ)^4301*100000000000000^3277 ≤ 13144460697757^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065433061 5000000000 13144460697757 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069823323/2000000000 : ℝ), (2622108923/5000000000 : ℝ), (-1065433061/5000000000 : ℝ)] ![(43992170905339/100000000000000 : ℝ), (21431684190213/50000000000000 : ℝ), (13144460697757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069823323/2000000000 : ℝ)|^4301 ≤ (43992170905339/100000000000000 : ℝ)^3277
        have hw : |(1069823323/2000000000 : ℝ)|=(1069823323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622108923/5000000000 : ℝ)|^4301 ≤ (21431684190213/50000000000000 : ℝ)^3277
        have hw : |(2622108923/5000000000 : ℝ)|=(2622108923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065433061/5000000000 : ℝ)|^4301 ≤ (13144460697757/100000000000000 : ℝ)^3277
        have hw : |(-1065433061/5000000000 : ℝ)|=(1065433061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540856657/1250000000 : ℝ)*x 0 + (2076688827/5000000000 : ℝ)*x 1 + (4507088463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540856657/1250000000 : ℝ)^4301 ≤ (33302965505427/100000000000000 : ℝ)^3277 := by
    have hnat : (540856657 : ℕ)^4301*100000000000000^3277 ≤ 33302965505427^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540856657 1250000000 33302965505427 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076688827/5000000000 : ℝ)^4301 ≤ (6312321931347/20000000000000 : ℝ)^3277 := by
    have hnat : (2076688827 : ℕ)^4301*20000000000000^3277 ≤ 6312321931347^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076688827 5000000000 6312321931347 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507088463/10000000000 : ℝ)^4301 ≤ (35135424825661/100000000000000 : ℝ)^3277 := by
    have hnat : (4507088463 : ℕ)^4301*100000000000000^3277 ≤ 35135424825661^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507088463 10000000000 35135424825661 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540856657/1250000000 : ℝ), (2076688827/5000000000 : ℝ), (4507088463/10000000000 : ℝ)] ![(33302965505427/100000000000000 : ℝ), (6312321931347/20000000000000 : ℝ), (35135424825661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540856657/1250000000 : ℝ)|^4301 ≤ (33302965505427/100000000000000 : ℝ)^3277
        have hw : |(540856657/1250000000 : ℝ)|=(540856657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076688827/5000000000 : ℝ)|^4301 ≤ (6312321931347/20000000000000 : ℝ)^3277
        have hw : |(2076688827/5000000000 : ℝ)|=(2076688827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507088463/10000000000 : ℝ)|^4301 ≤ (35135424825661/100000000000000 : ℝ)^3277
        have hw : |(4507088463/10000000000 : ℝ)|=(4507088463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044797379/10000000000 : ℝ)*x 0 + (5244825189/10000000000 : ℝ)*x 1 + (541254091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044797379/10000000000 : ℝ)^4301 ≤ (12452072474839/100000000000000 : ℝ)^3277 := by
    have hnat : (2044797379 : ℕ)^4301*100000000000000^3277 ≤ 12452072474839^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044797379 10000000000 12452072474839 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244825189/10000000000 : ℝ)^4301 ≤ (8573976754221/20000000000000 : ℝ)^3277 := by
    have hnat : (5244825189 : ℕ)^4301*20000000000000^3277 ≤ 8573976754221^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244825189 10000000000 8573976754221 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541254091/1000000000 : ℝ)^4301 ≤ (22339021875373/50000000000000 : ℝ)^3277 := by
    have hnat : (541254091 : ℕ)^4301*50000000000000^3277 ≤ 22339021875373^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541254091 1000000000 22339021875373 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044797379/10000000000 : ℝ), (5244825189/10000000000 : ℝ), (541254091/1000000000 : ℝ)] ![(12452072474839/100000000000000 : ℝ), (8573976754221/20000000000000 : ℝ), (22339021875373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044797379/10000000000 : ℝ)|^4301 ≤ (12452072474839/100000000000000 : ℝ)^3277
        have hw : |(-2044797379/10000000000 : ℝ)|=(2044797379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244825189/10000000000 : ℝ)|^4301 ≤ (8573976754221/20000000000000 : ℝ)^3277
        have hw : |(5244825189/10000000000 : ℝ)|=(5244825189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541254091/1000000000 : ℝ)|^4301 ≤ (22339021875373/50000000000000 : ℝ)^3277
        have hw : |(541254091/1000000000 : ℝ)|=(541254091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305608301/10000000000 : ℝ)*x 0 + (-981271369/5000000000 : ℝ)*x 1 + (1353135229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305608301/10000000000 : ℝ)^4301 ≤ (21761567932473/50000000000000 : ℝ)^3277 := by
    have hnat : (5305608301 : ℕ)^4301*50000000000000^3277 ≤ 21761567932473^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305608301 10000000000 21761567932473 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981271369/5000000000 : ℝ)^4301 ≤ (589941014869/5000000000000 : ℝ)^3277 := by
    have hnat : (981271369 : ℕ)^4301*5000000000000^3277 ≤ 589941014869^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981271369 5000000000 589941014869 5000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353135229/2500000000 : ℝ)^4301 ≤ (178712175263/400000000000 : ℝ)^3277 := by
    have hnat : (1353135229 : ℕ)^4301*400000000000^3277 ≤ 178712175263^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353135229 2500000000 178712175263 400000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305608301/10000000000 : ℝ), (-981271369/5000000000 : ℝ), (1353135229/2500000000 : ℝ)] ![(21761567932473/50000000000000 : ℝ), (589941014869/5000000000000 : ℝ), (178712175263/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305608301/10000000000 : ℝ)|^4301 ≤ (21761567932473/50000000000000 : ℝ)^3277
        have hw : |(5305608301/10000000000 : ℝ)|=(5305608301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-981271369/5000000000 : ℝ)|^4301 ≤ (589941014869/5000000000000 : ℝ)^3277
        have hw : |(-981271369/5000000000 : ℝ)|=(981271369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353135229/2500000000 : ℝ)|^4301 ≤ (178712175263/400000000000 : ℝ)^3277
        have hw : |(1353135229/2500000000 : ℝ)|=(1353135229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305608273/10000000000 : ℝ)*x 0 + (5412540943/10000000000 : ℝ)*x 1 + (-1962542741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305608273/10000000000 : ℝ)^4301 ≤ (43523135563481/100000000000000 : ℝ)^3277 := by
    have hnat : (5305608273 : ℕ)^4301*100000000000000^3277 ≤ 43523135563481^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305608273 10000000000 43523135563481 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412540943/10000000000 : ℝ)^4301 ≤ (22339022054133/50000000000000 : ℝ)^3277 := by
    have hnat : (5412540943 : ℕ)^4301*50000000000000^3277 ≤ 22339022054133^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412540943 10000000000 22339022054133 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962542741/10000000000 : ℝ)^4301 ≤ (2949705080263/25000000000000 : ℝ)^3277 := by
    have hnat : (1962542741 : ℕ)^4301*25000000000000^3277 ≤ 2949705080263^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962542741 10000000000 2949705080263 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305608273/10000000000 : ℝ), (5412540943/10000000000 : ℝ), (-1962542741/10000000000 : ℝ)] ![(43523135563481/100000000000000 : ℝ), (22339022054133/50000000000000 : ℝ), (2949705080263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305608273/10000000000 : ℝ)|^4301 ≤ (43523135563481/100000000000000 : ℝ)^3277
        have hw : |(5305608273/10000000000 : ℝ)|=(5305608273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412540943/10000000000 : ℝ)|^4301 ≤ (22339022054133/50000000000000 : ℝ)^3277
        have hw : |(5412540943/10000000000 : ℝ)|=(5412540943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1962542741/10000000000 : ℝ)|^4301 ≤ (2949705080263/25000000000000 : ℝ)^3277
        have hw : |(-1962542741/10000000000 : ℝ)|=(1962542741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s5_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216343967/500000000 : ℝ)*x 0 + (4505816553/10000000000 : ℝ)*x 1 + (4154655927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216343967/500000000 : ℝ)^4301 ≤ (6660645800809/20000000000000 : ℝ)^3277 := by
    have hnat : (216343967 : ℕ)^4301*20000000000000^3277 ≤ 6660645800809^3277*500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216343967 500000000 6660645800809 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505816553/10000000000 : ℝ)^4301 ≤ (17561205883921/50000000000000 : ℝ)^3277 := by
    have hnat : (4505816553 : ℕ)^4301*50000000000000^3277 ≤ 17561205883921^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505816553 10000000000 17561205883921 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154655927/10000000000 : ℝ)^4301 ≤ (15787179608713/50000000000000 : ℝ)^3277 := by
    have hnat : (4154655927 : ℕ)^4301*50000000000000^3277 ≤ 15787179608713^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154655927 10000000000 15787179608713 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216343967/500000000 : ℝ), (4505816553/10000000000 : ℝ), (4154655927/10000000000 : ℝ)] ![(6660645800809/20000000000000 : ℝ), (17561205883921/50000000000000 : ℝ), (15787179608713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216343967/500000000 : ℝ)|^4301 ≤ (6660645800809/20000000000000 : ℝ)^3277
        have hw : |(216343967/500000000 : ℝ)|=(216343967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505816553/10000000000 : ℝ)|^4301 ≤ (17561205883921/50000000000000 : ℝ)^3277
        have hw : |(4505816553/10000000000 : ℝ)|=(4505816553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154655927/10000000000 : ℝ)|^4301 ≤ (15787179608713/50000000000000 : ℝ)^3277
        have hw : |(4154655927/10000000000 : ℝ)|=(4154655927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11139/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2943/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1387/12500 : ℝ) ^ (1075/256 : ℝ) ≤ (2445597908236891/25000000000000000000 : ℝ) := by
    have hpowers : (1387/12500 : ℝ)^1075 ≤ (2445597908236891/25000000000000000000 : ℝ)^256 := by
      have hnat : (1387 : ℕ)^1075*25000000000000000000^256 ≤ 2445597908236891^256*12500^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1387 12500 2445597908236891 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1387/12500 : ℝ)) (X := (2445597908236891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (32429138034081431/100000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^1075 ≤ (32429138034081431/100000000000000000000 : ℝ)^256 := by
      have hnat : (14761 : ℕ)^1075*100000000000000000000^256 ≤ 32429138034081431^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 32429138034081431 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (32429138034081431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502445597908236891/12500000000000000000 : ℝ) ≤ (78128639688429/78125000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12502445597908236891/12500000000000000000 : ℝ)^256 ≤ (78128639688429/78125000000000 : ℝ)^1075 := by
      have hnat : (12502445597908236891 : ℕ)^256*78125000000000^1075 ≤ 78128639688429^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502445597908236891 12500000000000000000 78128639688429 78125000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78128639688429/78125000000000 : ℝ)) (X := (12502445597908236891/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008442305933405799/20000000000000000000 : ℝ) ≤ (10001005061807839/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (20008442305933405799/20000000000000000000 : ℝ)^256 ≤ (10001005061807839/10000000000000000 : ℝ)^1075 := by
      have hnat : (20008442305933405799 : ℕ)^256*10000000000000000^1075 ≤ 10001005061807839^1075*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008442305933405799 20000000000000000000 10001005061807839 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001005061807839/10000000000000000 : ℝ)) (X := (20008442305933405799/20000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032429138034081431/50000000000000000000 : ℝ) ≤ (5000772121748383/5000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50032429138034081431/50000000000000000000 : ℝ)^256 ≤ (5000772121748383/5000000000000000 : ℝ)^1075 := by
      have hnat : (50032429138034081431 : ℕ)^256*5000000000000000^1075 ≤ 5000772121748383^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032429138034081431 50000000000000000000 5000772121748383 5000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000772121748383/5000000000000000 : ℝ)) (X := (50032429138034081431/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2445597908236891/25000000000000000000 : ℝ) ≤ ((2289983870662196531/2290625000000000000 : ℝ)+2*(539181688927/366500000000000 : ℝ)*(1387/12500 : ℝ))^(1075/256 : ℝ) := by
    rw [show (2289983870662196531/2290625000000000000 : ℝ)+2*(539181688927/366500000000000 : ℝ)*(1387/12500 : ℝ)=(78128639688429/78125000000000 : ℝ) by norm_num, show 1+2*(2445597908236891/25000000000000000000 : ℝ)=(12502445597908236891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32429138034081431/100000000000000000000 : ℝ)+(2445597908236891/25000000000000000000 : ℝ) ≤ ((2289983870662196531/2290625000000000000 : ℝ)+(539181688927/366500000000000 : ℝ)*((14761/100000 : ℝ)+(1387/12500 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (2289983870662196531/2290625000000000000 : ℝ)+(539181688927/366500000000000 : ℝ)*((14761/100000 : ℝ)+(1387/12500 : ℝ))=(10001005061807839/10000000000000000 : ℝ) by norm_num, show 1+(32429138034081431/100000000000000000000 : ℝ)+(2445597908236891/25000000000000000000 : ℝ)=(20008442305933405799/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32429138034081431/100000000000000000000 : ℝ) ≤ ((2289983870662196531/2290625000000000000 : ℝ)+2*(539181688927/366500000000000 : ℝ)*(14761/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (2289983870662196531/2290625000000000000 : ℝ)+2*(539181688927/366500000000000 : ℝ)*(14761/100000 : ℝ)=(5000772121748383/5000000000000000 : ℝ) by norm_num, show 1+2*(32429138034081431/100000000000000000000 : ℝ)=(50032429138034081431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2289983870662196531/2290625000000000000 : ℝ)*(X 1 0+X 2 0)+(539181688927/366500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (2289983870662196531/2290625000000000000 : ℝ)) (alpha := (539181688927/366500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2289983870662196531/2290625000000000000 : ℝ)*(X 0 1+X 2 1)+(539181688927/366500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (2289983870662196531/2290625000000000000 : ℝ)) (alpha := (539181688927/366500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2289983870662196531/2290625000000000000 : ℝ)*(X 0 2+X 1 2)+(539181688927/366500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (2289983870662196531/2290625000000000000 : ℝ)) (alpha := (539181688927/366500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63899539/312500000 : ℝ)*X 0 0+(5413151449/10000000000 : ℝ)*X 0 1+(524421763/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349116839/10000000000 : ℝ)*X 1 0+(-85234637/400000000 : ℝ)*X 1 1+(524421777/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069823323/2000000000 : ℝ)*X 2 0+(2622108923/5000000000 : ℝ)*X 2 1+(-1065433061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540856657/1250000000 : ℝ)*X 0 0+(2076688827/5000000000 : ℝ)*X 0 1+(4507088463/10000000000 : ℝ)*X 0 2+(540856657/1250000000 : ℝ)*X 1 0+(2076688827/5000000000 : ℝ)*X 1 1+(4507088463/10000000000 : ℝ)*X 1 2+(540856657/1250000000 : ℝ)*X 2 0+(2076688827/5000000000 : ℝ)*X 2 1+(4507088463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2044797379/10000000000 : ℝ)*X 0 0+(5244825189/10000000000 : ℝ)*X 0 1+(541254091/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305608301/10000000000 : ℝ)*X 1 0+(-981271369/5000000000 : ℝ)*X 1 1+(1353135229/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305608273/10000000000 : ℝ)*X 2 0+(5412540943/10000000000 : ℝ)*X 2 1+(-1962542741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216343967/500000000 : ℝ)*X 0 0+(4505816553/10000000000 : ℝ)*X 0 1+(4154655927/10000000000 : ℝ)*X 0 2+(216343967/500000000 : ℝ)*X 1 0+(4505816553/10000000000 : ℝ)*X 1 1+(4154655927/10000000000 : ℝ)*X 1 2+(216343967/500000000 : ℝ)*X 2 0+(4505816553/10000000000 : ℝ)*X 2 1+(4154655927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36434363616740723592519/9162500000000000000000000000 : ℝ) := by norm_num
    linear_combination (70368241/10000000000000 : ℝ)*(base19) + (100586601/20000000000000 : ℝ)*(base23) + (6695533/6250000000000 : ℝ)*(upper2) + (250585903/100000000000000 : ℝ)*(upper3) + (81914729/100000000000000 : ℝ)*(upper4) + (2186672915129949/50000000000000 : ℝ)*(major0) + (2186672915129949/50000000000000 : ℝ)*(major1) + (2186672915129949/50000000000000 : ℝ)*(major2) + (591949954335719/10000000000000 : ℝ)*(sp0) + (5919508757688453/100000000000000 : ℝ)*(sp1) + (5919508958437857/100000000000000 : ℝ)*(sp2) + (2827173883670797/100000000000000 : ℝ)*(sp3) + (1239751709/12500000000000 : ℝ)*(sp4) + (12785827/156250000000 : ℝ)*(sp7) + (706795516650019/25000000000000 : ℝ)*(f.failure) + (5919509461370863/100000000000000 : ℝ)*(f.sum) + (44799271422677/9162500000000000000000000000 : ℝ)*base66 + (151610774442150669/114531250000000000000000000000000 : ℝ)*base67 + (284496299202306919/114531250000000000000000000000000 : ℝ)*base69 + (200264261010818081/114531250000000000000000000000000 : ℝ)*base72 + (25945408428221/18325000000000000000000000000 : ℝ)*base73 + (691519381496130581/114531250000000000000000000000000 : ℝ)*base76 + (276488700573943081/114531250000000000000000000000000 : ℝ)*base78 + (1430198284593400669/114531250000000000000000000000000 : ℝ)*base79 + (6271755087079/18325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (15602429/1250000000000000000000 : ℝ)*base90 + (15602429/1250000000000000000000 : ℝ)*base92 + (15602429/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224127753145210992554646651/28632812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1432676083/100000000000000 : ℝ)*(base19) + (294289869/20000000000000 : ℝ)*(base23) + (176168749/100000000000000 : ℝ)*(upper3) + (30497197/100000000000000 : ℝ)*(lower4) + (9832991/6250000000000 : ℝ)*(upper5) + (1101271072125993/25000000000000 : ℝ)*(major0) + (1101271072125993/25000000000000 : ℝ)*(major1) + (1101271072125993/25000000000000 : ℝ)*(major2) + (28792417127/100000000000000 : ℝ)*(sp1) + (30348405999/100000000000000 : ℝ)*(sp2) + (2981234343085707/50000000000000 : ℝ)*(sp4) + (1490609615269551/25000000000000 : ℝ)*(sp5) + (5962436866316071/100000000000000 : ℝ)*(sp6) + (1423849814957359/50000000000000 : ℝ)*(sp7) + (1423849814957359/50000000000000 : ℝ)*(f.failure) + (2981234343085707/50000000000000 : ℝ)*(f.sum) + (33306301173247/9162500000000000000000000000 : ℝ)*base65 + (160217314958036533/57265625000000000000000000000000 : ℝ)*base67 + (6882532375380283/57265625000000000000000000000000 : ℝ)*base69 + (107146380271911477/14316406250000000000000000000000 : ℝ)*base71 + (16447093648269/18325000000000000000000000000 : ℝ)*base73 + (92988426371650967/57265625000000000000000000000000 : ℝ)*base76 + (128126770348349033/57265625000000000000000000000000 : ℝ)*base77 + (61266443014161449/7158203125000000000000000000000 : ℝ)*base80 + (89781360115519/18325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16472369/2500000000000000000000 : ℝ)*base90 + (16472369/2500000000000000000000 : ℝ)*base92 + (16472369/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1341_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1341_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1341_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1341_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1341_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1969/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
